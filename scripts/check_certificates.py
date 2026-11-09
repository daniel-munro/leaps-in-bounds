"""Check certificates' structure and verification status, and check them
against each other and the literature.

Usage:
    python scripts/check_certificates.py [--allow-pending] [--new FILE ...] [--summary FILE] [-v]

This doesn't run the checkers on any evidence, which can take hours for large
witnesses. Instead, each certificate must be verified, with an entry in the
manifest (certificates/verified.yml) whose hash matches its evidence, or
attested, citing someone else's published checker. A maintainer verifies new
certificates with scripts/verify_certificates.py.

--allow-pending reports certificates awaiting verification without failing, as
for local builds. --new names the certificate files a pull request adds, which
must be at least as strong as every other certificate for the same bound.
--summary writes a Markdown report on them, which CI posts as a comment on the
pull request.
"""

import argparse
import pathlib
import sys
from typing import Any

import yaml

from certificates import (
    MANIFEST_PATH,
    TRUSTED_VERIFIERS,
    CertificateError,
    best_certificates,
    certificate_status,
    check_value_type,
    evidence_files,
    get_family,
    is_better,
    load_certificates,
    load_manifest,
)
from process_data import assign_updates_and_values, get_constants, load_updates


SUMMARY_MARKER = "<!-- certificate-check -->"


def check_structure(cert: dict[str, Any], constants: dict[str, Any], sources: dict[str, Any]) -> None:
    """Check everything about a certificate that's quick to check, short of
    its evidence."""
    if cert["constant"] not in constants:
        raise CertificateError(f"Unknown constant {cert['constant']}")
    if "source" in cert and cert["source"] not in sources:
        raise CertificateError(f"Unknown source {cert['source']}")
    family, _ = get_family(cert["constant"])
    check_value_type(family.values, cert["value"])
    if cert["kind"] == "witness":
        if family.witness_bound is None:
            raise CertificateError(f"{cert['constant']} only accepts Lean proofs")
        if cert["bound"] != family.witness_bound:
            raise CertificateError(f"Witnesses for {cert['constant']} can only certify {family.witness_bound} bounds")
        if not ("data" in cert["witness"]) ^ ("file" in cert["witness"]):
            raise CertificateError("witness needs one of 'data' or 'file'")
    else:
        if not cert["lean"]["module"].startswith("LeapsInBounds.Proofs."):
            raise CertificateError("Lean proofs must live under LeapsInBounds.Proofs")
    for path in evidence_files(cert):
        if not path.exists():
            raise CertificateError(f"evidence file {path} not found")


def literature_comparison(cert: dict[str, Any], constant: dict[str, Any]) -> str:
    """Describe how a certificate's bound compares with the best in the literature."""
    literature = constant[f"{cert['bound']}_bound"]
    if literature is None or literature.decimal_approx is None:
        return "no bound from the literature recorded on the site"
    # Literature values are rounded to 7 significant digits
    approx = float(f"{cert['approx']:.7g}")
    if is_better(cert["bound"], approx, literature.decimal_approx):
        return f"stronger than the best recorded, `{literature.latex}`"
    if approx == literature.decimal_approx:
        return "matches the best recorded"
    return f"weaker than the best recorded, `{literature.latex}`"


STATUS_TEXT = {
    "verified": "✅ verified",
    "attested": "🟡 attested",
    "pending": "⏳ awaiting verification",
    "stale": "⏳ changed since it was verified",
}


def format_summary(
    report: list[dict[str, Any]],
    errors: list[str],
    pending: list[str],
    constants: dict[str, dict[str, Any]],
) -> str:
    """Format the results for new certificates as a Markdown comment."""
    if errors:
        heading = "Certificate check failed ❌"
    elif pending:
        heading = "Certificates await verification ⏳"
    else:
        heading = "Certificate check passed ✅"
    lines = [SUMMARY_MARKER, f"## {heading}", ""]
    if report:
        lines += [
            "| Certificate | Bound | Evidence | Status | Previous certificate | Literature |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
        for row in report:
            cert = row["cert"]
            if cert is None:
                lines.append(f"| `{row['path']}` | | | ❌ {row['error']} | | |")
                continue
            relation = "≥" if cert["bound"] == "lower" else "≤"
            bound = f"`{cert['constant']}` {relation} `{cert['value']}`"
            kind = "Lean proof" if cert["kind"] == "lean" else "witness"
            status = f"❌ {row['error']}" if row["error"] else STATUS_TEXT[row["status"]]
            previous = row["previous"]
            previous = f"`{previous['value']}` ({previous['id']})" if previous else "none"
            constant = constants.get(cert["constant"])
            literature = literature_comparison(cert, constant) if constant else ""
            lines.append(f"| `{row['id']}` | {bound} | {kind} | {status} | {previous} | {literature} |")
        lines.append("")
    other_errors = [e for e in errors if not any(e.startswith(f"{row['id']} ") for row in report)]
    if other_errors:
        lines += ["Other errors:", ""] + [f"- {e}" for e in other_errors] + [""]
    if errors:
        lines.append(
            "See the [certificate rules](https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md) "
            "for the format, and push a fix to rerun the check."
        )
    else:
        if pending:
            lines.append(
                "The certificates are well formed. CI doesn't run the checkers, so a maintainer will check the "
                "evidence and add it to `certificates/verified.yml`."
            )
        lines.append(
            "A maintainer will also review the source and the description before merging. "
            "A certificate for a bound from the literature should cite it in `source`, and one for a "
            "new bound should say in `notes` how it was found."
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--allow-pending", action="store_true",
                        help="don't fail on certificates awaiting verification")
    parser.add_argument("--new", nargs="*", default=[], metavar="FILE",
                        help="certificate files added by a pull request")
    parser.add_argument("--summary", metavar="FILE", help="write a Markdown report on the new certificates")
    parser.add_argument("-v", "--verbose", action="store_true", help="list every certificate, not just problems")
    args = parser.parse_args()

    with open("source_data/constant_groups.yml") as file:
        groups = yaml.safe_load(file)
    with open("source_data/sources.yml") as file:
        sources = yaml.safe_load(file)
    constants = get_constants(groups)
    assign_updates_and_values(constants, load_updates("source_data/updates", sources))

    errors = []
    try:
        certificates = load_certificates()
        manifest = load_manifest()
    except CertificateError as e:
        sys.exit(f"Error: {e}")

    for cert_id, entry in manifest.items():
        if cert_id not in certificates:
            errors.append(f"{MANIFEST_PATH} has an entry for {cert_id}, which is not a certificate")
        if entry["verified_by"] not in TRUSTED_VERIFIERS:
            errors.append(f"{MANIFEST_PATH} entry for {cert_id} is by {entry['verified_by']}, who is not a trusted verifier")

    failed = {}
    status = {}
    for cert in certificates.values():
        try:
            check_structure(cert, constants, sources)
            status[cert["id"]] = certificate_status(cert, manifest)
        except CertificateError as e:
            failed[cert["id"]] = str(e)
    pending = sorted(cert_id for cert_id, s in status.items() if s in ("pending", "stale"))

    counts = {s: 0 for s in ["verified", "attested", "pending", "stale"]}
    for cert in certificates.values():
        if cert["id"] in failed:
            errors.append(f"{cert['id']}: {failed[cert['id']]}")
            print(f"{'FAILED':9} {cert['id']}")
            continue
        s = status[cert["id"]]
        counts[s] += 1
        if s in ("pending", "stale") or args.verbose:
            print(f"{s:9} {cert['id']}")
    summary = f"{len(certificates)} certificates: {counts['verified']} verified, {counts['attested']} attested"
    if counts["pending"] + counts["stale"]:
        summary += f", {counts['pending'] + counts['stale']} awaiting verification"
    if failed:
        summary += f", {len(failed)} malformed"
    print(summary)
    if pending and not args.allow_pending:
        errors += [
            f"{cert_id} is not verified: {'its evidence changed after' if status[cert_id] == 'stale' else 'it has no entry in'} "
            f"{MANIFEST_PATH} (run scripts/verify_certificates.py)"
            for cert_id in pending
        ]
    certificates = {k: v for k, v in certificates.items() if k not in failed}

    # Check certified bounds against each other and against the literature,
    # including those still awaiting verification
    best = best_certificates(certificates)
    for (constant_id, bound), cert in best.items():
        if bound != "lower":
            continue
        upper = best.get((constant_id, "upper"))
        if upper is not None and cert["approx"] > upper["approx"]:
            errors.append(f"{cert['id']} contradicts {upper['id']}")
    for (constant_id, bound), cert in best.items():
        opposite = constants[constant_id]["upper_bound" if bound == "lower" else "lower_bound"]
        if opposite is None or opposite.decimal_approx is None:
            continue
        # Literature values are rounded to 7 significant digits
        if is_better(bound, float(f"{cert['approx']:.7g}"), opposite.decimal_approx):
            errors.append(
                f"{cert['id']} contradicts the literature {'upper' if bound == 'lower' else 'lower'} "
                f"bound ${opposite.latex}$ for {constant_id}"
            )

    # New submissions must be at least as strong as existing certificates.
    # An equal one can replace a certificate that's slow to check, or upgrade
    # an attested bound to a verified one.
    report = []
    for path in args.new:
        cert_id = pathlib.Path(path).stem
        row = {"id": cert_id, "path": path, "cert": certificates.get(cert_id), "previous": None,
               "status": status.get(cert_id)}
        report.append(row)
        if cert_id in failed:
            row["error"] = failed[cert_id]
            continue
        if cert_id not in certificates:
            row["error"] = "not a certificate"
            errors.append(f"{path} is not a certificate")
            continue
        cert = certificates[cert_id]
        others = {k: v for k, v in certificates.items() if k != cert_id}
        previous = best_certificates(others).get((cert["constant"], cert["bound"]))
        row["previous"] = previous
        if previous is not None and is_better(cert["bound"], previous["approx"], cert["approx"]):
            row["error"] = f"weaker than {previous['id']} ({cert['bound']} bound {previous['value']})"
            errors.append(f"{cert_id} is {row['error']}")
        else:
            was = previous["value"] if previous else "none"
            print(f"new {cert['constant']} {cert['bound']} bound: {was} -> {cert['value']}")
        # Errors about this certificate found above, such as contradictions
        row.setdefault("error", "; ".join(e for e in errors if e.startswith(f"{cert_id} ")
                                          and "is not verified" not in e) or None)

    if args.summary and (report or errors):
        real_errors = [e for e in errors if "is not verified" not in e]
        with open(args.summary, "w") as file:
            file.write(format_summary(report, real_errors, pending, constants))

    if errors:
        print("\nErrors:")
        for error in errors:
            print(f"- {error}")
        sys.exit(1)


if __name__ == "__main__":
    main()
