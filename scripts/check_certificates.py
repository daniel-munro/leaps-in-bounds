"""Verify certificates and check them against each other and the literature.

Usage:
    python scripts/check_certificates.py [--lean [--no-build]] [--improves FILE ...] [--summary FILE] [-v]

--lean checks Lean proofs (needs Mathlib fetched in formal/); without it they
are skipped. It builds the proof modules first, unless --no-build is given
because they were compiled elsewhere, as in CI. --improves requires the given certificate files to be strictly
stronger than every other certificate for the same bound, as for new
submissions. --summary writes a Markdown report on those certificates, which
CI posts as a comment on the pull request.
"""

import argparse
import pathlib
import sys
from typing import Any

import yaml

from certificates import (
    CertificateError,
    best_certificates,
    check_lean,
    check_value_type,
    check_witness,
    get_family,
    is_better,
    load_certificates,
)
from process_data import assign_updates_and_values, get_constants, load_updates


SUMMARY_MARKER = "<!-- certificate-check -->"


def literature_comparison(cert: dict[str, Any], constant: dict[str, Any]) -> str:
    """Describe how a certificate's bound compares with the best in the literature."""
    literature = constant[f"{cert['bound']}_bound"]
    if literature is None or literature.decimal_approx is None:
        return "no bound in the literature yet: **new**"
    # Literature values are rounded to 7 significant digits
    approx = float(f"{cert['approx']:.7g}")
    if is_better(cert["bound"], approx, literature.decimal_approx):
        return f"beats the best known `{literature.latex}`: **new record**"
    if approx == literature.decimal_approx:
        return "matches the best known"
    return f"weaker than the best known `{literature.latex}`"


def format_summary(
    report: list[dict[str, Any]],
    errors: list[str],
    constants: dict[str, dict[str, Any]],
) -> str:
    """Format the results for new certificates as a Markdown comment."""
    passed = not errors
    lines = [
        SUMMARY_MARKER,
        f"## Certificate check {'passed ✅' if passed else 'failed ❌'}",
        "",
    ]
    if report:
        lines += [
            "| Certificate | Bound | Check | Previous certificate | Literature |",
            "| --- | --- | --- | --- | --- |",
        ]
        for row in report:
            cert = row["cert"]
            if cert is None:
                lines.append(f"| `{row['path']}` | | ❌ {row['error']} | | |")
                continue
            relation = "≥" if cert["bound"] == "lower" else "≤"
            bound = f"`{cert['constant']}` {relation} `{cert['value']}`"
            kind = "Lean proof" if cert["kind"] == "lean" else "witness"
            if row["error"]:
                check = f"❌ {row['error']}"
            elif row.get("skipped"):
                check = f"⚠️ {kind} not checked"
            else:
                check = f"✅ {kind} checked"
            previous = row["previous"]
            previous = f"`{previous['value']}` ({previous['id']})" if previous else "none"
            constant = constants.get(cert["constant"])
            literature = literature_comparison(cert, constant) if constant else ""
            lines.append(f"| `{row['id']}` | {bound} | {check} | {previous} | {literature} |")
        lines.append("")
    other_errors = [e for e in errors if not any(e.startswith(f"{row['id']} ") for row in report)]
    if other_errors:
        lines += ["Other errors:", ""] + [f"- {e}" for e in other_errors] + [""]
    if passed:
        lines.append(
            "A maintainer will still review the source and the description before merging. "
            "If a certificate improves on the literature, its source should say where the construction "
            "or proof comes from, or its notes how it was found."
        )
    else:
        lines.append(
            "See the [certificate rules](https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md) "
            "for the format, and push a fix to rerun the check."
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="also check Lean proofs")
    parser.add_argument("--no-build", action="store_true", help="check Lean proofs without building them")
    parser.add_argument("--improves", nargs="*", default=[], metavar="FILE",
                        help="certificate files that must improve on all others")
    parser.add_argument("--summary", metavar="FILE", help="write a Markdown report on the new certificates")
    parser.add_argument("-v", "--verbose", action="store_true", help="list every certificate, not just failures")
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
    except CertificateError as e:
        sys.exit(f"Error: {e}")

    # Check each certificate's evidence, with Lean proofs checked together
    failed = {}
    lean_certs = []
    for cert in certificates.values():
        try:
            if cert["constant"] not in constants:
                raise CertificateError(f"Unknown constant {cert['constant']}")
            if "source" in cert and cert["source"] not in sources:
                raise CertificateError(f"Unknown source {cert['source']}")
            family, _ = get_family(cert["constant"])
            check_value_type(family.values, cert["value"])
            if cert["kind"] == "witness":
                check_witness(cert)
            elif args.lean:
                lean_certs.append(cert)
        except CertificateError as e:
            failed[cert["id"]] = str(e)
    if lean_certs:
        failed |= check_lean(lean_certs, build=not args.no_build)
    counts = {"ok": 0, "skipped": 0, "FAILED": 0}
    for cert in certificates.values():
        if cert["id"] in failed:
            errors.append(f"{cert['id']}: {failed[cert['id']]}")
            status = "FAILED"
        elif cert["kind"] == "lean" and not args.lean:
            status = "skipped"
        else:
            status = "ok"
        counts[status] += 1
        if status == "FAILED" or args.verbose:
            print(f"{status:8} {cert['id']}")
    summary = f"Checked {len(certificates)} certificates: {counts['ok']} ok"
    if counts["skipped"]:
        summary += f", {counts['skipped']} Lean proofs skipped (run with --lean)"
    if counts["FAILED"]:
        summary += f", {counts['FAILED']} failed"
    print(summary)
    certificates = {k: v for k, v in certificates.items() if k not in failed}

    # Check verified bounds against each other and against the literature
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

    # Check that new submissions improve on existing certificates
    report = []
    for path in args.improves:
        cert_id = pathlib.Path(path).stem
        row = {"id": cert_id, "path": path, "cert": certificates.get(cert_id), "previous": None}
        report.append(row)
        if cert_id in failed:
            row["error"] = failed[cert_id]
            continue
        if cert_id not in certificates:
            row["error"] = "not a certificate"
            errors.append(f"{path} is not a certificate")
            continue
        cert = certificates[cert_id]
        row["skipped"] = cert["kind"] == "lean" and not args.lean
        others = {k: v for k, v in certificates.items() if k != cert_id}
        previous = best_certificates(others).get((cert["constant"], cert["bound"]))
        row["previous"] = previous
        if previous is not None and not is_better(cert["bound"], cert["approx"], previous["approx"]):
            row["error"] = f"does not improve on {previous['id']} ({cert['bound']} bound {previous['value']})"
            errors.append(f"{cert_id} {row['error']}")
        else:
            was = previous["value"] if previous else "none"
            print(f"improves {cert['constant']} {cert['bound']} bound: {was} -> {cert['value']}")
        # Errors about this certificate found above, such as contradictions
        row.setdefault("error", "; ".join(e for e in errors if e.startswith(f"{cert_id} ")) or None)

    if args.summary and (report or errors):
        with open(args.summary, "w") as file:
            file.write(format_summary(report, errors, constants))

    if errors:
        print("\nErrors:")
        for error in errors:
            print(f"- {error}")
        sys.exit(1)


if __name__ == "__main__":
    main()
