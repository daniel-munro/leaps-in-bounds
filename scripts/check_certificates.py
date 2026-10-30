"""Verify certificates and check them against each other and the literature.

Usage:
    python scripts/check_certificates.py [--lean [--no-build]] [--improves FILE ...]

--lean checks Lean proofs (needs Mathlib fetched in formal/); without it they
are skipped. It builds the proof modules first, unless --no-build is given
because they were compiled elsewhere, as in CI. --improves requires the given certificate files to be strictly
stronger than every other certificate for the same bound, as for new
submissions.
"""

import argparse
import pathlib
import sys

import yaml

from certificates import (
    CertificateError,
    best_certificates,
    check_lean,
    check_witness,
    get_family,
    is_better,
    load_certificates,
)
from process_data import assign_updates_and_values, get_constants, load_updates


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="also check Lean proofs")
    parser.add_argument("--no-build", action="store_true", help="check Lean proofs without building them")
    parser.add_argument("--improves", nargs="*", default=[], metavar="FILE",
                        help="certificate files that must improve on all others")
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
            get_family(cert["constant"])
            if cert["kind"] == "witness":
                check_witness(cert)
            elif args.lean:
                lean_certs.append(cert)
        except CertificateError as e:
            failed[cert["id"]] = str(e)
    if lean_certs:
        failed |= check_lean(lean_certs, build=not args.no_build)
    for cert in certificates.values():
        if cert["id"] in failed:
            errors.append(f"{cert['id']}: {failed[cert['id']]}")
            print(f"FAILED   {cert['id']}")
        elif cert["kind"] == "lean" and not args.lean:
            print(f"skipped  {cert['id']} (Lean; run with --lean)")
        else:
            print(f"ok       {cert['id']}")
    certificates = {k: v for k, v in certificates.items() if k not in failed}

    # Check verified bounds against each other and against the literature
    best = best_certificates(certificates)
    for (constant_id, bound), cert in best.items():
        if bound != "lower":
            continue
        upper = best.get((constant_id, "upper"))
        if upper is not None and cert["value"] > upper["value"]:
            errors.append(f"{cert['id']} contradicts {upper['id']}")
    for (constant_id, bound), cert in best.items():
        opposite = constants[constant_id]["upper_bound" if bound == "lower" else "lower_bound"]
        if opposite is None or opposite.decimal_approx is None:
            continue
        if is_better(bound, cert["value"], opposite.decimal_approx):
            errors.append(
                f"{cert['id']} contradicts the literature {'upper' if bound == 'lower' else 'lower'} "
                f"bound ${opposite.latex}$ for {constant_id}"
            )

    # Check that new submissions improve on existing certificates
    for path in args.improves:
        cert_id = pathlib.Path(path).stem
        if cert_id in failed:
            continue
        if cert_id not in certificates:
            errors.append(f"{path} is not a certificate")
            continue
        cert = certificates[cert_id]
        others = {k: v for k, v in certificates.items() if k != cert_id}
        previous = best_certificates(others).get((cert["constant"], cert["bound"]))
        if previous is not None and not is_better(cert["bound"], cert["value"], previous["value"]):
            errors.append(f"{cert_id} does not improve on {previous['id']} ({cert['bound']} bound {previous['value']})")
        else:
            was = previous["value"] if previous else "none"
            print(f"improves {cert['constant']} {cert['bound']} bound: {was} -> {cert['value']}")

    if errors:
        print("\nErrors:")
        for error in errors:
            print(f"- {error}")
        sys.exit(1)


if __name__ == "__main__":
    main()
