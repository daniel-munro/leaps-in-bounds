"""Check certificates' evidence and record them as verified in the manifest.

Usage:
    python scripts/verify_certificates.py [ID ...] [--all] [--base REF] [--jobs N] [--dry-run]

Run by a trusted verifier (see TRUSTED_VERIFIERS in certificates.py), usually
on a pull request's branch before merging it. With no IDs, checks every
certificate awaiting verification: those with no manifest entry or a stale
one, and those whose entry differs from the base branch's manifest, so that
entries added by the pull request itself are checked again rather than
trusted. Attested certificates are only checked when named, since they're
usually attested because they take too long to check here.

--all checks every certificate except unverified attested ones, as an audit.
Each certificate that passes gets a manifest entry recording the hash of its
evidence, the commit of the checkers, who ran them, and the date. --dry-run
checks without writing the manifest.

The checkers must be committed, so that the recorded commit says exactly what
checked the evidence. If they differ from the base branch, as when a pull
request adds or changes a checker, review those changes before trusting the
result.
"""

import argparse
import datetime
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Any, Mapping

import yaml

from certificates import (
    MANIFEST_PATH,
    TRUSTED_VERIFIERS,
    CertificateError,
    certificate_status,
    check_lean,
    check_witness,
    evidence_hash,
    load_certificates,
    load_manifest,
    write_manifest,
)

# Files that define what certificates mean or how they're checked
CHECKER_PATHS = [
    "scripts",
    "formal/LeapsInBounds/Statements",
    "formal/lakefile.toml",
    "formal/lean-toolchain",
    "formal/lake-manifest.json",
]


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def base_manifest(base: str) -> dict[str, Any]:
    try:
        text = git("show", f"{base}:{MANIFEST_PATH.as_posix()}")
    except subprocess.CalledProcessError:
        return {}
    manifest = yaml.safe_load(text) or {}
    for entry in manifest.values():
        entry["date"] = str(entry["date"])
    return manifest


def run_witness(cert: Mapping[str, Any]) -> tuple[str, str | None, float]:
    start = time.monotonic()
    try:
        check_witness(cert)
        error = None
    except CertificateError as e:
        error = str(e)
    return cert["id"], error, time.monotonic() - start


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("ids", nargs="*", metavar="ID", help="certificate IDs to check")
    parser.add_argument("--all", action="store_true", help="check every certificate except attested ones")
    parser.add_argument("--base", default="origin/main", help="branch whose manifest entries are trusted (default origin/main)")
    parser.add_argument("--jobs", type=int, default=1, help="witnesses to check in parallel")
    parser.add_argument("--verifier", help="GitHub account to record (default: the only trusted verifier)")
    parser.add_argument("--dry-run", action="store_true", help="check without writing the manifest")
    parser.add_argument("-v", "--verbose", action="store_true", help="list every certificate, not just slow or failed ones")
    args = parser.parse_args()

    verifier = args.verifier or (TRUSTED_VERIFIERS[0] if len(TRUSTED_VERIFIERS) == 1 else None)
    if verifier not in TRUSTED_VERIFIERS and not args.dry_run:
        sys.exit(f"Give --verifier, one of the trusted verifiers: {', '.join(TRUSTED_VERIFIERS)}")

    dirty = git("status", "--porcelain", "--", *CHECKER_PATHS).strip()
    if dirty and not args.dry_run:
        sys.exit(f"Commit the checkers first, so the manifest can record what checked the evidence:\n{dirty}")
    commit = git("rev-parse", "HEAD").strip()
    changed = git("diff", "--name-only", args.base, "--", *CHECKER_PATHS).strip()
    if changed:
        print(f"Warning: these checker files differ from {args.base}, so review them before trusting the result:")
        print("\n".join(f"  {line}" for line in changed.splitlines()) + "\n")

    certificates = load_certificates()
    manifest = load_manifest()
    base = base_manifest(args.base)
    if args.ids:
        unknown = [i for i in args.ids if i not in certificates]
        if unknown:
            sys.exit(f"Unknown certificates: {', '.join(unknown)}")
        targets = args.ids
    else:
        targets = []
        for cert_id, cert in certificates.items():
            status = certificate_status(cert, manifest)
            if args.all:
                if status != "attested":
                    targets.append(cert_id)
            elif status in ("pending", "stale") or (cert_id in manifest and manifest[cert_id] != base.get(cert_id)):
                targets.append(cert_id)
    if not targets:
        print("Nothing to verify")
        return

    certs = [certificates[cert_id] for cert_id in targets]
    witnesses = [c for c in certs if c["kind"] == "witness"]
    leans = [c for c in certs if c["kind"] == "lean"]
    print(f"Checking {len(witnesses)} witnesses and {len(leans)} Lean proofs with the checkers at {commit[:7]}")
    hashes = {c["id"]: evidence_hash(c) for c in certs}

    failed: dict[str, str] = {}
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_witness, c) for c in witnesses]
        for future in as_completed(futures):
            cert_id, error, seconds = future.result()
            if error or seconds >= 1 or args.verbose:
                print(f"{'FAILED' if error else 'ok':7} {cert_id} ({seconds:.1f}s)", flush=True)
            if error:
                failed[cert_id] = error
    if leans:
        start = time.monotonic()
        lean_failed = check_lean(leans)
        failed |= lean_failed
        print(f"Lean: {len(leans) - len(lean_failed)} of {len(leans)} ok ({time.monotonic() - start:.1f}s)")

    # The evidence must not have changed while it was being checked
    for c in certs:
        if c["id"] not in failed and evidence_hash(c) != hashes[c["id"]]:
            failed[c["id"]] = "evidence changed while it was being checked"

    passed = [c["id"] for c in certs if c["id"] not in failed]
    print(f"\n{len(passed)} of {len(certs)} certificates passed")
    if not args.dry_run and passed:
        today = datetime.date.today().isoformat()
        for cert_id in passed:
            entry = manifest.get(cert_id)
            # Keep the base branch's record when re-checking the same evidence
            if entry is None or entry != base.get(cert_id) or entry["sha256"] != hashes[cert_id]:
                manifest[cert_id] = {"sha256": hashes[cert_id], "checker": commit, "verified_by": verifier, "date": today}
        write_manifest(manifest)
        print(f"Recorded them in {MANIFEST_PATH}")
    if failed:
        print("\nFailed:")
        for cert_id, error in sorted(failed.items()):
            print(f"- {cert_id}: {error}")
            if not args.dry_run and cert_id in manifest:
                print("  (its manifest entry is left as it was)")
        sys.exit(1)


if __name__ == "__main__":
    main()
