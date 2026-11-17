"""The manifest of verified certificates.

A certificate is verified when the manifest has an entry for it whose hash
matches its evidence, recorded by a trusted verifier who checked it with the
checkers here. CI only compares hashes, so it never runs the checks itself.
See certificates/README.md.
"""

import hashlib
import json
import pathlib
import re
from typing import Any, Mapping

import yaml

from .errors import CertificateError
from .lean import FORMAL_DIR
from .loading import CERTIFICATES_DIR


MANIFEST_PATH = CERTIFICATES_DIR / "verified.yml"

# GitHub accounts whose verifications count. Only a maintainer adds to this.
TRUSTED_VERIFIERS = ["daniel-munro"]

# Fields of a certificate covered by its evidence hash
HASHED_FIELDS = ["constant", "bound", "value", "kind", "witness", "lean"]
MANIFEST_FIELDS = ["sha256", "checker", "verified_by", "date"]
MANIFEST_HEADER = """\
# Certificates whose evidence a trusted verifier has checked, keyed by
# certificate ID. Written by scripts/verify_certificates.py; see
# certificates/README.md. Each entry records the hash of the evidence that was
# checked, the commit of the checkers used, who ran them, and when.
"""
LEAN_IMPORT = re.compile(r"^import\s+(\S+)", re.MULTILINE)


def evidence_files(cert: Mapping[str, Any]) -> list[pathlib.Path]:
    """The files holding a certificate's evidence, besides its YAML file:
    a witness file, or a Lean proof module and the proof modules it imports."""
    if cert["kind"] == "witness":
        file = cert["witness"].get("file")
        return [pathlib.Path(cert["path"]).parent / file] if file else []
    if "url" in cert["lean"]:
        return []
    files = []
    pending = [cert["lean"]["module"]]
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen or not module.startswith("LeapsInBounds.Proofs."):
            continue
        seen.add(module)
        path = FORMAL_DIR / (module.replace(".", "/") + ".lean")
        if not path.exists():
            raise CertificateError(f"{cert['id']}: Lean module {module} not found at {path}")
        files.append(path)
        pending += LEAN_IMPORT.findall(path.read_text())
    return sorted(files)


def evidence_hash(cert: Mapping[str, Any]) -> str:
    """SHA-256 of what a certificate claims and its evidence: the fields that
    say what is being proved and how, and the contents of its evidence files.
    Other fields, such as notes or an attestation, can change without
    invalidating a verification."""
    claim = {field: cert[field] for field in HASHED_FIELDS if field in cert}
    digest = hashlib.sha256(json.dumps(claim, sort_keys=True, default=str).encode())
    for path in evidence_files(cert):
        digest.update(b"\0" + path.as_posix().encode() + b"\0")
        digest.update(path.read_bytes())
    return digest.hexdigest()


def load_manifest(path: str | pathlib.Path = MANIFEST_PATH) -> dict[str, dict[str, Any]]:
    """Load the manifest of verified certificates, keyed by certificate ID."""
    path = pathlib.Path(path)
    if not path.exists():
        return {}
    with open(path) as file:
        manifest = yaml.safe_load(file) or {}
    for cert_id, entry in manifest.items():
        missing = [field for field in MANIFEST_FIELDS if field not in entry]
        if missing:
            raise CertificateError(f"{path}: entry {cert_id} is missing fields {missing}")
        entry["date"] = str(entry["date"])
    return manifest


def write_manifest(manifest: Mapping[str, Mapping[str, Any]], path: str | pathlib.Path = MANIFEST_PATH) -> None:
    with open(path, "w") as file:
        file.write(MANIFEST_HEADER)
        yaml.dump({k: dict(manifest[k]) for k in sorted(manifest)}, file, sort_keys=False)


def certificate_status(cert: Mapping[str, Any], manifest: Mapping[str, Mapping[str, Any]]) -> str:
    """How a certificate's evidence has been checked:

    - "verified": a trusted verifier checked it, as recorded in the manifest;
    - "attested": someone else says they checked it with a published checker;
    - "stale": the manifest has an entry, but the evidence has changed since;
    - "pending": neither, so it awaits verification.
    """
    entry = manifest.get(cert["id"])
    if entry is not None:
        if entry["sha256"] == evidence_hash(cert) and entry["verified_by"] in TRUSTED_VERIFIERS:
            return "verified"
        return "stale"
    if "attestation" in cert:
        return "attested"
    return "pending"
