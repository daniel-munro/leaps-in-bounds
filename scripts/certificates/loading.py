"""Load certificates and check their structure, short of their evidence."""

import pathlib
import re
from typing import Any, Iterable, Mapping

import yaml

from .errors import CertificateError
from .values import value_approx


CERTIFICATES_DIR = pathlib.Path("certificates")
REQUIRED_FIELDS = ["constant", "bound", "value", "kind", "submitted_by", "date"]
GITHUB_USERNAME = re.compile(r"[A-Za-z0-9](?:-?[A-Za-z0-9]){0,38}")

# Most bytes of evidence a certificate can keep in the repository: its YAML
# file and its evidence files, as stored (so compressed, if they are). Larger
# evidence can only be linked from an attested certificate. The site shows the
# state of each problem rather than archiving its data.
MAX_EVIDENCE_BYTES = 500_000
SHA256 = re.compile(r"[0-9a-f]{64}")
ATTESTATION_FIELDS = ["by", "checker", "command"]
PINNED_URL = re.compile(r"^https://\S*\b[0-9a-f]{40}\b")


def load_certificates(certificates_dir: str | pathlib.Path = CERTIFICATES_DIR) -> dict[str, dict[str, Any]]:
    """Load all certificates, keyed by ID (the file name without extension).

    Only checks the structure of each file, not its evidence.
    """
    certificates = {}
    for path in sorted(pathlib.Path(certificates_dir).glob("*/*.yml")):
        cert_id = path.stem
        if cert_id in certificates:
            raise CertificateError(f"Duplicate certificate ID: {cert_id}")
        with open(path) as file:
            cert = yaml.safe_load(file)
        missing = [field for field in REQUIRED_FIELDS if field not in cert]
        if missing:
            raise CertificateError(f"{path}: missing fields {missing}")
        if cert["bound"] not in ("lower", "upper"):
            raise CertificateError(f"{path}: bound must be 'lower' or 'upper'")
        if not isinstance(cert["submitted_by"], str) or not GITHUB_USERNAME.fullmatch(cert["submitted_by"]):
            raise CertificateError(f"{path}: submitted_by must be a GitHub username")
        if cert["kind"] not in ("witness", "lean"):
            raise CertificateError(f"{path}: kind must be 'witness' or 'lean'")
        if cert["kind"] not in cert:
            raise CertificateError(f"{path}: kind is '{cert['kind']}' but there is no '{cert['kind']}' section")
        if "attestation" in cert:
            check_attestation(cert["attestation"], path)
        if cert["kind"] == "witness":
            check_witness_source(cert, path)
        else:
            check_lean_source(cert, path)
        cert["approx"] = value_approx(cert["value"], path)
        cert["id"] = cert_id
        cert["path"] = str(path)
        cert["date"] = str(cert["date"])
        certificates[cert_id] = cert
    return certificates


def check_attestation(attestation: Any, path: Any) -> None:
    """Check the structure of a certificate's attestation: someone else's
    claim to have checked the evidence with a published checker."""
    if not isinstance(attestation, dict):
        raise CertificateError(f"{path}: attestation must be a mapping")
    missing = [field for field in ATTESTATION_FIELDS if not attestation.get(field)]
    if missing:
        raise CertificateError(f"{path}: attestation is missing fields {missing}")
    extra = set(attestation) - set(ATTESTATION_FIELDS) - {"evidence", "notes"}
    if extra:
        raise CertificateError(f"{path}: attestation has unknown fields {sorted(extra)}")
    for field in ["checker", "evidence"]:
        if field in attestation and not PINNED_URL.search(str(attestation[field])):
            raise CertificateError(
                f"{path}: attestation {field} must be a URL pinned to a commit (a full 40-character hash)"
            )


def check_witness_source(cert: Mapping[str, Any], path: Any) -> None:
    """Check that a witness gives exactly one of inline data, a file here, or
    (for an attested certificate only) a link to a file elsewhere."""
    witness = cert["witness"]
    if not isinstance(witness, dict):
        raise CertificateError(f"{path}: witness must be a mapping")
    sources = [key for key in ["data", "file", "url"] if key in witness]
    if len(sources) != 1:
        raise CertificateError(f"{path}: witness needs exactly one of 'data', 'file' or 'url'")
    if "url" in witness:
        if "attestation" not in cert:
            raise CertificateError(
                f"{path}: a witness given by url can't be checked here, so the certificate needs an attestation"
            )
        if not str(witness["url"]).startswith("https://"):
            raise CertificateError(f"{path}: witness url must be an https URL")
        if not SHA256.fullmatch(str(witness.get("sha256", ""))):
            raise CertificateError(f"{path}: a witness given by url needs the file's sha256 (64 lowercase hex digits)")
    elif "sha256" in witness:
        raise CertificateError(f"{path}: witness sha256 is only for a witness given by url")


def check_lean_source(cert: Mapping[str, Any], path: Any) -> None:
    """Check that a Lean proof names its theorem and gives exactly one of a
    module here (under formal/) or, for an attested certificate only, a link
    to the proof elsewhere, pinned to a commit: one too large to keep here,
    checked by someone else."""
    lean = cert["lean"]
    if not isinstance(lean, dict):
        raise CertificateError(f"{path}: lean must be a mapping")
    if not lean.get("theorem"):
        raise CertificateError(f"{path}: lean needs a theorem")
    sources = [key for key in ["module", "url"] if key in lean]
    if len(sources) != 1:
        raise CertificateError(f"{path}: lean needs exactly one of 'module' or 'url'")
    if "url" in lean:
        if "attestation" not in cert:
            raise CertificateError(
                f"{path}: a Lean proof given by url can't be checked here, so the certificate needs an attestation"
            )
        if not PINNED_URL.search(str(lean["url"])):
            raise CertificateError(f"{path}: lean url must be a URL pinned to a commit (a full 40-character hash)")


def is_external(cert: Mapping[str, Any]) -> bool:
    """Whether a certificate's evidence is only linked, not kept here: a
    witness or Lean proof given by url. These can only be attested."""
    return "url" in cert[cert["kind"]]


def is_better(bound: str, a: float, b: float) -> bool:
    """Whether bound value a is strictly stronger than b."""
    return a > b if bound == "lower" else a < b


def best_certificates(
    certificates: Mapping[str, Mapping[str, Any]],
    preferred: Iterable[str] = (),
) -> dict[tuple[str, str], Mapping[str, Any]]:
    """Find the strongest certificate for each (constant, bound) pair.
    Ties go to certificates whose IDs are in preferred (such as verified
    ones), then to the earliest date."""
    preferred = set(preferred)
    best = {}
    for cert in sorted(certificates.values(), key=lambda c: (c["id"] not in preferred, c["date"])):
        key = (cert["constant"], cert["bound"])
        if key not in best or is_better(cert["bound"], cert["approx"], best[key]["approx"]):
            best[key] = cert
    return best
