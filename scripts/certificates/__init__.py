"""Load and verify bound certificates.

A certificate claims a lower or upper bound on one constant and carries
evidence that can be checked mechanically, so the bound doesn't rely on trust
in a secondary source:

- witness: an explicit construction, checked by a verifier for the constant's
  family (see families/, one module per family).
- lean: a Lean theorem in formal/ whose type is the family's formal statement
  of the bound (see lean.py).

A certificate is verified once a trusted verifier has run the checks here,
as recorded in the manifest (certificates/verified.yml), or attested when its
evidence was checked elsewhere with a published checker (see
manifest.certificate_status). See certificates/README.md for the file format.

The modules:

- loading: reading certificates and checking their structure
- manifest: evidence hashes and the manifest of verified certificates
- lean: checking Lean proofs against the formal statements
- family: the Family record of how to check a family's certificates
- families: one module per family, and the FAMILIES registry
- values, witness, graphs, geometry: shared parsing and checking helpers
"""

from .errors import CertificateError
from .families import FAMILIES, check_witness, get_family
from .lean import check_lean
from .loading import (
    GITHUB_USERNAME,
    MAX_EVIDENCE_BYTES,
    best_certificates,
    is_better,
    is_external,
    load_certificates,
)
from .manifest import (
    MANIFEST_PATH,
    TRUSTED_VERIFIERS,
    certificate_status,
    evidence_files,
    evidence_hash,
    load_manifest,
    write_manifest,
)
from .values import check_value_type

__all__ = [
    "FAMILIES",
    "GITHUB_USERNAME",
    "MANIFEST_PATH",
    "MAX_EVIDENCE_BYTES",
    "TRUSTED_VERIFIERS",
    "CertificateError",
    "best_certificates",
    "certificate_status",
    "check_lean",
    "check_value_type",
    "check_witness",
    "evidence_files",
    "evidence_hash",
    "get_family",
    "is_better",
    "is_external",
    "load_certificates",
    "load_manifest",
    "write_manifest",
]
