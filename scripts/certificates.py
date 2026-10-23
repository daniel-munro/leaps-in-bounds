"""Load and verify bound certificates.

A certificate claims a lower or upper bound on one constant and carries
evidence that can be checked mechanically, so the bound doesn't rely on trust
in a secondary source:

- witness: an explicit construction, checked by a verifier for the constant's
  family (see FAMILIES).
- lean: a Lean theorem in formal/ whose type is the family's formal statement
  of the bound.

See certificates/README.md for the file format.
"""

import pathlib
import re
import subprocess
import tempfile
from dataclasses import dataclass
from typing import Any, Callable, Mapping

import yaml

CERTIFICATES_DIR = pathlib.Path("certificates")
FORMAL_DIR = pathlib.Path("formal")

# Axioms a Lean proof may depend on. Notably excludes sorryAx and
# Lean.ofReduceBool (used by native_decide, which trusts the compiler).
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

REQUIRED_FIELDS = ["constant", "bound", "value", "kind", "submitted_by", "date"]


class CertificateError(Exception):
    pass


def load_certificates(certificates_dir: str | pathlib.Path = CERTIFICATES_DIR) -> dict[str, dict[str, Any]]:
    """Load all certificates, keyed by ID (the file name without extension).

    Only checks the structure of each file, not its evidence.
    """
    certificates = {}
    for path in sorted(pathlib.Path(certificates_dir).glob("**/*.yml")):
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
        if cert["kind"] not in ("witness", "lean"):
            raise CertificateError(f"{path}: kind must be 'witness' or 'lean'")
        if cert["kind"] not in cert:
            raise CertificateError(f"{path}: kind is '{cert['kind']}' but there is no '{cert['kind']}' section")
        cert["id"] = cert_id
        cert["path"] = str(path)
        cert["date"] = str(cert["date"])
        certificates[cert_id] = cert
    return certificates


#########
# Graphs #
#########

def decode_graph6(data: str) -> list[int]:
    """Decode a graph6 string into a list of adjacency bitsets."""
    data = data.strip()
    if data.startswith(">>graph6<<"):
        data = data[len(">>graph6<<"):]
    values = [ord(c) - 63 for c in data]
    if any(v < 0 or v > 63 for v in values):
        raise CertificateError("Invalid graph6 character")
    if values[0] < 63:
        n, values = values[0], values[1:]
    elif values[1] < 63:
        n = (values[1] << 12) | (values[2] << 6) | values[3]
        values = values[4:]
    else:
        n = 0
        for v in values[2:8]:
            n = (n << 6) | v
        values = values[8:]
    num_bits = n * (n - 1) // 2
    if len(values) != (num_bits + 5) // 6:
        raise CertificateError(f"graph6 data has wrong length for {n} vertices")
    bits = [(v >> (5 - k)) & 1 for v in values for k in range(6)]
    adj = [0] * n
    index = 0
    for j in range(1, n):
        for i in range(j):
            if bits[index]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            index += 1
    return adj


def encode_graph6(adj: list[int]) -> str:
    """Encode a list of adjacency bitsets as a graph6 string."""
    n = len(adj)
    if n < 63:
        values = [n]
    elif n < 258048:
        values = [63, (n >> 12) & 63, (n >> 6) & 63, n & 63]
    else:
        values = [63, 63] + [(n >> (6 * k)) & 63 for k in range(5, -1, -1)]
    bits = [(adj[i] >> j) & 1 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    for k in range(0, len(bits), 6):
        values.append(int("".join(map(str, bits[k:k + 6])), 2))
    return "".join(chr(v + 63) for v in values)


def complement(adj: list[int]) -> list[int]:
    n = len(adj)
    full = (1 << n) - 1
    return [full & ~adj[v] & ~(1 << v) for v in range(n)]


def has_clique(adj: list[int], k: int) -> bool:
    """Check whether a graph has a clique with k vertices."""
    def extend(candidates: int, needed: int) -> bool:
        if needed == 0:
            return True
        while candidates:
            if candidates.bit_count() < needed:
                return False
            v = candidates.bit_length() - 1
            candidates &= ~(1 << v)
            if extend(candidates & adj[v], needed - 1):
                return True
        return False
    return extend((1 << len(adj)) - 1, k)


def read_witness_data(cert: Mapping[str, Any]) -> str:
    witness = cert["witness"]
    if "data" in witness:
        return witness["data"]
    if "file" in witness:
        return (pathlib.Path(cert["path"]).parent / witness["file"]).read_text()
    raise CertificateError(f"{cert['id']}: witness needs 'data' or 'file'")


###########
# Families #
###########

@dataclass
class Family:
    """How to check certificates for one group of constants."""
    # Matches constant IDs, capturing the parameters as named groups.
    id_pattern: re.Pattern[str]
    # Lean module containing the formal statements.
    lean_module: str
    # (params, bound, value) -> Lean proposition stating the bound.
    lean_statement: Callable[[Mapping[str, int], str, int], str]
    # (params, bound, value, cert) -> None, raising CertificateError if invalid.
    check_witness: Callable[[Mapping[str, int], str, int, Mapping[str, Any]], None]


def ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> str:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Ramsey.{name} {params['r']} {params['s']} {value}"


def ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R(r,s) >= value is witnessed by a graph on value - 1 vertices with no
    r-clique and no independent set of size s."""
    if bound != "lower":
        raise CertificateError("Ramsey witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "graph6":
        raise CertificateError("Ramsey witnesses must use format: graph6")
    adj = decode_graph6(read_witness_data(cert))
    if len(adj) != value - 1:
        raise CertificateError(f"Graph has {len(adj)} vertices, but R(r,s) >= {value} needs {value - 1}")
    if has_clique(adj, params["r"]):
        raise CertificateError(f"Graph contains a clique of size {params['r']}")
    if has_clique(complement(adj), params["s"]):
        raise CertificateError(f"Graph contains an independent set of size {params['s']}")


# Keyed by constant group ID.
FAMILIES = {
    "ramsey": Family(
        id_pattern=re.compile(r"ramsey-(?P<r>\d+)-(?P<s>\d+)"),
        lean_module="LeapsInBounds.Statements.Ramsey",
        lean_statement=ramsey_lean_statement,
        check_witness=ramsey_check_witness,
    ),
}


def get_family(constant_id: str) -> tuple[Family, dict[str, int]]:
    for family in FAMILIES.values():
        match = family.id_pattern.fullmatch(constant_id)
        if match:
            return family, {k: int(v) for k, v in match.groupdict().items()}
    raise CertificateError(f"No certificate family supports constant {constant_id}")


################
# Verification #
################

def check_lean(cert: Mapping[str, Any], family: Family, params: Mapping[str, int]) -> None:
    """Check that the named theorem proves the expected statement using only
    allowed axioms. Requires the formal/ project to be built."""
    module = cert["lean"]["module"]
    theorem = cert["lean"]["theorem"]
    if not module.startswith("LeapsInBounds.Proofs."):
        raise CertificateError("Lean proofs must live under LeapsInBounds.Proofs")
    statement = family.lean_statement(params, cert["bound"], cert["value"])
    source = (
        f"import {family.lean_module}\n"
        f"import {module}\n\n"
        f"example : {statement} := {theorem}\n\n"
        f"#print axioms {theorem}\n"
    )
    build = subprocess.run(["lake", "build", module], cwd=FORMAL_DIR, capture_output=True, text=True)
    if build.returncode != 0:
        raise CertificateError(f"lake build {module} failed:\n{build.stdout}{build.stderr}")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=FORMAL_DIR, delete=False) as file:
        file.write(source)
        check_path = pathlib.Path(file.name)
    try:
        result = subprocess.run(["lake", "env", "lean", check_path.name], cwd=FORMAL_DIR, capture_output=True, text=True)
    finally:
        check_path.unlink()
    output = result.stdout + result.stderr
    if result.returncode != 0 or re.search(r":\d+:\d+: error", output):
        raise CertificateError(f"Theorem {theorem} does not prove `{statement}`:\n{output}")
    if "does not depend on any axioms" in output:
        return
    match = re.search(r"depends on axioms: \[(.*?)\]", output, re.DOTALL)
    if not match:
        raise CertificateError(f"Could not read axioms from Lean output:\n{output}")
    axioms = {a.strip() for a in match.group(1).split(",")}
    disallowed = axioms - ALLOWED_AXIOMS
    if disallowed:
        raise CertificateError(f"Proof uses disallowed axioms: {sorted(disallowed)}")


def check_certificate(cert: Mapping[str, Any], lean: bool) -> bool:
    """Verify a certificate's evidence. Returns False if it was skipped
    because it's a Lean proof and lean is False."""
    family, params = get_family(cert["constant"])
    if cert["kind"] == "witness":
        family.check_witness(params, cert["bound"], cert["value"], cert)
        return True
    if not lean:
        return False
    check_lean(cert, family, params)
    return True


def is_better(bound: str, a: float, b: float) -> bool:
    """Whether bound value a is strictly stronger than b."""
    return a > b if bound == "lower" else a < b


def best_certificates(certificates: Mapping[str, Mapping[str, Any]]) -> dict[tuple[str, str], Mapping[str, Any]]:
    """Find the strongest certificate for each (constant, bound) pair.
    Ties go to the earliest date."""
    best = {}
    for cert in sorted(certificates.values(), key=lambda c: c["date"]):
        key = (cert["constant"], cert["bound"])
        if key not in best or is_better(cert["bound"], cert["value"], best[key]["value"]):
            best[key] = cert
    return best
