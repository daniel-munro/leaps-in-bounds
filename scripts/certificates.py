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

import json
import math
import pathlib
import re
import subprocess
import tempfile
from dataclasses import dataclass
from typing import Any, Callable, Mapping

import numpy as np
import sympy
import yaml

CERTIFICATES_DIR = pathlib.Path("certificates")
FORMAL_DIR = pathlib.Path("formal")
CHECK_LEAN_SCRIPT = pathlib.Path("scripts/check_lean.lean")

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
        cert["approx"] = value_approx(cert["value"], path)
        cert["id"] = cert_id
        cert["path"] = str(path)
        cert["date"] = str(cert["date"])
        certificates[cert_id] = cert
    return certificates


SQRT_PATTERN = re.compile(r"\\sqrt\{(\d+)\}")


def value_approx(value: Any, path: Any = None) -> float:
    """Numeric value of a certificate's bound, which is an integer or a string
    `\\sqrt{m}` for a natural number m."""
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if isinstance(value, str) and SQRT_PATTERN.fullmatch(value):
        return math.sqrt(int(SQRT_PATTERN.fullmatch(value).group(1)))
    raise CertificateError(f"{path}: value must be an integer or '\\sqrt{{m}}', not {value!r}")


def sqrt_argument(value: int | str) -> int:
    """The m with value = √m, for an integer value or one written `\\sqrt{m}`.
    Square roots of perfect squares must be written as integers."""
    if isinstance(value, int):
        return value * value
    m = int(SQRT_PATTERN.fullmatch(value).group(1))
    if math.isqrt(m) ** 2 == m:
        raise CertificateError(f"Write \\sqrt{{{m}}} as {math.isqrt(m)}")
    return m


#########
# Graphs #
#########

def decode_values(data: str, header: str) -> list[int]:
    """Convert graph6/sparse6 characters to 6-bit values, dropping the
    optional header."""
    data = data.strip()
    if data.startswith(header):
        data = data[len(header):]
    values = [ord(c) - 63 for c in data]
    if not values or any(v < 0 or v > 63 for v in values):
        raise CertificateError(f"Invalid {header.strip('<>')} data")
    return values


def decode_size(values: list[int]) -> tuple[int, list[int]]:
    """Read the number of vertices from the start of graph6/sparse6 values,
    returning it and the remaining values."""
    if values[0] < 63:
        return values[0], values[1:]
    if values[1] < 63:
        return (values[1] << 12) | (values[2] << 6) | values[3], values[4:]
    n = 0
    for v in values[2:8]:
        n = (n << 6) | v
    return n, values[8:]


def encode_size(n: int) -> list[int]:
    if n < 63:
        return [n]
    if n < 258048:
        return [63, (n >> 12) & 63, (n >> 6) & 63, n & 63]
    return [63, 63] + [(n >> (6 * k)) & 63 for k in range(5, -1, -1)]


def decode_graph6(data: str) -> list[int]:
    """Decode a graph6 string into a list of adjacency bitsets."""
    n, values = decode_size(decode_values(data, ">>graph6<<"))
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
    values = encode_size(n)
    bits = [(adj[i] >> j) & 1 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    for k in range(0, len(bits), 6):
        values.append(int("".join(map(str, bits[k:k + 6])), 2))
    return "".join(chr(v + 63) for v in values)


def decode_sparse6(data: str) -> list[int]:
    """Decode a sparse6 string into a list of adjacency bitsets.

    The data is a sequence of (b, x) pairs, with b one bit and x enough bits
    for n - 1. Keeping a current vertex v: b = 1 increments v, then x > v
    moves v to x, and otherwise gives the edge {x, v}. Padding is ignored.
    """
    data = data.strip()
    if data.startswith(">>sparse6<<"):
        data = data[len(">>sparse6<<"):]
    if not data.startswith(":"):
        raise CertificateError("sparse6 data must start with ':'")
    n, values = decode_size(decode_values(data[1:], ""))
    k = max(1, (n - 1).bit_length())
    bits = [(v >> (5 - i)) & 1 for v in values for i in range(6)]
    adj = [0] * n
    v = 0
    for index in range(0, len(bits) - k, k + 1):
        if bits[index]:
            v += 1
        x = int("".join(map(str, bits[index + 1:index + k + 1])), 2)
        if x >= n or v >= n:
            break
        if x > v:
            v = x
        elif x == v:
            raise CertificateError("sparse6 data contains a loop")
        else:
            adj[x] |= 1 << v
            adj[v] |= 1 << x
    return adj


def encode_sparse6(adj: list[int]) -> str:
    """Encode a list of adjacency bitsets as a sparse6 string."""
    n = len(adj)
    k = max(1, (n - 1).bit_length())
    edge_bits = []
    v = 0
    for high in range(n):
        for low in bits(adj[high] & ((1 << high) - 1)):
            if high == v:
                edge_bits.append([0, low])
            elif high == v + 1:
                edge_bits.append([1, low])
            else:
                edge_bits += [[1, high], [0, low]]
            v = high
    out = [b for flag, x in edge_bits for b in [flag] + [(x >> (k - 1 - i)) & 1 for i in range(k)]]
    padding = -len(out) % 6
    # Padding of 1s could otherwise decode as an extra edge {v + 1, n - 1}
    if k < 6 and n == 1 << k and padding >= k and v < n - 1:
        out.append(0)
    out += [1] * (-len(out) % 6)
    values = encode_size(n) + [int("".join(map(str, out[i:i + 6])), 2) for i in range(0, len(out), 6)]
    return ":" + "".join(chr(v + 63) for v in values)


def read_graph(cert: Mapping[str, Any]) -> list[int]:
    """Decode a graph witness in graph6 or sparse6 format."""
    decoders = {"graph6": decode_graph6, "sparse6": decode_sparse6}
    fmt = cert["witness"].get("format")
    if fmt not in decoders:
        raise CertificateError("Graph witnesses must use format: graph6 or sparse6")
    return decoders[fmt](read_witness_data(cert))


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


def bits(mask: int) -> list[int]:
    """List the positions of the set bits in mask."""
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def girth(adj: list[int]) -> float:
    """Length of the shortest cycle, or infinity if the graph is acyclic.

    BFS from each vertex: an edge within layer i closes a walk of length
    2i + 1, and a vertex in layer i + 1 with two neighbors in layer i closes
    one of length 2i + 2. Each such walk contains a cycle at most that long,
    and every shortest cycle is found this way from one of its vertices.
    """
    best = float("inf")
    for source in range(len(adj)):
        seen = layer = 1 << source
        depth = 0
        while layer and 2 * depth + 1 < best:
            if any(adj[v] & layer for v in bits(layer)):
                best = 2 * depth + 1
                break
            next_layer = 0
            for v in bits(layer):
                new = adj[v] & ~seen
                if new & next_layer:
                    best = min(best, 2 * depth + 2)
                next_layer |= new
            seen |= next_layer
            layer = next_layer
            depth += 1
    return best


def eccentricity_at_most(adj: list[int], source: int, k: int) -> bool:
    """Check whether every vertex is within distance k of source."""
    full = (1 << len(adj)) - 1
    reached = 1 << source
    for _ in range(k):
        if reached == full:
            break
        new = 0
        for v in bits(reached):
            new |= adj[v]
        reached |= new
    return reached == full


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
    # (params, bound, value) -> Lean constant stating the bound, and its
    # natural number arguments.
    lean_statement: Callable[[Mapping[str, int], str, int | str], tuple[str, list[int]]]
    # (params, bound, value, cert) -> None, raising CertificateError if invalid.
    check_witness: Callable[[Mapping[str, int], str, int | str, Mapping[str, Any]], None]
    # Whether values can be square roots, written `\sqrt{m}`, besides integers.
    sqrt_values: bool = False


def ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Ramsey.{name}", [params['r'], params['s'], value]


def ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R(r,s) >= value is witnessed by a graph on value - 1 vertices with no
    r-clique and no independent set of size s."""
    if bound != "lower":
        raise CertificateError("Ramsey witnesses can only certify lower bounds")
    adj = read_graph(cert)
    if len(adj) != value - 1:
        raise CertificateError(f"Graph has {len(adj)} vertices, but R(r,s) >= {value} needs {value - 1}")
    if has_clique(adj, params["r"]):
        raise CertificateError(f"Graph contains a clique of size {params['r']}")
    if has_clique(complement(adj), params["s"]):
        raise CertificateError(f"Graph contains an independent set of size {params['s']}")


def van_der_waerden_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.VanDerWaerden.{name}", [params['r'], params['k'], value]


def has_monochromatic_ap(colors: str, k: int) -> bool:
    """Check whether a coloring (one character per integer) has a
    monochromatic arithmetic progression of length k."""
    n = len(colors)
    for color in set(colors):
        mask = sum(1 << i for i, c in enumerate(colors) if c == color)
        for d in range(1, (n - 1) // (k - 1) + 1):
            ap_starts = mask
            for i in range(1, k):
                ap_starts &= mask >> (i * d)
            if ap_starts:
                return True
    return False


def van_der_waerden_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """W(r,k) >= value is witnessed by an r-coloring of value - 1 consecutive
    integers with no monochromatic arithmetic progression of length k."""
    if bound != "lower":
        raise CertificateError("Van der Waerden witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "coloring":
        raise CertificateError("Van der Waerden witnesses must use format: coloring")
    r, k = params["r"], params["k"]
    if r > 10 or k < 2:
        raise CertificateError("Van der Waerden witnesses need r <= 10 and k >= 2")
    colors = "".join(read_witness_data(cert).split())
    if not set(colors) <= set("0123456789"[:r]):
        raise CertificateError(f"Coloring must use the digits 0 to {r - 1}")
    if len(colors) != value - 1:
        raise CertificateError(f"Coloring has {len(colors)} integers, but W(r,k) >= {value} needs {value - 1}")
    if has_monochromatic_ap(colors, k):
        raise CertificateError(f"Coloring has a monochromatic arithmetic progression of length {k}")


def cage_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Cage.{name}", [params['k'], params['g'], value]


def cage_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """n(k,g) <= value is witnessed by a k-regular graph of girth g on value
    vertices."""
    if bound != "upper":
        raise CertificateError("Cage witnesses can only certify upper bounds")
    adj = read_graph(cert)
    if len(adj) != value:
        raise CertificateError(f"Graph has {len(adj)} vertices, but n(k,g) <= {value} needs {value}")
    if any(neighbors.bit_count() != params["k"] for neighbors in adj):
        raise CertificateError(f"Graph is not {params['k']}-regular")
    if girth(adj) != params["g"]:
        raise CertificateError(f"Graph has girth {girth(adj)}, not {params['g']}")


def degree_diameter_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.DegreeDiameter.{name}", [params['d'], params['k'], value]


def degree_diameter_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """N(d,k) >= value is witnessed by a graph on value vertices with maximum
    degree at most d and diameter at most k."""
    if bound != "lower":
        raise CertificateError("Degree-diameter witnesses can only certify lower bounds")
    adj = read_graph(cert)
    if len(adj) != value:
        raise CertificateError(f"Graph has {len(adj)} vertices, but N(d,k) >= {value} needs {value}")
    if any(neighbors.bit_count() > params["d"] for neighbors in adj):
        raise CertificateError(f"Graph has a vertex of degree more than {params['d']}")
    if not all(eccentricity_at_most(adj, v, params["k"]) for v in range(len(adj))):
        raise CertificateError(f"Graph has diameter more than {params['k']}")


def superpermutation_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Superpermutation.{name}", [params['n'], value]


def superpermutation_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """L(n) <= value is witnessed by a string of length at most value that
    contains every permutation of n symbols."""
    if bound != "upper":
        raise CertificateError("Superpermutation witnesses can only certify upper bounds")
    if cert["witness"].get("format") != "string":
        raise CertificateError("Superpermutation witnesses must use format: string")
    n = params["n"]
    if not 1 <= n <= 9:
        raise CertificateError("Superpermutation witnesses need 1 <= n <= 9")
    symbols = set("123456789"[:n])
    string = "".join(read_witness_data(cert).split())
    if not set(string) <= symbols:
        raise CertificateError(f"String must use the digits 1 to {n}")
    if len(string) > value:
        raise CertificateError(f"String has length {len(string)}, more than {value}")
    windows = {string[i:i + n] for i in range(len(string) - n + 1)}
    found = sum(set(window) == symbols for window in windows)
    if found != math.factorial(n):
        raise CertificateError(f"String contains {found} of the {math.factorial(n)} permutations")


def kissing_number_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.KissingNumber.{name}", [params['n'], value]


def read_vectors(data: str) -> list[tuple[int, ...]]:
    """Parse integer vectors, one per line, with whitespace-separated entries."""
    try:
        vectors = [tuple(int(x) for x in line.split()) for line in data.splitlines() if line.strip()]
    except ValueError:
        raise CertificateError("Vectors must have integer entries")
    if not vectors or len({len(v) for v in vectors}) != 1:
        raise CertificateError("Vectors must all have the same length")
    return vectors


def read_symmetries(symmetries: Any, dim: int) -> list[tuple[int, ...]]:
    """Check signed permutations of dim coordinates: s maps x to the vector
    whose i-th entry is sign(s[i]) * x[|s[i]|], with coordinates numbered from
    1."""
    if not isinstance(symmetries, list):
        raise CertificateError("symmetries must be a list of signed permutations")
    out = []
    for s in symmetries:
        if (not isinstance(s, list) or not all(isinstance(x, int) for x in s)
                or sorted(abs(x) for x in s) != list(range(1, dim + 1))):
            raise CertificateError(f"Symmetry {s} is not a signed permutation of 1..{dim}")
        out.append(tuple(s))
    return out


def orbit_closure(seeds: list[tuple[int, ...]], symmetries: list[tuple[int, ...]], limit: int) -> list[tuple[int, ...]]:
    """All images of the seeds under the group generated by the symmetries."""
    seen = set(seeds)
    queue = list(seen)
    while queue:
        v = queue.pop()
        for s in symmetries:
            w = tuple(v[i - 1] if i > 0 else -v[-i - 1] for i in s)
            if w not in seen:
                seen.add(w)
                queue.append(w)
                if len(seen) > limit:
                    raise CertificateError(f"Configuration has more than {limit} vectors")
    return sorted(seen)


def span_dimension_at_most(vectors: list[tuple[int, ...]], n: int) -> bool:
    """Exactly check whether the vectors span a space of dimension at most n.

    Picks a basis candidate in floating point, then checks exactly that its
    rows are independent and that every vector is orthogonal to the integer
    null space of the candidate.
    """
    x = np.array(vectors, dtype=np.float64)
    basis = []
    q = np.zeros((0, x.shape[1]))
    while True:
        residual = x - (x @ q.T) @ q
        norms = np.einsum("ij,ij->i", residual, residual)
        i = int(np.argmax(norms))
        if norms[i] < 1e-6 or len(basis) > n:
            break
        basis.append(vectors[i])
        q = np.vstack([q, residual[i] / math.sqrt(norms[i])])
    if len(basis) > n:
        return False
    b = sympy.Matrix(basis)
    if b.rank() != len(basis):
        return False
    null = []
    for v in b.nullspace():
        scale = sympy.ilcm(*[entry.q for entry in v])
        null.append([int(entry * scale) for entry in v])
    if not null:
        return True
    p = np.array(null, dtype=object)
    return not np.any(np.array(vectors, dtype=object) @ p.T)


def kissing_number_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """A kissing configuration of value unit vectors in R^n, with angles of at
    least 60 degrees between them, is witnessed by integer vectors of the same
    squared norm N, spanning a space of dimension at most n, whose pairwise
    inner products are at most N / 2.

    The vectors can be listed in full, or as seeds whose orbits under some
    signed permutations of the coordinates make up the configuration. Signed
    permutations preserve inner products, so it suffices to compare each seed
    with every vector.
    """
    if bound != "lower":
        raise CertificateError("Kissing number witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "vectors":
        raise CertificateError("Kissing number witnesses must use format: vectors")
    seeds = read_vectors(read_witness_data(cert))
    dim = len(seeds[0])
    if dim > 64 or any(abs(x) > 2**20 for v in seeds for x in v):
        raise CertificateError("Vectors must have at most 64 coordinates, each at most 2^20 in absolute value")
    symmetries = read_symmetries(cert["witness"].get("symmetries", []), dim)
    vectors = orbit_closure(seeds, symmetries, limit=10**6)
    if len(vectors) != value:
        raise CertificateError(f"Configuration has {len(vectors)} vectors, not {value}")
    norms = {sum(x * x for x in s) for s in seeds}
    if len(norms) != 1 or 0 in norms:
        raise CertificateError("Vectors must be nonzero with the same squared norm")
    norm = norms.pop()
    if not span_dimension_at_most(vectors, params["n"]):
        raise CertificateError(f"Vectors span a space of dimension more than {params['n']}")
    all_vectors = np.array(vectors, dtype=np.int64)
    index = {v: i for i, v in enumerate(vectors)}
    for start in range(0, len(seeds), 256):
        block = seeds[start:start + 256]
        products = np.array(block, dtype=np.int64) @ all_vectors.T
        for row, s in enumerate(block):
            products[row, index[s]] = 0
        if np.any(2 * products > norm):
            raise CertificateError(f"Some vectors have inner product more than {norm} / 2")


def square_packing_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[int]]:
    name = "SqrtLowerBound" if bound == "lower" else "SqrtUpperBound"
    return f"LeapsInBounds.SquarePacking.{name}", [params['n'], sqrt_argument(value)]


def square_packing_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Square packing bounds can only be certified by Lean proofs so far")


# Keyed by constant group ID.
FAMILIES = {
    "ramsey": Family(
        id_pattern=re.compile(r"ramsey-(?P<r>\d+)-(?P<s>\d+)"),
        lean_module="LeapsInBounds.Statements.Ramsey",
        lean_statement=ramsey_lean_statement,
        check_witness=ramsey_check_witness,
    ),
    "van-der-waerden": Family(
        id_pattern=re.compile(r"van-der-waerden-(?P<r>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.VanDerWaerden",
        lean_statement=van_der_waerden_lean_statement,
        check_witness=van_der_waerden_check_witness,
    ),
    "cage": Family(
        id_pattern=re.compile(r"cage-(?P<k>\d+)-(?P<g>\d+)"),
        lean_module="LeapsInBounds.Statements.Cage",
        lean_statement=cage_lean_statement,
        check_witness=cage_check_witness,
    ),
    "degree-diameter": Family(
        id_pattern=re.compile(r"degree-diameter-(?P<d>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.DegreeDiameter",
        lean_statement=degree_diameter_lean_statement,
        check_witness=degree_diameter_check_witness,
    ),
    "minimal-superpermutation": Family(
        id_pattern=re.compile(r"minimal-superpermutation-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Superpermutation",
        lean_statement=superpermutation_lean_statement,
        check_witness=superpermutation_check_witness,
    ),
    "kissing-number": Family(
        id_pattern=re.compile(r"kissing-number-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.KissingNumber",
        lean_statement=kissing_number_lean_statement,
        check_witness=kissing_number_check_witness,
    ),
    "square-packing": Family(
        id_pattern=re.compile(r"square-packing-in-square-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SquarePacking",
        lean_statement=square_packing_lean_statement,
        check_witness=square_packing_check_witness,
        sqrt_values=True,
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

def check_lean(certs: list[Mapping[str, Any]], build: bool = True) -> dict[str, str]:
    """Check that each certificate's named theorem proves the expected
    statement using only allowed axioms. Returns an error message for each
    certificate that fails.

    Builds the proof modules first unless build is False, in which case they
    must already be compiled. Building runs the submission's code, so CI
    builds them in a separate job.

    The comparison is done by scripts/check_lean.lean, which builds the
    expected statement directly rather than elaborating it alongside the
    submitted proof, and replays the proofs through the kernel.
    """
    errors = {}
    entries = []
    for cert in certs:
        module = cert["lean"]["module"]
        if not module.startswith("LeapsInBounds.Proofs."):
            errors[cert["id"]] = "Lean proofs must live under LeapsInBounds.Proofs"
            continue
        family, params = get_family(cert["constant"])
        statement, args = family.lean_statement(params, cert["bound"], cert["value"])
        entries.append({
            "id": cert["id"],
            "statementModule": family.lean_module,
            "statement": statement,
            "args": args,
            "proofModule": module,
            "theorem": cert["lean"]["theorem"],
        })
    modules = sorted({entry["proofModule"] for entry in entries})
    if not modules:
        return errors
    if build:
        result = subprocess.run(["lake", "build", *modules], cwd=FORMAL_DIR, capture_output=True, text=True)
        if result.returncode != 0:
            output = result.stdout + result.stderr
            return errors | {entry["id"]: f"lake build failed:\n{output}" for entry in entries}
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as file:
        json.dump(entries, file)
        input_path = pathlib.Path(file.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(CHECK_LEAN_SCRIPT.resolve()), str(input_path)],
            cwd=FORMAL_DIR, capture_output=True, text=True,
        )
    finally:
        input_path.unlink()
    try:
        failures = json.loads(result.stdout) if result.returncode == 0 else None
    except json.JSONDecodeError:
        failures = None
    if failures is None:
        output = result.stdout + result.stderr
        return errors | {entry["id"]: f"Lean check failed:\n{output}" for entry in entries}
    for entry in entries:
        if entry["id"] in failures:
            statement = " ".join([entry["statement"], *map(str, entry["args"])])
            errors[entry["id"]] = f"Theorem {entry['theorem']} does not prove `{statement}`: {failures[entry['id']]}"
    return errors


def check_witness(cert: Mapping[str, Any]) -> None:
    """Verify a witness certificate's evidence."""
    family, params = get_family(cert["constant"])
    family.check_witness(params, cert["bound"], cert["value"], cert)


def is_better(bound: str, a: float, b: float) -> bool:
    """Whether bound value a is strictly stronger than b."""
    return a > b if bound == "lower" else a < b


def best_certificates(certificates: Mapping[str, Mapping[str, Any]]) -> dict[tuple[str, str], Mapping[str, Any]]:
    """Find the strongest certificate for each (constant, bound) pair.
    Ties go to the earliest date."""
    best = {}
    for cert in sorted(certificates.values(), key=lambda c: c["date"]):
        key = (cert["constant"], cert["bound"])
        if key not in best or is_better(cert["bound"], cert["approx"], best[key]["approx"]):
            best[key] = cert
    return best
