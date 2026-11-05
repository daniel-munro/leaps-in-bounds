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

import itertools
import json
import math
import pathlib
import re
import subprocess
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Mapping

import numpy as np
import sympy
import yaml

CERTIFICATES_DIR = pathlib.Path("certificates")
FORMAL_DIR = pathlib.Path("formal")
CHECK_LEAN_SCRIPT = pathlib.Path("scripts/check_lean.lean")

REQUIRED_FIELDS = ["constant", "bound", "value", "kind", "submitted_by", "date"]
GITHUB_USERNAME = re.compile(r"[A-Za-z0-9](?:-?[A-Za-z0-9]){0,38}")


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
        if not isinstance(cert["submitted_by"], str) or not GITHUB_USERNAME.fullmatch(cert["submitted_by"]):
            raise CertificateError(f"{path}: submitted_by must be a GitHub username")
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


#########
# Values #
#########

# Bounds are integers, or for some families square roots `\sqrt{m}` or sums of
# rational multiples of square roots, such as `4+2\sqrt{3}+\frac{4\sqrt{6}}{3}`
# (see Family.values).

SQRT_PATTERN = re.compile(r"\\sqrt\{(\d+)\}")
RADICAL_TERM = re.compile(r"([+-]?)(?:\\frac\{(\d*)(?:\\sqrt\{(\d+)\})?\}\{(\d+)\}|(\d*)(?:\\sqrt\{(\d+)\})?)")
MAX_RADICAND = 10**9


def squarefree_part(m: int) -> tuple[int, int]:
    """Write m = k² r with r squarefree, returning (k, r)."""
    k, r, p = 1, 1, 2
    while p * p <= m:
        while m % (p * p) == 0:
            m //= p * p
            k *= p
        if m % p == 0:
            m //= p
            r *= p
        p += 1
    return k, r * m


def prime_factors(m: int) -> list[int]:
    """The distinct prime factors of m, in increasing order."""
    primes, p = [], 2
    while p * p <= m:
        if m % p == 0:
            primes.append(p)
            while m % p == 0:
                m //= p
        p += 1
    return primes + [m] if m > 1 else primes


class Radical:
    """An exact real number ∑ cᵢ √mᵢ, with rational cᵢ and distinct squarefree
    mᵢ (mᵢ = 1 for the rational part), stored as {mᵢ: cᵢ}."""

    def __init__(self, terms: Mapping[int, Fraction] | None = None) -> None:
        self.terms = {m: Fraction(c) for m, c in (terms or {}).items() if c}

    @classmethod
    def sqrt(cls, m: int, c: Fraction | int = 1) -> "Radical":
        """c √m."""
        k, r = squarefree_part(m)
        return cls({r: Fraction(c) * k})

    def __add__(self, other: "Radical | Fraction | int") -> "Radical":
        terms = dict(self.terms)
        for m, c in to_radical(other).terms.items():
            terms[m] = terms.get(m, 0) + c
        return Radical(terms)

    __radd__ = __add__

    def __neg__(self) -> "Radical":
        return Radical({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: "Radical | Fraction | int") -> "Radical":
        return self + -to_radical(other)

    def __rsub__(self, other: "Radical | Fraction | int") -> "Radical":
        return to_radical(other) + -self

    def __mul__(self, other: "Radical | Fraction | int") -> "Radical":
        out = Radical()
        for m, c in self.terms.items():
            for n, d in to_radical(other).terms.items():
                g = math.gcd(m, n)  # √m √n = g √(mn / g²)
                out += Radical({m * n // (g * g): c * d * g})
        return out

    __rmul__ = __mul__

    def sign(self) -> int:
        """The exact sign: -1, 0 or 1.

        For the largest prime p in a radicand, write x = u + v √p with no √p
        in u or v. If u and v have the same sign (or one is 0), so does x.
        Otherwise x has the sign of u times that of u² - p v², since
        x (u - v √p) = u² - p v² and u - v √p has the sign of u.
        """
        if not self.terms:
            return 0
        p = max(max(prime_factors(m), default=1) for m in self.terms)
        if p == 1:
            return 1 if self.terms[1] > 0 else -1
        u = Radical({m: c for m, c in self.terms.items() if m % p})
        v = Radical({m // p: c for m, c in self.terms.items() if m % p == 0})
        su, sv = u.sign(), v.sign()
        if su == 0 or su == sv:
            return sv
        if sv == 0:
            return su
        return su * (u * u - p * v * v).sign()

    def __float__(self) -> float:
        return math.fsum(float(c) * math.sqrt(m) for m, c in self.terms.items())

    def lean_args(self) -> tuple[list[list[int]], int]:
        """The terms [[c₁, m₁], ...] and denominator d with self = (∑ cᵢ √mᵢ) / d,
        for integers cᵢ, d the least common denominator, and mᵢ increasing."""
        d = math.lcm(*(c.denominator for c in self.terms.values()))
        return [[int(c * d), m] for m, c in sorted(self.terms.items())], d


def to_radical(x: "Radical | Fraction | int") -> Radical:
    return x if isinstance(x, Radical) else Radical({1: Fraction(x)})


def parse_radical(text: Any) -> Radical:
    """Parse an integer, or a string summing terms `a`, `a\\sqrt{m}` or
    `\\frac{a\\sqrt{m}}{b}`, each with an optional sign, where a can be
    omitted before a square root."""
    if isinstance(text, int) and not isinstance(text, bool):
        return to_radical(text)
    error = CertificateError(f"Can't read {text!r} as a sum of rational multiples of square roots")
    if not isinstance(text, str):
        raise error
    s = re.sub(r"\s*([+-])\s*", r"\1", text.strip())
    if not s or any(c.isspace() for c in s):
        raise error
    total, pos = Radical(), 0
    while pos < len(s):
        match = RADICAL_TERM.match(s, pos)
        if match.end() == pos or (pos > 0 and not match.group(1)):
            raise error
        sign, frac_coef, frac_root, den, coef, root = match.groups()
        if den is not None:
            coef, root = frac_coef, frac_root
        if not coef and not root:
            raise error
        c, m, d = int(coef or 1), int(root or 1), int(den or 1)
        if d == 0 or m > MAX_RADICAND:
            raise error
        total += Radical.sqrt(m, Fraction(-c if sign == "-" else c, d))
        pos = match.end()
    return total


def value_approx(value: Any, path: Any = None) -> float:
    """Numeric value of a certificate's bound: an integer, or a string that
    parse_radical reads."""
    try:
        return float(parse_radical(value))
    except CertificateError:
        raise CertificateError(f"{path}: value must be an integer or a sum of rational multiples of square roots, not {value!r}")


def check_value_type(values: str, value: Any) -> None:
    """Check that a value has a form allowed by a family (see Family.values)."""
    if isinstance(value, int) and not isinstance(value, bool):
        return
    if values == "sqrt" and isinstance(value, str) and SQRT_PATTERN.fullmatch(value):
        return
    if values == "radical":
        parse_radical(value)
        return
    allowed = {"integer": "integers", "sqrt": "integers or '\\sqrt{m}'"}.get(values)
    raise CertificateError(f"Values for this family must be {allowed}")


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
    reached = layer = 1 << source
    for _ in range(k):
        if reached == full:
            break
        new = 0
        for v in bits(layer):
            new |= adj[v]
        layer = new & ~reached
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
    # arguments: natural numbers, or lists of [integer, natural number] pairs
    # (List (ℤ × ℕ) in Lean).
    lean_statement: Callable[[Mapping[str, int], str, int | str], tuple[str, list[Any]]]
    # (params, bound, value, cert) -> None, raising CertificateError if invalid.
    check_witness: Callable[[Mapping[str, int], str, int | str, Mapping[str, Any]], None]
    # Which bound a witness can certify ("lower" or "upper"), or None if only
    # Lean proofs are accepted.
    witness_bound: str | None
    # Which values are allowed: "integer", "sqrt" (also `\sqrt{m}`), or
    # "radical" (sums of rational multiples of square roots, read by
    # parse_radical).
    values: str = "integer"


def ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Ramsey.{name}", [params['r'], params['s'], value]


def ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R(r,s) >= value is witnessed by a graph on value - 1 vertices with no
    r-clique and no independent set of size s."""
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


def circle_in_triangle_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.CircleInTriangle.{name}", [params['n'], terms, d]


def read_points(data: str) -> list[tuple[Radical, Radical]]:
    """Parse points `x, y`, one per line, with coordinates read by
    parse_radical."""
    points = []
    for line in data.splitlines():
        if line.strip():
            coords = line.split(",")
            if len(coords) != 2:
                raise CertificateError(f"Expected a point 'x, y', not {line.strip()!r}")
            points.append((parse_radical(coords[0]), parse_radical(coords[1])))
    return points


def circle_in_triangle_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    """The side s(n) of the smallest equilateral triangle containing n unit
    circles with disjoint interiors is at most value if there are n centers
    at distance at least 2 from each other, and at least 1 from each side of
    the triangle with vertices (0, 0), (value, 0) and (value / 2, value √3 / 2).

    Coordinates are exact sums of rational multiples of square roots, so the
    inequalities, including the equalities where circles touch, are decided
    exactly.
    """
    if cert["witness"].get("format") != "points":
        raise CertificateError("Circle packing witnesses must use format: points")
    s = parse_radical(value)
    points = read_points(read_witness_data(cert))
    if len(points) != params["n"]:
        raise CertificateError(f"Witness has {len(points)} centers, not {params['n']}")
    # Deciding signs takes time exponential in the number of primes
    radicands = {m for x, y in points for m in [*x.terms, *y.terms, *s.terms]}
    if len({p for m in radicands for p in prime_factors(m)}) > 6:
        raise CertificateError("Coordinates can use square roots of at most 6 different primes")
    sqrt3 = Radical.sqrt(3)
    for i, (x, y) in enumerate(points):
        # Distances to the sides y = 0, y = √3 x and y = √3 (s - x)
        if (y - 1).sign() < 0 or (sqrt3 * x - y - 2).sign() < 0 or (sqrt3 * (s - x) - y - 2).sign() < 0:
            raise CertificateError(f"Circle {i + 1} is not inside the triangle")
    for i in range(len(points)):
        for j in range(i):
            dx, dy = points[i][0] - points[j][0], points[i][1] - points[j][1]
            if (dx * dx + dy * dy - 4).sign() < 0:
                raise CertificateError(f"Circles {j + 1} and {i + 1} overlap")


def schur_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Schur.{name}", [params['k'], value]


def weak_schur_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "WeakLowerBound" if bound == "lower" else "WeakUpperBound"
    return f"LeapsInBounds.Schur.{name}", [params['k'], value]


def has_monochromatic_sum(colors: str, weak: bool = False) -> bool:
    """Check whether a coloring of 1, ..., n (one character per integer) has
    a monochromatic solution to x + y = z, with x ≠ y if weak."""
    for color in set(colors):
        # Bit i is set if integer i has this color
        mask = sum(1 << (i + 1) for i, c in enumerate(colors) if c == color)
        for x in bits(mask):
            # Bit y is set if y and x + y both have this color
            sums = (mask >> x) & mask
            if weak:
                sums &= ~(1 << x)
            if sums:
                return True
    return False


def schur_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], weak: bool) -> None:
    """S(k) >= value (or WS(k) >= value) is witnessed by a k-coloring of 1, ...,
    value with no monochromatic solution to x + y = z (with x ≠ y for WS)."""
    if cert["witness"].get("format") != "coloring":
        raise CertificateError("Schur witnesses must use format: coloring")
    k = params["k"]
    if k > 10:
        raise CertificateError("Schur witnesses need k <= 10")
    colors = "".join(read_witness_data(cert).split())
    if not set(colors) <= set("0123456789"[:k]):
        raise CertificateError(f"Coloring must use the digits 0 to {k - 1}")
    if len(colors) != value:
        raise CertificateError(f"Coloring has {len(colors)} integers, but a lower bound of {value} needs {value}")
    if has_monochromatic_sum(colors, weak):
        raise CertificateError(f"Coloring has a monochromatic solution to x + y = z{' with x ≠ y' if weak else ''}")


def schur_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    schur_witness(params, bound, value, cert, weak=False)


def weak_schur_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    schur_witness(params, bound, value, cert, weak=True)


def golomb_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Golomb.{name}", [params['n'], value]


def read_marks(data: str) -> list[int]:
    """Parse marks: integers separated by whitespace or commas."""
    try:
        return [int(x) for x in data.replace(",", " ").split()]
    except ValueError:
        raise CertificateError("Marks must be integers")


def golomb_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """G(n) <= value is witnessed by n distinct marks in 0, ..., value whose
    pairwise differences are distinct."""
    if cert["witness"].get("format") != "marks":
        raise CertificateError("Golomb ruler witnesses must use format: marks")
    marks = read_marks(read_witness_data(cert))
    if len(set(marks)) != len(marks):
        raise CertificateError("Marks must be distinct")
    if len(marks) != params["n"]:
        raise CertificateError(f"Ruler has {len(marks)} marks, not {params['n']}")
    if any(not 0 <= a <= value for a in marks):
        raise CertificateError(f"Marks must be between 0 and {value}")
    differences = [b - a for a, b in itertools.combinations(sorted(marks), 2)]
    if len(set(differences)) != len(differences):
        raise CertificateError("Two pairs of marks are the same distance apart")


def snake_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.SnakeInTheBox.{name}", [params['n'], value]


def coil_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "CoilLowerBound" if bound == "lower" else "CoilUpperBound"
    return f"LeapsInBounds.SnakeInTheBox.{name}", [params['n'], value]


def read_transitions(data: str, n: int) -> list[int]:
    """Parse a transition sequence: one character per coordinate, from 0 to
    n - 1, written in base 36 (0 to 9, then a to z). Whitespace is ignored."""
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"[:n]
    transitions = "".join(data.split()).lower()
    if not set(transitions) <= set(digits):
        raise CertificateError(f"Transitions must be coordinates from 0 to {digits[-1]}")
    return [digits.index(c) for c in transitions]


def transition_vertices(transitions: list[int]) -> list[int]:
    """The vertices of Q_n, as bitmasks, visited by flipping each coordinate
    in turn, starting at 0."""
    vertices = [0]
    for c in transitions:
        vertices.append(vertices[-1] ^ (1 << c))
    return vertices


def is_snake(transitions: list[int], n: int, coil: bool = False) -> bool:
    """Check that the transitions trace an induced path in Q_n (an induced
    cycle, back to the start, if coil): its vertices are distinct and
    adjacent only when they're consecutive."""
    vertices = transition_vertices(transitions)
    if coil:
        if len(vertices) < 4 or vertices.pop() != 0:
            return False
    position = {v: i for i, v in enumerate(vertices)}
    if len(position) != len(vertices):
        return False
    length = len(vertices)
    for i, v in enumerate(vertices):
        for c in range(n):
            j = position.get(v ^ (1 << c))
            if j is None:
                continue
            gap = abs(i - j)
            if gap != 1 and not (coil and gap == length - 1):
                return False
    return True


def snake_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], coil: bool) -> None:
    """A snake (or coil) of length L in Q_n witnesses that the longest one has
    length at least L. It's given by its transition sequence: the coordinate
    that changes along each edge, starting from the vertex 0."""
    kind = "Coil" if coil else "Snake"
    if cert["witness"].get("format") != "transitions":
        raise CertificateError(f"{kind} witnesses must use format: transitions")
    n = params["n"]
    if n > 36:
        raise CertificateError(f"{kind} witnesses need n <= 36")
    transitions = read_transitions(read_witness_data(cert), n)
    if len(transitions) != value:
        raise CertificateError(f"{kind} has {len(transitions)} edges, but a lower bound of {value} needs {value}")
    if not is_snake(transitions, n, coil):
        if coil:
            raise CertificateError("Transitions don't trace an induced cycle in the hypercube")
        raise CertificateError("Transitions don't trace an induced path in the hypercube")


def snake_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    snake_witness(params, bound, value, cert, coil=False)


def coil_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    snake_witness(params, bound, value, cert, coil=True)


def cap_set_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.CapSet.{name}", [params['n'], value]


def read_ternary_points(data: str, n: int) -> list[tuple[int, ...]]:
    """Parse points of F_3^n: whitespace-separated words of n digits from 0
    to 2, one per coordinate."""
    points = []
    for word in data.split():
        if len(word) != n or not set(word) <= set("012"):
            raise CertificateError(f"Points must be {n} digits from 0 to 2, not {word[:40]!r}")
        points.append(tuple(int(c) for c in word))
    return points


def is_cap(points: list[tuple[int, ...]]) -> bool:
    """Check that the points are distinct and no three of them are on a line:
    no distinct x, y, z with x + y + z = 0, since the third point on the line
    through x and y is -(x + y)."""
    point_set = set(points)
    if len(point_set) != len(points):
        return False
    for i, x in enumerate(points):
        for y in points[i + 1:]:
            if tuple(-(a + b) % 3 for a, b in zip(x, y)) in point_set:
                return False
    return True


def cap_set_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """r(n) >= value is witnessed by value points of F_3^n with no three on a
    line."""
    if bound != "lower":
        raise CertificateError("Cap set witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "points":
        raise CertificateError("Cap set witnesses must use format: points")
    points = read_ternary_points(read_witness_data(cert), params["n"])
    if len(points) != value:
        raise CertificateError(f"Witness has {len(points)} points, but a lower bound of {value} needs {value}")
    if not is_cap(points):
        raise CertificateError("Points aren't distinct, or three of them are on a line")


def no_three_in_line_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.NoThreeInLine.{name}", [params['n'], value]


def read_grid_points(data: str) -> list[tuple[int, int]]:
    """Parse grid points `x,y`: two natural numbers joined by a comma, the
    points separated by whitespace."""
    points = []
    for word in data.split():
        match = re.fullmatch(r"(\d+),(\d+)", word)
        if not match:
            raise CertificateError(f"Points must be written x,y, not {word[:40]!r}")
        points.append((int(match.group(1)), int(match.group(2))))
    return points


def line_through(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int, int]:
    """The line through two distinct integer points, as coprime (a, b, c) with
    ax + by = c, normalized so that each line has one representation."""
    a, b = q[1] - p[1], p[0] - q[0]
    g = math.gcd(a, b)
    a, b = a // g, b // g
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * p[0] + b * p[1]


def no_three_collinear(points: list[tuple[int, int]]) -> bool:
    """Check that the points are distinct and no three are on a line: no two
    pairs of them span the same line."""
    if len(set(points)) != len(points):
        return False
    lines = set()
    for i, p in enumerate(points):
        for q in points[i + 1:]:
            line = line_through(p, q)
            if line in lines:
                return False
            lines.add(line)
    return True


def no_three_in_line_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """D(n) >= value is witnessed by value points of the n x n grid with no
    three on a line."""
    if bound != "lower":
        raise CertificateError("No-three-in-line witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "points":
        raise CertificateError("No-three-in-line witnesses must use format: points")
    n = params["n"]
    points = read_grid_points(read_witness_data(cert))
    if len(points) != value:
        raise CertificateError(f"Witness has {len(points)} points, but a lower bound of {value} needs {value}")
    if not all(x < n and y < n for x, y in points):
        raise CertificateError(f"Points must have coordinates from 0 to {n - 1}")
    if not no_three_collinear(points):
        raise CertificateError("Points aren't distinct, or three of them are on a line")


def line_arrangement_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.LineArrangement.{name}", [params['n'], value]


def general_line_arrangement_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "GeneralLowerBound" if bound == "lower" else "GeneralUpperBound"
    return f"LeapsInBounds.LineArrangement.{name}", [params['n'], value]


Line = tuple[int, int, int]
Point = tuple[Fraction, Fraction]


def read_arrangements(data: str, n: int) -> list[list[Line]]:
    """Parse arrangements, one per line of text: 3n integers, with a, b, c for
    each line a x + b y = c."""
    arrangements = []
    for row in data.splitlines():
        if not row.strip():
            continue
        try:
            values = [int(x) for x in row.split()]
        except ValueError:
            raise CertificateError("Line coefficients must be integers")
        if len(values) != 3 * n:
            raise CertificateError(f"Each arrangement needs {3 * n} integers, found {len(values)}")
        arrangements.append([tuple(values[3 * i:3 * i + 3]) for i in range(n)])
    return arrangements


def intersect_lines(l1: Line, l2: Line) -> Point | None:
    """The intersection point of two lines, or None if they're parallel."""
    a1, b1, c1 = l1
    a2, b2, c2 = l2
    det = a1 * b2 - a2 * b1
    if det == 0:
        return None
    return Fraction(c1 * b2 - c2 * b1, det), Fraction(a1 * c2 - a2 * c1, det)


def sign(x: Fraction | int) -> int:
    return (x > 0) - (x < 0)


def sides(lines: list[Line], p: Point) -> tuple[int, ...]:
    """The covector of p: which side of each line it's on."""
    return tuple(sign(a * p[0] + b * p[1] - c) for a, b, c in lines)


def arrangement_covectors(lines: list[Line]) -> set[tuple[int, ...]]:
    """All covectors of an arrangement: those of the vertices, of a point on
    each edge, and of points on either side of each edge (every face is next to
    an edge)."""
    n = len(lines)
    on_line: list[set[Point]] = [set() for _ in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        p = intersect_lines(lines[i], lines[j])
        if p is not None:
            on_line[i].add(p)
            on_line[j].add(p)
    result = set()
    for i, (a, b, c) in enumerate(lines):
        direction = (-b, a)
        points = sorted(on_line[i], key=lambda p: p[0] * direction[0] + p[1] * direction[1])
        result.update(sides(lines, p) for p in points)
        if points:
            first, last = points[0], points[-1]
            samples = [(first[0] - direction[0], first[1] - direction[1]),
                       (last[0] + direction[0], last[1] + direction[1])]
            samples += [((p[0] + q[0]) / 2, (p[1] + q[1]) / 2) for p, q in zip(points, points[1:])]
        else:
            samples = [(Fraction(a * c, a * a + b * b), Fraction(b * c, a * a + b * b))]
        for p in samples:
            edge = sides(lines, p)
            result.add(edge)
            result.add(edge[:i] + (1,) + edge[i + 1:])
            result.add(edge[:i] + (-1,) + edge[i + 1:])
    return result


def line_ends(lines: list[Line]) -> list[tuple[int, tuple[int, int]]]:
    """The 2n ends of the lines, in counterclockwise order around a large
    circle: (i, u) is the end of line i in direction u."""
    def key(end: tuple[int, tuple[int, int]]) -> tuple[Any, ...]:
        i, (x, y) = end
        a, b, c = lines[i]
        g = math.gcd(x, y)
        x, y = x // g, y // g
        # Angles in [0, pi), then in [pi, 2 pi). In each half, the angle
        # increases as x / y decreases, starting from the direction with y = 0.
        half = 0 if y > 0 or (y == 0 and x > 0) else 1
        angle = (0, 0) if y == 0 else (1, Fraction(-x, y))
        # Ends in the same direction, of parallel lines, are ordered by how far
        # each line is to the left, with (x, y) reduced to compare exactly.
        offset = Fraction(c * (-a * y + b * x), a * a + b * b)
        return half, angle, offset
    ends = [(i, u) for i, (a, b, _) in enumerate(lines) for u in ((-b, a), (b, -a))]
    return sorted(ends, key=key)


def arrangement_type(lines: list[Line]) -> tuple[tuple[int, ...], ...]:
    """A canonical form of the combinatorial type of an arrangement: its
    covectors, with the lines renumbered and their sides chosen as follows,
    minimized over the start and direction of a walk around the ends of the
    lines. Number the lines in the order the walk first meets them, and make
    positive the side of each line that the walk goes on to, after the first
    end of the line.

    An equivalence of two arrangements comes from a homeomorphism of the plane
    taking lines to lines, which takes the ends in order around a large circle
    to the ends in the same or the opposite order. So it takes each numbering
    and choice of sides above to another, and equivalent arrangements get the
    same form.
    """
    n = len(lines)
    covectors = arrangement_covectors(lines)
    ends = line_ends(lines)
    best = None
    for start in range(2 * n):
        for direction in (1, -1):
            order: list[int] = []
            signs = [0] * n
            for t in range(2 * n):
                i, (x, y) = ends[(start + direction * t) % (2 * n)]
                if not signs[i]:
                    a, b, _ = lines[i]
                    order.append(i)
                    # The side to the left of the line, heading toward this
                    # end, comes after it counterclockwise.
                    signs[i] = direction * sign(-a * y + b * x)
            form = tuple(sorted(tuple(v[i] * signs[i] for i in order) for v in covectors))
            if best is None or form < best:
                best = form
    return best


def is_general_position(lines: list[Line]) -> bool:
    points = []
    for l1, l2 in itertools.combinations(lines, 2):
        p = intersect_lines(l1, l2)
        if p is None:
            return False
        points.append(p)
    return len(set(points)) == len(points)


def line_arrangement_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], general: bool) -> None:
    """There are at least `value` types of arrangements of n lines (in general
    position) when `value` such arrangements are pairwise inequivalent."""
    if cert["witness"].get("format") != "lines":
        raise CertificateError("Line arrangement witnesses must use format: lines")
    n = params["n"]
    arrangements = read_arrangements(read_witness_data(cert), n)
    if len(arrangements) != value:
        raise CertificateError(f"Witness has {len(arrangements)} arrangements, not {value}")
    types = set()
    for k, lines in enumerate(arrangements, 1):
        if any(a == 0 and b == 0 for a, b, _ in lines):
            raise CertificateError(f"Arrangement {k}: a line has a = b = 0")
        if any(a1 * b2 == a2 * b1 and a1 * c2 == a2 * c1 and b1 * c2 == b2 * c1
               for (a1, b1, c1), (a2, b2, c2) in itertools.combinations(lines, 2)):
            raise CertificateError(f"Arrangement {k}: two lines are the same")
        if general and not is_general_position(lines):
            raise CertificateError(f"Arrangement {k} is not in general position")
        form = arrangement_type(lines)
        if form in types:
            raise CertificateError(f"Arrangement {k} has the same type as an earlier one")
        types.add(form)


def line_arrangement_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    line_arrangement_witness(params, bound, value, cert, general=False)


def general_line_arrangement_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    line_arrangement_witness(params, bound, value, cert, general=True)


# Keyed by constant group ID.
FAMILIES = {
    "ramsey": Family(
        id_pattern=re.compile(r"ramsey-(?P<r>\d+)-(?P<s>\d+)"),
        lean_module="LeapsInBounds.Statements.Ramsey",
        lean_statement=ramsey_lean_statement,
        check_witness=ramsey_check_witness,
        witness_bound="lower",
    ),
    "van-der-waerden": Family(
        id_pattern=re.compile(r"van-der-waerden-(?P<r>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.VanDerWaerden",
        lean_statement=van_der_waerden_lean_statement,
        check_witness=van_der_waerden_check_witness,
        witness_bound="lower",
    ),
    "cage": Family(
        id_pattern=re.compile(r"cage-(?P<k>\d+)-(?P<g>\d+)"),
        lean_module="LeapsInBounds.Statements.Cage",
        lean_statement=cage_lean_statement,
        check_witness=cage_check_witness,
        witness_bound="upper",
    ),
    "degree-diameter": Family(
        id_pattern=re.compile(r"degree-diameter-(?P<d>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.DegreeDiameter",
        lean_statement=degree_diameter_lean_statement,
        check_witness=degree_diameter_check_witness,
        witness_bound="lower",
    ),
    "minimal-superpermutation": Family(
        id_pattern=re.compile(r"minimal-superpermutation-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Superpermutation",
        lean_statement=superpermutation_lean_statement,
        check_witness=superpermutation_check_witness,
        witness_bound="upper",
    ),
    "kissing-number": Family(
        id_pattern=re.compile(r"kissing-number-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.KissingNumber",
        lean_statement=kissing_number_lean_statement,
        check_witness=kissing_number_check_witness,
        witness_bound="lower",
    ),
    "square-packing": Family(
        id_pattern=re.compile(r"square-packing-in-square-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SquarePacking",
        lean_statement=square_packing_lean_statement,
        check_witness=square_packing_check_witness,
        witness_bound=None,
        values="sqrt",
    ),
    "circle-in-equilateral": Family(
        id_pattern=re.compile(r"circle-in-equilateral-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.CircleInTriangle",
        lean_statement=circle_in_triangle_lean_statement,
        check_witness=circle_in_triangle_check_witness,
        witness_bound="upper",
        values="radical",
    ),
    "schur": Family(
        id_pattern=re.compile(r"schur-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.Schur",
        lean_statement=schur_lean_statement,
        check_witness=schur_check_witness,
        witness_bound="lower",
    ),
    "weak-schur": Family(
        id_pattern=re.compile(r"weak-schur-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.Schur",
        lean_statement=weak_schur_lean_statement,
        check_witness=weak_schur_check_witness,
        witness_bound="lower",
    ),
    "golomb-ruler": Family(
        id_pattern=re.compile(r"golomb-ruler-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Golomb",
        lean_statement=golomb_lean_statement,
        check_witness=golomb_check_witness,
        witness_bound="upper",
    ),
    "snake-in-the-box": Family(
        id_pattern=re.compile(r"snake-in-the-box-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SnakeInTheBox",
        lean_statement=snake_lean_statement,
        check_witness=snake_check_witness,
        witness_bound="lower",
    ),
    "coil-in-the-box": Family(
        id_pattern=re.compile(r"coil-in-the-box-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SnakeInTheBox",
        lean_statement=coil_lean_statement,
        check_witness=coil_check_witness,
        witness_bound="lower",
    ),
    "cap-set": Family(
        id_pattern=re.compile(r"cap-set-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.CapSet",
        lean_statement=cap_set_lean_statement,
        check_witness=cap_set_check_witness,
        witness_bound="lower",
    ),
    "no-three-in-line": Family(
        id_pattern=re.compile(r"no-three-in-line-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.NoThreeInLine",
        lean_statement=no_three_in_line_lean_statement,
        check_witness=no_three_in_line_check_witness,
        witness_bound="lower",
    ),
    "affine-line-arrangements": Family(
        id_pattern=re.compile(r"affine-line-arrangements-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.LineArrangement",
        lean_statement=line_arrangement_lean_statement,
        check_witness=line_arrangement_check_witness,
        witness_bound="lower",
    ),
    "affine-line-arrangements-general-position": Family(
        id_pattern=re.compile(r"affine-line-arrangements-general-position-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.LineArrangement",
        lean_statement=general_line_arrangement_lean_statement,
        check_witness=general_line_arrangement_check_witness,
        witness_bound="lower",
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
            statement = " ".join([entry["statement"], *map(lean_arg, entry["args"])])
            errors[entry["id"]] = f"Theorem {entry['theorem']} does not prove `{statement}`: {failures[entry['id']]}"
    return errors


def lean_arg(arg: int | list[list[int]]) -> str:
    """Write a statement argument as Lean source, for messages."""
    if isinstance(arg, int):
        return str(arg)
    return "[" + ", ".join(f"({c}, {m})" for c, m in arg) + "]"


def check_witness(cert: Mapping[str, Any]) -> None:
    """Verify a witness certificate's evidence."""
    family, params = get_family(cert["constant"])
    if family.witness_bound is not None and cert["bound"] != family.witness_bound:
        raise CertificateError(f"Witnesses for {cert['constant']} can only certify {family.witness_bound} bounds")
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
