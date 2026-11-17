"""The Tammes problem: n points on the sphere as far apart as possible."""

import re
from fractions import Fraction
from typing import Any, Mapping

import mpmath

from ..errors import CertificateError
from ..family import Family
from ..values import parse_radical
from ..witness import read_witness_data


def tammes_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.Tammes.{name}", [params['n'], terms, d]


def read_rational_vectors(data: str) -> list[tuple[Fraction, Fraction, Fraction]]:
    """Parse vectors `x, y, z`, one per line, with rational coordinates
    (integers, decimals or fractions `a/b`)."""
    vectors = []
    for line in data.splitlines():
        if not line.strip():
            continue
        coords = line.split(",")
        if len(coords) != 3:
            raise CertificateError(f"Expected a vector 'x, y, z', not {line.strip()!r}")
        try:
            vectors.append(tuple(Fraction(c.strip()) for c in coords))
        except (ValueError, ZeroDivisionError):
            raise CertificateError(f"Coordinates must be rational, not {line.strip()!r}")
    return vectors


# cos(a°) for the rational a where it's rational (Niven's theorem), so those
# bounds, which optimal configurations attain, are decided exactly
EXACT_COSINES = {Fraction(0): Fraction(1), Fraction(60): Fraction(1, 2), Fraction(90): Fraction(0),
                 Fraction(120): Fraction(-1, 2), Fraction(180): Fraction(-1)}


def cosine_interval(a: Fraction) -> tuple[Fraction, Fraction]:
    """Rational bounds lo <= cos(a°) <= hi, exact where cos(a°) is rational,
    from mpmath's interval arithmetic."""
    if a in EXACT_COSINES:
        return EXACT_COSINES[a], EXACT_COSINES[a]
    iv = mpmath.iv
    prec, iv.prec = iv.prec, 256
    try:
        c = iv.cos(iv.pi * iv.mpf(a.numerator) / iv.mpf(a.denominator * 180))
        return _fraction(c.a), _fraction(c.b)
    finally:
        iv.prec = prec


def _fraction(x: Any) -> Fraction:
    """An endpoint of an mpmath interval, a binary float, as a Fraction."""
    sign, man, exp, _ = mpmath.mpf(x._mpi_[0] if hasattr(x, "_mpi_") else x)._mpf_
    value = Fraction(man) * Fraction(2) ** exp
    return -value if sign else value


def cosine_at_most(dot: Fraction, norms: Fraction, c: Fraction) -> bool:
    """Whether dot / sqrt(norms) <= c, exactly, for norms > 0."""
    if c >= 0:
        return dot <= 0 or dot * dot <= c * c * norms
    return dot < 0 and dot * dot >= c * c * norms


def tammes_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    """T(n) >= a (in degrees) is witnessed by n nonzero vectors in ℝ³, each two
    at an angle of at least a degrees: scaled to unit length, they're points on
    the sphere that far apart.

    Vectors have rational coordinates and needn't have unit length, so the
    cosine of the angle between u and v is u·v / √(|u|²|v|²), compared exactly
    with rational bounds on cos(a°) for a rational. Where cos(a°) is irrational,
    a configuration that attains the angle exactly can't be decided this way,
    so the bound has to be rounded down a little.
    """
    if cert["witness"].get("format") != "vectors":
        raise CertificateError("Tammes witnesses must use format: vectors")
    a = parse_radical(value)
    if set(a.terms) - {1}:
        raise CertificateError("The angle must be a rational number of degrees")
    a = a.terms.get(1, Fraction(0))
    if not 0 <= a <= 180:
        raise CertificateError("The angle must be between 0 and 180 degrees")
    vectors = read_rational_vectors(read_witness_data(cert))
    if len(vectors) != params["n"]:
        raise CertificateError(f"Witness has {len(vectors)} vectors, not {params['n']}")
    norms = [sum(c * c for c in v) for v in vectors]
    if any(m == 0 for m in norms):
        raise CertificateError("Vectors must be nonzero")
    lo, hi = cosine_interval(a)
    for i in range(len(vectors)):
        for j in range(i):
            dot = sum(x * y for x, y in zip(vectors[i], vectors[j]))
            if cosine_at_most(dot, norms[i] * norms[j], lo):
                continue
            if not cosine_at_most(dot, norms[i] * norms[j], hi):
                raise CertificateError(f"Vectors {j + 1} and {i + 1} are less than {value} degrees apart")
            raise CertificateError(f"Vectors {j + 1} and {i + 1} are too close to {value} degrees apart to decide (try rounding the angle down)")


FAMILIES = {
    "tammes": Family(
        id_pattern=re.compile(r"tammes-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Tammes",
        lean_statement=tammes_lean_statement,
        check_witness=tammes_check_witness,
        witness_bound="lower",
        values="radical",
    ),
}
