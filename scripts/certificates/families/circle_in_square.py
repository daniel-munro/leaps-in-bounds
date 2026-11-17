"""Packing n unit circles in the smallest square."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..geometry import read_points
from ..values import parse_radical, prime_factors
from ..witness import read_witness_data


def circle_in_square_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.CircleInSquare.{name}", [params['n'], terms, d]


def circle_in_square_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    """The side s(n) of the smallest square containing n unit circles with
    disjoint interiors is at most value if there are n centers at distance at
    least 2 from each other, in the square [1, value - 1]².

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
    for i, (x, y) in enumerate(points):
        if any((t - 1).sign() < 0 or (s - t - 1).sign() < 0 for t in (x, y)):
            raise CertificateError(f"Circle {i + 1} is not inside the square")
    for i in range(len(points)):
        for j in range(i):
            dx, dy = points[i][0] - points[j][0], points[i][1] - points[j][1]
            if (dx * dx + dy * dy - 4).sign() < 0:
                raise CertificateError(f"Circles {j + 1} and {i + 1} overlap")


FAMILIES = {
    "circle-in-square": Family(
        id_pattern=re.compile(r"circle-in-square-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.CircleInSquare",
        lean_statement=circle_in_square_lean_statement,
        check_witness=circle_in_square_check_witness,
        witness_bound="upper",
        values="radical",
    ),
}
