"""The Heilbronn triangle problem: n points in a square or triangle, with the
smallest triangle they form as large as possible."""

import itertools
import re
from typing import Any, Callable, Mapping

from ..errors import CertificateError
from ..family import Family
from ..geometry import read_points
from ..values import Radical, parse_radical
from ..witness import read_witness_data


def heilbronn_lean_statement(region: str) -> Callable[[Mapping[str, int], str, int | str], tuple[str, list[Any]]]:
    def statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
        name = f"{region}RadicalLowerBound" if bound == "lower" else f"{region}RadicalUpperBound"
        terms, d = parse_radical(value).lean_args()
        return f"LeapsInBounds.Heilbronn.{name}", [params['n'], terms, d]
    return statement


def in_square(x: Radical, y: Radical) -> bool:
    return all(t.sign() >= 0 and (1 - t).sign() >= 0 for t in (x, y))


def in_triangle(x: Radical, y: Radical) -> bool:
    return x.sign() >= 0 and y.sign() >= 0 and (1 - x - y).sign() >= 0


def heilbronn_check_witness(region: str) -> Callable[[Mapping[str, int], str, int | str, Mapping[str, Any]], None]:
    """H(n) >= a (in the square) or Δ(n) >= a (in the triangle) is witnessed by
    n points in the region, each three forming a triangle of area at least a,
    or, in the triangle, a times its area 1/2.

    The square is [0, 1]², and the triangle has vertices (0, 0), (1, 0) and
    (0, 1). Twice the area of each triangle is the absolute value of a
    determinant, so with rational coordinates (decimals or fractions) the
    comparisons are exact. Coordinates with square roots are also accepted, but
    are slower.
    """
    inside = in_square if region == "Square" else in_triangle
    # The bound on twice the area of each triangle
    scale = 2 if region == "Square" else 1

    def check(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
        if cert["witness"].get("format") != "points":
            raise CertificateError("Heilbronn witnesses must use format: points")
        a = parse_radical(value)
        points = read_points(read_witness_data(cert))
        if len(points) != params["n"]:
            raise CertificateError(f"Witness has {len(points)} points, not {params['n']}")
        for i, (x, y) in enumerate(points):
            if not inside(x, y):
                raise CertificateError(f"Point {i + 1} is not in the {region.lower()}")
        rational = all(set(t.terms) <= {1} for p in points for t in p)
        if rational:
            pts = [(x.terms.get(1, 0), y.terms.get(1, 0)) for x, y in points]
        else:
            pts = points
        threshold = a * scale
        least = threshold.terms.get(1, 0) if set(threshold.terms) <= {1} else None
        for (i, p), (j, q), (k, r) in itertools.combinations(enumerate(pts), 3):
            det = (q[0] - p[0]) * (r[1] - p[1]) - (r[0] - p[0]) * (q[1] - p[1])
            if least is not None and rational:
                ok = abs(det) >= least
            else:
                d = det if isinstance(det, Radical) else Radical({1: det})
                if d.sign() < 0:
                    d = -d
                ok = (d - threshold).sign() >= 0
            if not ok:
                raise CertificateError(f"Points {i + 1}, {j + 1} and {k + 1} form a triangle of area less than {value}"
                                       + ("" if region == "Square" else " times the area of the region"))

    return check


FAMILIES = {
    "heilbronn-square": Family(
        id_pattern=re.compile(r"heilbronn-square-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Heilbronn",
        lean_statement=heilbronn_lean_statement("Square"),
        check_witness=heilbronn_check_witness("Square"),
        witness_bound="lower",
        values="radical",
    ),
    "heilbronn-triangle": Family(
        id_pattern=re.compile(r"heilbronn-triangle-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Heilbronn",
        lean_statement=heilbronn_lean_statement("Triangle"),
        check_witness=heilbronn_check_witness("Triangle"),
        witness_bound="lower",
        values="radical",
    ),
}
