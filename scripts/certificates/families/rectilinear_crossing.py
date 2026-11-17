"""The rectilinear crossing number of complete graphs."""

import itertools
import math
import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..geometry import no_three_collinear
from ..witness import read_witness_data


def rectilinear_crossing_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.RectilinearCrossing.{name}", [params['n'], value]


def read_integer_points(data: str) -> list[tuple[int, int]]:
    """Parse points `x,y` of the integer grid: two integers joined by a comma,
    the points separated by whitespace."""
    points = []
    for word in data.split():
        match = re.fullmatch(r"(-?\d+),(-?\d+)", word)
        if not match:
            raise CertificateError(f"Points must be written x,y with integers x and y, not {word[:40]!r}")
        points.append((int(match.group(1)), int(match.group(2))))
    return points


def orientation(p: tuple[int, int], q: tuple[int, int], r: tuple[int, int]) -> int:
    """Twice the signed area of the triangle pqr: positive if it turns left."""
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])


def rectilinear_crossings(points: list[tuple[int, int]]) -> int:
    """The number of crossings in the straight-line drawing of the complete
    graph on points in general position. Two edges cross exactly when their
    four ends are in convex position, and four points in general position
    aren't in convex position exactly when one is inside the triangle of the
    other three, so this is C(n, 4) minus the number of pairs of a triangle
    and a point inside it."""
    n = len(points)
    inside = 0
    for i, j, k in itertools.combinations(range(n), 3):
        p, q, r = points[i], points[j], points[k]
        if orientation(p, q, r) < 0:
            q, r = r, q
        inside += sum(1 for s in points
                      if orientation(p, q, s) > 0 and orientation(q, r, s) > 0 and orientation(r, p, s) > 0)
    return math.comb(n, 4) - inside


def rectilinear_crossing_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """cr(K_n) <= value is witnessed by n integer points, no three on a line,
    whose straight-line drawing of K_n has at most value crossings."""
    if bound != "upper":
        raise CertificateError("Rectilinear crossing number witnesses can only certify upper bounds")
    if cert["witness"].get("format") != "points":
        raise CertificateError("Rectilinear crossing number witnesses must use format: points")
    n = params["n"]
    points = read_integer_points(read_witness_data(cert))
    if len(points) != n:
        raise CertificateError(f"Witness has {len(points)} points, but K_{n} needs {n}")
    if not no_three_collinear(points):
        raise CertificateError("Points aren't distinct, or three of them are on a line")
    crossings = rectilinear_crossings(points)
    if crossings > value:
        raise CertificateError(f"Drawing has {crossings} crossings, more than {value}")


FAMILIES = {
    "rectilinear-crossing": Family(
        id_pattern=re.compile(r"rectilinear-crossing-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.RectilinearCrossing",
        lean_statement=rectilinear_crossing_lean_statement,
        check_witness=rectilinear_crossing_check_witness,
        witness_bound="upper",
    ),
}
