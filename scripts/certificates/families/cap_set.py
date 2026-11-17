"""Cap sets in F_3^n."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


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


FAMILIES = {
    "cap-set": Family(
        id_pattern=re.compile(r"cap-set-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.CapSet",
        lean_statement=cap_set_lean_statement,
        check_witness=cap_set_check_witness,
        witness_bound="lower",
    ),
}
