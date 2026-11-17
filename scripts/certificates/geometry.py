"""Points in the plane, shared by several families."""

import math

from .errors import CertificateError
from .values import Radical, parse_radical


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
