"""Arrangements of lines in the plane, and those in general position."""

import itertools
import math
import re
from fractions import Fraction
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


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


FAMILIES = {
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
