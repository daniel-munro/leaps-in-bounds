"""Arrangements of lines in the plane, and those in general position."""

import hashlib
import itertools
import math
import re
from fractions import Fraction
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..streaming import count_distinct, map_batches
from ..witness import witness_lines


def line_arrangement_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.LineArrangement.{name}", [params['n'], value]


def general_line_arrangement_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "GeneralLowerBound" if bound == "lower" else "GeneralUpperBound"
    return f"LeapsInBounds.LineArrangement.{name}", [params['n'], value]


Line = tuple[int, int, int]
Point = tuple[Fraction, Fraction]


def parse_arrangement(row: str, n: int) -> list[Line]:
    """Parse an arrangement from a line of text: 3n integers, with a, b, c for
    each line a x + b y = c."""
    try:
        values = [int(x) for x in row.split()]
    except ValueError:
        raise CertificateError("Line coefficients must be integers")
    if len(values) != 3 * n:
        raise CertificateError(f"Each arrangement needs {3 * n} integers, found {len(values)}")
    return [tuple(values[3 * i:3 * i + 3]) for i in range(n)]


def read_arrangements(data: str, n: int) -> list[list[Line]]:
    """Parse arrangements, one per line of text (see parse_arrangement)."""
    return [parse_arrangement(row, n) for row in data.splitlines() if row.strip()]


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


def general_line_ends(lines: list[Line]) -> list[tuple[int, tuple[int, int]]]:
    """line_ends, for lines no two of which are parallel, sorted by angle with
    floats and then checked exactly: much faster."""
    ends = []
    for i, (a, b, _) in enumerate(lines):
        for x, y in ((-b, a), (b, -a)):
            # Angles in [0, pi), then in [pi, 2 pi), each measured within its half
            if y > 0 or (y == 0 and x > 0):
                ends.append((0, math.atan2(y, x), i, (x, y)))
            else:
                ends.append((1, math.atan2(-y, -x), i, (x, y)))
    ends.sort()
    # Each end must come strictly after the one before, counterclockwise: in
    # a later half, or in the same half and to the left of it
    for (h1, _, _, (x1, y1)), (h2, _, _, (x2, y2)) in zip(ends, ends[1:]):
        if h1 == h2 and x1 * y2 - y1 * x2 <= 0:
            return line_ends(lines)
    return [(i, u) for _, _, i, u in ends]


def crossing_order(lines: list[Line], i: int) -> list[int] | None:
    """The other lines in the order they cross line i, toward its end in
    direction (-b, a), or None if two of them cross it at the same point or
    one is parallel to it. Sorted with floats, then checked exactly."""
    a1, b1, c1 = lines[i]
    positions = []
    for j, (a2, b2, c2) in enumerate(lines):
        if j == i:
            continue
        det = a1 * b2 - a2 * b1
        if det == 0:
            return None
        # The crossing point is (x, y) / det; its position along line i,
        # toward (-b1, a1), is its dot product with that direction, num / det
        num = -(c1 * b2 - c2 * b1) * b1 + (a1 * c2 - a2 * c1) * a1
        if det < 0:
            num, det = -num, -det
        positions.append((num / det, num, det, j))
    positions.sort()
    if any(n1 * d2 >= n2 * d1 for (_, n1, d1, _), (_, n2, d2, _) in zip(positions, positions[1:])):
        # Floats too close to sort by: sort exactly
        positions.sort(key=lambda p: Fraction(p[1], p[2]))
        if any(n1 * d2 == n2 * d1 for (_, n1, d1, _), (_, n2, d2, _) in zip(positions, positions[1:])):
            return None  # three lines through a point
    return [j for _, _, _, j in positions]


def general_arrangement_type(lines: list[Line]) -> bytes | tuple[int, ...] | None:
    """A canonical form of the combinatorial type of an arrangement in general
    position, or None if it isn't in general position. Much faster than
    arrangement_type, which it agrees with on whether two arrangements in
    general position have the same type.

    Walk around the ends of the lines as in arrangement_type, numbering the
    lines in the order the walk first meets them. For each line in that order,
    list the numbers of the other lines in the order they cross it, starting
    from the end the walk met first. The form is the smallest such list over
    the start and direction of the walk.

    An equivalence of two arrangements takes the ends in order around a large
    circle to the ends in the same or the opposite order, and the order of the
    crossings along each line to the order along its image. So equivalent
    arrangements get the same form, and arrangements with different forms are
    inequivalent. (For arrangements in general position, the converse holds
    too, but it isn't needed: a lower bound only needs different forms to mean
    different types.)

    This follows the canonical form in the checker that Sami Hani Badaoui and
    Sarah Ellen Mary Vaughan wrote for ten-line arrangements (pull request #85).
    """
    n = len(lines)
    # crossings[(i, u)]: the other lines in the order they cross line i,
    # starting from its end in direction u
    crossings = {}
    for i, (a, b, _) in enumerate(lines):
        order = crossing_order(lines, i)
        if order is None:
            return None
        # The order runs toward (-b, a), so it starts from the other end
        crossings[(i, (b, -a))] = order
        crossings[(i, (-b, a))] = order[::-1]
    ends = general_line_ends(lines)
    if n <= 256 and all(ends[k][0] == ends[k + n][0] for k in range(n)):
        # No two lines are parallel, so the two ends of each line are n apart
        # in the walk, which meets every line in its first n steps. Renumber
        # the lines with a translation table.
        cross = [(i, bytes(crossings[(i, u)])) for i, u in ends]
        cross = cross + cross
        best = None
        for start in range(2 * n):
            for walk in (cross[start:start + n], cross[start + n + 1:start + 2 * n + 1][::-1]):
                table = bytearray(256)
                for k, (i, _) in enumerate(walk):
                    table[i] = k
                form = b"".join([order for _, order in walk]).translate(table)
                if best is None or form < best:
                    best = form
        return best
    best = None
    for start in range(2 * n):
        for direction in (1, -1):
            number = [-1] * n
            first_end = []
            for t in range(2 * n):
                i, u = ends[(start + direction * t) % (2 * n)]
                if number[i] < 0:
                    number[i] = len(first_end)
                    first_end.append((i, u))
            form = tuple(number[j] for end in first_end for j in crossings[end])
            if best is None or form < best:
                best = form
    return best


# Arrangements checked per batch. A witness with more than one batch is checked
# in parallel, in processes that each check a batch at a time.
BATCH_ROWS = 10_000


def type_digests(rows: list[str], n: int, general: bool, first: int) -> bytes:
    """Check a batch of arrangements, given as text and numbered from first,
    and return an 8-byte hash of the canonical form of each one's type."""
    digests = bytearray()
    for k, row in enumerate(rows, first):
        try:
            lines = parse_arrangement(row, n)
        except CertificateError as e:
            raise CertificateError(f"Arrangement {k}: {e}")
        if any(a == 0 and b == 0 for a, b, _ in lines):
            raise CertificateError(f"Arrangement {k}: a line has a = b = 0")
        # Equivalence preserves general position, since two lines meet when
        # some covector is 0 on both, and three lines meet at a point when some
        # covector is 0 on all three. So forms of the two kinds never need
        # comparing with each other.
        form = general_arrangement_type(lines)
        if form is not None:
            key = b"g" + (form if isinstance(form, bytes) else repr(form).encode())
        else:
            if general:
                raise CertificateError(f"Arrangement {k} is not in general position")
            if any(a1 * b2 == a2 * b1 and a1 * c2 == a2 * c1 and b1 * c2 == b2 * c1
                   for (a1, b1, c1), (a2, b2, c2) in itertools.combinations(lines, 2)):
                raise CertificateError(f"Arrangement {k}: two lines are the same")
            key = b"c" + repr(arrangement_type(lines)).encode()
        digests += hashlib.blake2b(key, digest_size=8).digest()
    return bytes(digests)


def line_arrangement_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], general: bool) -> None:
    """There are at least `value` types of arrangements of n lines (in general
    position) when the witness has arrangements of at least `value` types.
    Arrangements of the same type can repeat, which helps a generator that
    samples arrangements at random.

    Types are compared by an 8-byte hash of their canonical forms. Different
    hashes mean different forms, and so inequivalent arrangements. Two types
    can share a hash, which only undercounts them, so the count is still a
    lower bound on the number of types. For a few million types, the chance
    that any two share one is tiny anyway."""
    if cert["witness"].get("format") != "lines":
        raise CertificateError("Line arrangement witnesses must use format: lines")
    n = params["n"]
    total, distinct = count_distinct(map_batches(type_digests, witness_lines(cert), BATCH_ROWS, n, general))
    if distinct < value:
        raise CertificateError(f"Witness has {total} arrangements of {distinct} distinct types, fewer than {value}")


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
