"""Print COUNT arrangements of N lines of pairwise different combinatorial
types, one per row as 3N integers a b c, one triple per line a x + b y = c.

GENERAL of them are in general position: random lines with small coefficients.
The other COUNT - GENERAL are not: random lines through two points of a small
grid, which are often parallel or meet three or more at a point.

Types are told apart by a canonical form that is the same for arrangements of
the same type (see form() below), and an arrangement is printed only if its
form is new. The form may also be the same for some arrangements of different
types, which only means that fewer types are found per draw: the checker
decides which arrangements are of different types, not this program.

Deterministic: the random numbers are seeded, and nothing depends on the
machine or the order of iteration over a set.
"""

import math
import random
import sys
from fractions import Fraction

N = 10
COUNT = 700000
GENERAL = 700000
SEED = 1


def vertices(lines, i):
    """The vertices on line i, in order toward its end in direction (-b, a),
    that is, from its end in direction (b, -a), each as the tuple of the other lines through it; or None if two lines are
    the same."""
    a1, b1, c1 = lines[i]
    crossings = []
    for j, (a2, b2, c2) in enumerate(lines):
        if j == i:
            continue
        det = a1 * b2 - a2 * b1
        if det == 0:
            if a1 * c2 == a2 * c1 and b1 * c2 == b2 * c1:
                return None
            continue
        # The crossing is (x, y) / det, at position p / det along (-b1, a1)
        x, y = c1 * b2 - c2 * b1, a1 * c2 - a2 * c1
        p = a1 * y - b1 * x
        if det < 0:
            p, det = -p, -det
        crossings.append((p / det, p, det, j))
    # Sort by floating point, which orders these small fractions correctly,
    # then group crossings at the same point and check the order exactly
    crossings.sort()
    groups = []
    last = None
    for _, p, d, j in crossings:
        if last is not None:
            lp, ld = last
            if p * ld == lp * d:
                groups[-1].append(j)
                continue
            if p * ld < lp * d:
                raise AssertionError("floating point misordered the crossings")
        groups.append([j])
        last = (p, d)
    return [tuple(g) for g in groups]


def ends(lines):
    """The 2N ends of the lines, in counterclockwise order around a large
    circle, as (i, u) for the end of line i in direction u. The same order as
    line_ends in scripts/certificates/families/line_arrangement.py."""
    def key(end):
        i, (x, y) = end
        a, b, c = lines[i]
        g = math.gcd(x, y)
        x, y = x // g, y // g
        half = 0 if y > 0 or (y == 0 and x > 0) else 1
        angle = (0, 0) if y == 0 else (1, Fraction(-x, y))
        offset = Fraction(c * (-a * y + b * x), a * a + b * b)
        return half, angle, offset
    result = [(i, u) for i, (a, b, _) in enumerate(lines) for u in ((-b, a), (b, -a))]
    result.sort(key=key)
    return result


def general_ends(lines):
    """The same, for lines of which no two are parallel, so that the ends can
    be ordered by the angle of their directions alone, which floating point
    does correctly for small integers."""
    def key(end):
        x, y = end[1]
        half = 0 if y > 0 or (y == 0 and x > 0) else 1
        return (half, 0, 0.0) if y == 0 else (half, 1, -x / y)
    result = [(i, u) for i, (a, b, _) in enumerate(lines) for u in ((-b, a), (b, -a))]
    result.sort(key=key)
    return result


def form(lines):
    """A canonical form of the type of an arrangement, and whether it's in
    general position; or None if two of its lines are the same.

    Walk around the ends of the lines, numbering the lines in the order the
    walk first meets them. For each line in that order, list its vertices in
    order from the end the walk met first, each as the numbers of the other
    lines through it. The form is the smallest such list over the start and
    direction of the walk.

    An equivalence of two arrangements takes the ends in order around a large
    circle to the ends in the same or the opposite order, the lines through
    each vertex to the lines through its image, and the order of the vertices
    along each line to the order along its image. So arrangements of the same
    type get the same form. (In general position, this is the form that the
    checker uses, general_arrangement_type.)"""
    n = len(lines)
    from_end = {}
    is_general = True
    for i, (a, b, _) in enumerate(lines):
        vs = vertices(lines, i)
        if vs is None:
            return None
        if len(vs) < n - 1:
            is_general = False
        # from_end[(i, u)]: the vertices of line i, from its end in direction u
        from_end[(i, (b, -a))] = vs
        from_end[(i, (-b, a))] = vs[::-1]
    best = None
    if is_general:
        # Any n ends in a row are one end of each line
        order = general_ends(lines)
        crossings = [bytes(j for (j,) in from_end[end]) for end in order]
        line_of = [i for i, _ in order]
        for start in range(2 * n):
            for step in (1, -1):
                walk = [(start + step * t) % (2 * n) for t in range(n)]
                table = bytearray(256)
                for k, e in enumerate(walk):
                    table[line_of[e]] = k
                f = b"".join([crossings[e] for e in walk]).translate(table)
                if best is None or f < best:
                    best = f
        return best, True
    order = ends(lines)
    for start in range(2 * n):
        for step in (1, -1):
            number = [-1] * n
            first = []
            for t in range(2 * n):
                end = order[(start + step * t) % (2 * n)]
                if number[end[0]] < 0:
                    number[end[0]] = len(first)
                    first.append(end)
            f = tuple(tuple(tuple(sorted(number[j] for j in v)) for v in from_end[end]) for end in first)
            if best is None or f < best:
                best = f
    return best, False


def general_draw(rng):
    """N random lines with small coefficients, no two parallel: a and b of
    absolute value at most r, and c at most 2 r. Small r reaches more of the
    types with few lines, and larger r makes three lines through a point
    rarer."""
    r = rng.randrange(3, 10) if N <= 8 else rng.randrange(N - 3, N + 1)
    lines = []
    while len(lines) < N:
        a, b, c = rng.randrange(-r, r + 1), rng.randrange(-r, r + 1), rng.randrange(-2 * r, 2 * r + 1)
        if (a or b) and all(a * b2 != a2 * b for a2, b2, _ in lines):
            lines.append((a, b, c))
    return lines


def grid_draw(rng):
    """N random lines through two points of a k x k grid, k from 3 to 6."""
    k = rng.randrange(3, 7)
    lines = []
    while len(lines) < N:
        x1, y1, x2, y2 = (rng.randrange(k) for _ in range(4))
        if (x1, y1) != (x2, y2):
            a, b = y2 - y1, x1 - x2
            lines.append((a, b, a * x1 + b * y1))
    return lines


def main():
    rng = random.Random(SEED)
    seen = set()
    wanted = {True: GENERAL, False: COUNT - GENERAL}
    found = {True: 0, False: 0}
    while found[True] < wanted[True] or found[False] < wanted[False]:
        # Draw the kind that is further behind, as a fraction of what's wanted
        kind = found[True] * wanted[False] <= found[False] * wanted[True]
        if found[kind] >= wanted[kind]:
            kind = not kind
        lines = general_draw(rng) if kind else grid_draw(rng)
        result = form(lines)
        if result is None or result[1] != kind or result[0] in seen:
            continue
        seen.add(result[0])
        found[kind] += 1
        sys.stdout.write(" ".join(str(x) for line in lines for x in line) + "\n")


main()
