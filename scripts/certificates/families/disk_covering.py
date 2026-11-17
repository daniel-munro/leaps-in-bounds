"""Covering a disk with n equal smaller disks."""

import math
import re
from fractions import Fraction
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..geometry import read_points
from ..values import parse_radical
from ..witness import read_witness_data


def disk_covering_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.DiskCovering.{name}", [params['n'], terms, d]


# Bounds the work of checking a covering, which grows with the precision needed
# near the points it covers most tightly.
MAX_COVERING_SQUARES = 2_000_000
MAX_COVERING_DEPTH = 60


def disk_covering_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    """r(n) <= value is witnessed by n centers such that the closed disks of
    radius value around them cover the closed unit disk.

    The checker covers the square [-1, 1]² with squares, splitting each one
    into four until it misses the unit disk or lies in one of the disks, all
    with exact rational arithmetic. This always finishes when the disks cover
    the unit disk with a little room to spare, but not when they cover it only
    just, as at the points where an optimal covering is tight: for those, the
    radius has to be rounded up.
    """
    if cert["witness"].get("format") != "points":
        raise CertificateError("Disk covering witnesses must use format: points")
    r_squared = parse_radical(value) * parse_radical(value)
    if set(r_squared.terms) - {1} or parse_radical(value).sign() <= 0:
        raise CertificateError("The radius must be positive with a rational square")
    r2 = r_squared.terms.get(1, Fraction(0))
    centers = []
    for x, y in read_points(read_witness_data(cert)):
        if set(x.terms) - {1} or set(y.terms) - {1}:
            raise CertificateError("Centers must have rational coordinates")
        centers.append((x.terms.get(1, Fraction(0)), y.terms.get(1, Fraction(0))))
    if len(centers) != params["n"]:
        raise CertificateError(f"Witness has {len(centers)} centers, not {params['n']}")
    # Scale by the common denominator so the arithmetic is on integers: a square
    # at depth k has side 2^(D - k + 1) and the unit disk has radius 2^D, so
    # centers and the radius are scaled by 2^D too.
    D = MAX_COVERING_DEPTH
    scale = 1 << D
    denominator = math.lcm(*(c.denominator for x, y in centers for c in (x, y)), r2.denominator)
    # Exact comparisons of squared distances, with everything multiplied by
    # denominator² (and the radius² by denominator): a center (x, y) becomes
    # (x · denominator · 2^D), while square corners are multiplied by denominator.
    big = [(int(x * denominator) * scale, int(y * denominator) * scale) for x, y in centers]
    big_r2 = int(r2 * denominator) * denominator * scale * scale
    unit2 = denominator * denominator * scale * scale

    def dist2_range(cx: int, cy: int, x0: int, y0: int, side: int) -> tuple[int, int]:
        # Least and greatest squared distance from (cx, cy) to the square
        dx_near = max(x0 - cx, 0, cx - x0 - side)
        dy_near = max(y0 - cy, 0, cy - y0 - side)
        dx_far = max(abs(cx - x0), abs(cx - x0 - side))
        dy_far = max(abs(cy - y0), abs(cy - y0 - side))
        return dx_near * dx_near + dy_near * dy_near, dx_far * dx_far + dy_far * dy_far

    stack = [(-scale * denominator, -scale * denominator, 2 * scale * denominator, 0)]
    squares = 0
    while stack:
        x0, y0, side, depth = stack.pop()
        squares += 1
        if squares > MAX_COVERING_SQUARES:
            raise CertificateError(f"Checking the covering needs more than {MAX_COVERING_SQUARES} squares: the disks don't cover the unit disk, or only just (try rounding the radius up)")
        if dist2_range(0, 0, x0, y0, side)[0] > unit2:
            continue
        if any(dist2_range(cx, cy, x0, y0, side)[1] <= big_r2 for cx, cy in big):
            continue
        if depth == D:
            raise CertificateError(f"The disks don't cover the unit disk near ({x0 / (scale * denominator):.6f}, {y0 / (scale * denominator):.6f}), or only just (try rounding the radius up)")
        half = side // 2
        for dx in (0, half):
            for dy in (0, half):
                stack.append((x0 + dx, y0 + dy, half, depth + 1))


FAMILIES = {
    "disk-covering": Family(
        id_pattern=re.compile(r"disk-covering-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.DiskCovering",
        lean_statement=disk_covering_lean_statement,
        check_witness=disk_covering_check_witness,
        witness_bound="upper",
        values="radical",
    ),
}
