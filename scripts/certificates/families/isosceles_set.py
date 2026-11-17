"""Isosceles sets: points in R^n with every three forming an isosceles triangle."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..values import Radical, parse_radical
from ..witness import read_witness_data


def isosceles_set_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.IsoscelesSet.{name}", [params['n'], value]


def read_radical_points(data: str) -> list[tuple[Radical, ...]]:
    """Parse points, one per line, with coordinates separated by commas and
    read by parse_radical."""
    points = []
    for line in data.strip().splitlines():
        if line.strip():
            points.append(tuple(parse_radical(c.strip()) for c in line.split(",")))
    if len({len(p) for p in points}) > 1:
        raise CertificateError("All points must have the same number of coordinates")
    return points


def affine_dimension(points: list[tuple[Radical, ...]]) -> int:
    """The dimension of the affine subspace spanned by the points, by exact
    Gaussian elimination on their differences from the first."""
    rows = [[a - b for a, b in zip(p, points[0])] for p in points[1:]]
    rank, cols = 0, len(points[0]) if points else 0
    for col in range(cols):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col].terms), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = rows[rank][col].inverse()
        rows[rank] = [x * inv for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col].terms:
                f = rows[r][col]
                rows[r] = [x - f * y for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def is_isosceles_set(points: list[tuple[Radical, ...]]) -> bool:
    """Check that the points are distinct and every three of them form an
    isosceles triangle: two of its sides have the same length. Squared
    distances are compared exactly."""
    n = len(points)
    dist = [[sum(((a - b) * (a - b) for a, b in zip(p, q)), Radical()) for q in points] for p in points]
    if any(not dist[i][j].terms for i in range(n) for j in range(i + 1, n)):
        return False
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                a, b, c = dist[i][j], dist[i][k], dist[j][k]
                if a != b and a != c and b != c:
                    return False
    return True


def isosceles_set_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """A lower bound on the largest isosceles set in E^n is witnessed by that
    many points in some Euclidean space, spanning an affine subspace of
    dimension at most n, any three of which form an isosceles triangle."""
    if bound != "lower":
        raise CertificateError("Isosceles set witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "points":
        raise CertificateError("Isosceles set witnesses must use format: points")
    points = read_radical_points(read_witness_data(cert))
    if len(points) != value:
        raise CertificateError(f"Witness has {len(points)} points, but a lower bound of {value} needs {value}")
    if affine_dimension(points) > params["n"]:
        raise CertificateError(f"Points span more than {params['n']} dimensions")
    if not is_isosceles_set(points):
        raise CertificateError("Points aren't distinct, or three of them form a triangle with three different sides")


FAMILIES = {
    "isosceles-set": Family(
        id_pattern=re.compile(r"isosceles-set-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.IsoscelesSet",
        lean_statement=isosceles_set_lean_statement,
        check_witness=isosceles_set_check_witness,
        witness_bound="lower",
    ),
}
