"""The no-three-in-line problem."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..geometry import no_three_collinear
from ..witness import read_witness_data


def no_three_in_line_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.NoThreeInLine.{name}", [params['n'], value]


def read_grid_points(data: str) -> list[tuple[int, int]]:
    """Parse grid points `x,y`: two natural numbers joined by a comma, the
    points separated by whitespace."""
    points = []
    for word in data.split():
        match = re.fullmatch(r"(\d+),(\d+)", word)
        if not match:
            raise CertificateError(f"Points must be written x,y, not {word[:40]!r}")
        points.append((int(match.group(1)), int(match.group(2))))
    return points


def no_three_in_line_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """D(n) >= value is witnessed by value points of the n x n grid with no
    three on a line."""
    if bound != "lower":
        raise CertificateError("No-three-in-line witnesses can only certify lower bounds")
    if cert["witness"].get("format") != "points":
        raise CertificateError("No-three-in-line witnesses must use format: points")
    n = params["n"]
    points = read_grid_points(read_witness_data(cert))
    if len(points) != value:
        raise CertificateError(f"Witness has {len(points)} points, but a lower bound of {value} needs {value}")
    if not all(x < n and y < n for x, y in points):
        raise CertificateError(f"Points must have coordinates from 0 to {n - 1}")
    if not no_three_collinear(points):
        raise CertificateError("Points aren't distinct, or three of them are on a line")


FAMILIES = {
    "no-three-in-line": Family(
        id_pattern=re.compile(r"no-three-in-line-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.NoThreeInLine",
        lean_statement=no_three_in_line_lean_statement,
        check_witness=no_three_in_line_check_witness,
        witness_bound="lower",
    ),
}
