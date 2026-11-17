"""Optimal Golomb rulers."""

import itertools
import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


def golomb_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Golomb.{name}", [params['n'], value]


def read_marks(data: str) -> list[int]:
    """Parse marks: integers separated by whitespace or commas."""
    try:
        return [int(x) for x in data.replace(",", " ").split()]
    except ValueError:
        raise CertificateError("Marks must be integers")


def golomb_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """G(n) <= value is witnessed by n distinct marks in 0, ..., value whose
    pairwise differences are distinct."""
    if cert["witness"].get("format") != "marks":
        raise CertificateError("Golomb ruler witnesses must use format: marks")
    marks = read_marks(read_witness_data(cert))
    if len(set(marks)) != len(marks):
        raise CertificateError("Marks must be distinct")
    if len(marks) != params["n"]:
        raise CertificateError(f"Ruler has {len(marks)} marks, not {params['n']}")
    if any(not 0 <= a <= value for a in marks):
        raise CertificateError(f"Marks must be between 0 and {value}")
    differences = [b - a for a, b in itertools.combinations(sorted(marks), 2)]
    if len(set(differences)) != len(differences):
        raise CertificateError("Two pairs of marks are the same distance apart")


FAMILIES = {
    "golomb-ruler": Family(
        id_pattern=re.compile(r"golomb-ruler-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Golomb",
        lean_statement=golomb_lean_statement,
        check_witness=golomb_check_witness,
        witness_bound="upper",
    ),
}
