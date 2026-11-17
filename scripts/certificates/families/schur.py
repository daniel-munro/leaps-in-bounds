"""Schur numbers and weak Schur numbers."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..graphs import bits
from ..witness import read_coloring


def schur_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Schur.{name}", [params['k'], value]


def weak_schur_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "WeakLowerBound" if bound == "lower" else "WeakUpperBound"
    return f"LeapsInBounds.Schur.{name}", [params['k'], value]


def has_monochromatic_sum(colors: str, weak: bool = False) -> bool:
    """Check whether a coloring of 1, ..., n (one character per integer) has
    a monochromatic solution to x + y = z, with x ≠ y if weak."""
    for color in set(colors):
        # Bit i is set if integer i has this color
        mask = sum(1 << (i + 1) for i, c in enumerate(colors) if c == color)
        for x in bits(mask):
            # Bit y is set if y and x + y both have this color
            sums = (mask >> x) & mask
            if weak:
                sums &= ~(1 << x)
            if sums:
                return True
    return False


def schur_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], weak: bool) -> None:
    """S(k) >= value (or WS(k) >= value) is witnessed by a k-coloring of 1, ...,
    value with no monochromatic solution to x + y = z (with x ≠ y for WS)."""
    colors = read_coloring(cert, params["k"])
    if len(colors) != value:
        raise CertificateError(f"Coloring has {len(colors)} integers, but a lower bound of {value} needs {value}")
    if has_monochromatic_sum(colors, weak):
        raise CertificateError(f"Coloring has a monochromatic solution to x + y = z{' with x ≠ y' if weak else ''}")


def schur_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    schur_witness(params, bound, value, cert, weak=False)


def weak_schur_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    schur_witness(params, bound, value, cert, weak=True)


FAMILIES = {
    "schur": Family(
        id_pattern=re.compile(r"schur-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.Schur",
        lean_statement=schur_lean_statement,
        check_witness=schur_check_witness,
        witness_bound="lower",
    ),
    "weak-schur": Family(
        id_pattern=re.compile(r"weak-schur-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.Schur",
        lean_statement=weak_schur_lean_statement,
        check_witness=weak_schur_check_witness,
        witness_bound="lower",
    ),
}
