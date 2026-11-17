"""Packing n unit squares in the smallest square."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..values import sqrt_argument


def square_packing_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[int]]:
    name = "SqrtLowerBound" if bound == "lower" else "SqrtUpperBound"
    return f"LeapsInBounds.SquarePacking.{name}", [params['n'], sqrt_argument(value)]


def square_packing_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Square packing bounds can only be certified by Lean proofs so far")


FAMILIES = {
    "square-packing": Family(
        id_pattern=re.compile(r"square-packing-in-square-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SquarePacking",
        lean_statement=square_packing_lean_statement,
        check_witness=square_packing_check_witness,
        witness_bound=None,
        values="sqrt",
    ),
}
