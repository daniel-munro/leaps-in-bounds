"""Lebesgue's universal covering problem."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..values import parse_radical


def lebesgue_cover_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.LebesgueCover.{name}", [terms, d]


def lebesgue_cover_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Bounds on the Lebesgue universal covering constant can only be certified by Lean proofs")


FAMILIES = {
    "lebesgue-universal-cover": Family(
        id_pattern=re.compile(r"lebesgue-universal-cover"),
        lean_module="LeapsInBounds.Statements.LebesgueCover",
        lean_statement=lebesgue_cover_lean_statement,
        check_witness=lebesgue_cover_check_witness,
        witness_bound=None,
        values="radical",
    ),
}
