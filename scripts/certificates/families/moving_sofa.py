"""The moving sofa constant."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..values import parse_radical


def moving_sofa_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.MovingSofa.{name}", [terms, d]


def moving_sofa_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Bounds on the moving sofa constant can only be certified by Lean proofs")


FAMILIES = {
    "moving-sofa": Family(
        id_pattern=re.compile(r"moving-sofa"),
        lean_module="LeapsInBounds.Statements.MovingSofa",
        lean_statement=moving_sofa_lean_statement,
        check_witness=moving_sofa_check_witness,
        witness_bound=None,
        values="radical",
    ),
}
