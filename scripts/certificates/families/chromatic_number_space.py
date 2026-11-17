"""The chromatic number of Euclidean space."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family


def chromatic_number_space_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.ChromaticNumberSpace.{name}", [params['n'], value]


def chromatic_number_space_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Bounds on the chromatic number of Euclidean space can only be certified by Lean proofs so far")


FAMILIES = {
    "chromatic-number-space": Family(
        id_pattern=re.compile(r"chromatic-number-space-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.ChromaticNumberSpace",
        lean_statement=chromatic_number_space_lean_statement,
        check_witness=chromatic_number_space_check_witness,
        witness_bound=None,
    ),
}
