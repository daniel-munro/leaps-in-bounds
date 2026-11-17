"""The de Bruijn–Newman constant."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..values import parse_radical


def debruijn_newman_lean_statement(params: Mapping[str, int], bound: str, value: int | str) -> tuple[str, list[Any]]:
    name = "RadicalLowerBound" if bound == "lower" else "RadicalUpperBound"
    terms, d = parse_radical(value).lean_args()
    return f"LeapsInBounds.DeBruijnNewman.{name}", [terms, d]


def debruijn_newman_check_witness(params: Mapping[str, int], bound: str, value: int | str, cert: Mapping[str, Any]) -> None:
    raise CertificateError("Bounds on the de Bruijn–Newman constant can only be certified by Lean proofs")


FAMILIES = {
    "debruijn-newman": Family(
        id_pattern=re.compile(r"debruijn-newman"),
        lean_module="LeapsInBounds.Statements.DeBruijnNewman",
        lean_statement=debruijn_newman_lean_statement,
        check_witness=debruijn_newman_check_witness,
        witness_bound=None,
        values="radical",
    ),
}
