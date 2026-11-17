"""Ramsey numbers R(r, s)."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..graphs import complement, has_clique, read_graph


def ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Ramsey.{name}", [params['r'], params['s'], value]


def ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R(r,s) >= value is witnessed by a graph on value - 1 vertices with no
    r-clique and no independent set of size s."""
    adj = read_graph(cert)
    if len(adj) != value - 1:
        raise CertificateError(f"Graph has {len(adj)} vertices, but R(r,s) >= {value} needs {value - 1}")
    if has_clique(adj, params["r"]):
        raise CertificateError(f"Graph contains a clique of size {params['r']}")
    if has_clique(complement(adj), params["s"]):
        raise CertificateError(f"Graph contains an independent set of size {params['s']}")


FAMILIES = {
    "ramsey": Family(
        id_pattern=re.compile(r"ramsey-(?P<r>\d+)-(?P<s>\d+)"),
        lean_module="LeapsInBounds.Statements.Ramsey",
        lean_statement=ramsey_lean_statement,
        check_witness=ramsey_check_witness,
        witness_bound="lower",
    ),
}
