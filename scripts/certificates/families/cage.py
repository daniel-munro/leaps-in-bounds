"""Cages: the fewest vertices of a k-regular graph of girth g."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..graphs import girth, read_graph


def cage_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Cage.{name}", [params['k'], params['g'], value]


def cage_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """n(k,g) <= value is witnessed by a k-regular graph of girth g on value
    vertices."""
    adj = read_graph(cert)
    if len(adj) != value:
        raise CertificateError(f"Graph has {len(adj)} vertices, but n(k,g) <= {value} needs {value}")
    if any(neighbors.bit_count() != params["k"] for neighbors in adj):
        raise CertificateError(f"Graph is not {params['k']}-regular")
    if girth(adj) != params["g"]:
        raise CertificateError(f"Graph has girth {girth(adj)}, not {params['g']}")


FAMILIES = {
    "cage": Family(
        id_pattern=re.compile(r"cage-(?P<k>\d+)-(?P<g>\d+)"),
        lean_module="LeapsInBounds.Statements.Cage",
        lean_statement=cage_lean_statement,
        check_witness=cage_check_witness,
        witness_bound="upper",
    ),
}
