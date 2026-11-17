"""The degree-diameter problem: the most vertices of a graph of maximum degree d and
diameter k.
"""

import re
from typing import Any, Mapping

import numpy as np

from ..errors import CertificateError
from ..family import Family
from ..graphs import check_simple, decode_hamming_lines, diameter_at_most, edge_arrays, read_graph
from ..witness import read_witness_file


def degree_diameter_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.DegreeDiameter.{name}", [params['d'], params['k'], value]


def degree_diameter_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """N(d,k) >= value is witnessed by a graph on value vertices with maximum
    degree at most d and diameter at most k."""
    if cert["witness"].get("format") == "hamming-lines":
        n, u, v = decode_hamming_lines(read_witness_file(cert))
        check_simple(n, u, v)
    else:
        adj = read_graph(cert)
        n = len(adj)
        u, v = edge_arrays(adj)
    if n != value:
        raise CertificateError(f"Graph has {n} vertices, but N(d,k) >= {value} needs {value}")
    if np.bincount(np.concatenate([u, v]), minlength=n).max(initial=0) > params["d"]:
        raise CertificateError(f"Graph has a vertex of degree more than {params['d']}")
    if not diameter_at_most(n, u, v, params["k"]):
        raise CertificateError(f"Graph has diameter more than {params['k']}")


FAMILIES = {
    "degree-diameter": Family(
        id_pattern=re.compile(r"degree-diameter-(?P<d>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.DegreeDiameter",
        lean_statement=degree_diameter_lean_statement,
        check_witness=degree_diameter_check_witness,
        witness_bound="lower",
    ),
}
