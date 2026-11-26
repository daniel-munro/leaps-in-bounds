"""Book Ramsey numbers R(B_m, B_n)."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..graphs import complement, read_graph


def book_ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.BookRamsey.{name}", [params['m'], params['n'], value]


def largest_book(adj: list[int]) -> int:
    """The largest number of common neighbors of the ends of an edge: the
    largest k such that the graph contains the book B_k."""
    best = 0
    for u in range(len(adj)):
        for v in range(u + 1, len(adj)):
            if adj[u] >> v & 1:
                best = max(best, (adj[u] & adj[v]).bit_count())
    return best


def book_ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R(B_m, B_n) >= value is witnessed by a graph on value - 1 vertices in
    which no edge has m common neighbors, and whose complement has no edge
    with n common neighbors."""
    m, n = params["m"], params["n"]
    if m > n:
        raise CertificateError("Book Ramsey constants are listed with m <= n")
    adj = read_graph(cert)
    if len(adj) != value - 1:
        raise CertificateError(f"Graph has {len(adj)} vertices, but R(B_m,B_n) >= {value} needs {value - 1}")
    if (k := largest_book(adj)) >= m:
        raise CertificateError(f"Graph contains the book B_{m}: an edge has {k} common neighbors")
    if (k := largest_book(complement(adj))) >= n:
        raise CertificateError(f"Complement contains the book B_{n}: an edge has {k} common neighbors")


FAMILIES = {
    "book-ramsey": Family(
        id_pattern=re.compile(r"book-ramsey-(?P<m>\d+)-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.BookRamsey",
        lean_statement=book_ramsey_lean_statement,
        check_witness=book_ramsey_check_witness,
        witness_bound="lower",
    ),
}
