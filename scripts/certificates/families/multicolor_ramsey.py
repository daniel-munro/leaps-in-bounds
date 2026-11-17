"""Multicolor Ramsey numbers for triangles, R(3; r)."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from .schur import has_monochromatic_sum
from ..family import Family
from ..witness import BASE36, read_coloring, read_symbols


def multicolor_ramsey_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.MulticolorRamsey.{name}", [params['k'], value]


def has_monochromatic_triangle(n: int, colors: str) -> bool:
    """Check whether an edge coloring of K_n, given as the colors of the edges
    (0, 1), (0, 2), ..., (0, n - 1), (1, 2), ..., (n - 2, n - 1) in that
    order, has a monochromatic triangle."""
    neighbors: dict[str, list[int]] = {color: [0] * n for color in set(colors)}
    i = 0
    for u in range(n):
        for v in range(u + 1, n):
            adj = neighbors[colors[i]]
            # A common neighbor of u and v in this color closes a triangle
            if adj[u] & adj[v]:
                return True
            adj[u] |= 1 << v
            adj[v] |= 1 << u
            i += 1
    return False


def multicolor_ramsey_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """R_k(3) >= value is witnessed by a k-coloring of the edges of K_{value - 1}
    with no monochromatic triangle: given edge by edge (format: edge-coloring),
    or by a coloring of the differences 1, ..., value - 2 (format: coloring)
    with no monochromatic solution to x + y = z, where the edge between
    vertices u and v gets the color of |u - v|."""
    k = params["k"]
    witness_format = cert["witness"].get("format")
    if witness_format == "coloring":
        colors = read_coloring(cert, k)
        if len(colors) != value - 2:
            raise CertificateError(f"Coloring has {len(colors)} differences, but R_k(3) >= {value} needs {value - 2}")
        if has_monochromatic_sum(colors):
            raise CertificateError("Coloring has a monochromatic solution to x + y = z, so a monochromatic triangle")
    elif witness_format == "edge-coloring":
        if not 1 <= k <= len(BASE36):
            raise CertificateError(f"Colorings can have at most {len(BASE36)} colors")
        colors = read_symbols(cert, BASE36[:k], "Edge coloring")
        n = value - 1
        if len(colors) != n * (n - 1) // 2:
            raise CertificateError(
                f"Edge coloring has {len(colors)} edges, but R_k(3) >= {value} needs the {n * (n - 1) // 2} edges of K_{n}"
            )
        if has_monochromatic_triangle(n, colors):
            raise CertificateError("Edge coloring has a monochromatic triangle")
    else:
        raise CertificateError("Witness must use format: coloring or format: edge-coloring")


FAMILIES = {
    "multicolor-ramsey-triangle": Family(
        id_pattern=re.compile(r"multicolor-ramsey-triangle-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.MulticolorRamsey",
        lean_statement=multicolor_ramsey_lean_statement,
        check_witness=multicolor_ramsey_check_witness,
        witness_bound="lower",
    ),
}
