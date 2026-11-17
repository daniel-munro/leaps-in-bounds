"""Minimal superpermutations: the shortest string containing every permutation of n
symbols.
"""

import math
import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import BASE36, read_symbols


def superpermutation_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Superpermutation.{name}", [params['n'], value]


def superpermutation_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """L(n) <= value is witnessed by a string of length at most value that
    contains every permutation of n symbols."""
    if cert["witness"].get("format") != "string":
        raise CertificateError("Superpermutation witnesses must use format: string")
    n = params["n"]
    if not 1 <= n <= len(BASE36) - 1:
        raise CertificateError(f"Superpermutation witnesses need 1 <= n <= {len(BASE36) - 1}")
    string = read_symbols(cert, BASE36[1:n + 1], "String")
    symbols = set(BASE36[1:n + 1])
    if len(string) > value:
        raise CertificateError(f"String has length {len(string)}, more than {value}")
    windows = {string[i:i + n] for i in range(len(string) - n + 1)}
    found = sum(set(window) == symbols for window in windows)
    if found != math.factorial(n):
        raise CertificateError(f"String contains {found} of the {math.factorial(n)} permutations")


FAMILIES = {
    "minimal-superpermutation": Family(
        id_pattern=re.compile(r"minimal-superpermutation-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Superpermutation",
        lean_statement=superpermutation_lean_statement,
        check_witness=superpermutation_check_witness,
        witness_bound="upper",
    ),
}
