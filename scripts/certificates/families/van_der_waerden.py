"""Van der Waerden numbers W(r, k)."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import read_coloring


def van_der_waerden_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.VanDerWaerden.{name}", [params['r'], params['k'], value]


def has_monochromatic_ap(colors: str, k: int) -> bool:
    """Check whether a coloring (one character per integer) has a
    monochromatic arithmetic progression of length k."""
    n = len(colors)
    for color in set(colors):
        mask = sum(1 << i for i, c in enumerate(colors) if c == color)
        for d in range(1, (n - 1) // (k - 1) + 1):
            ap_starts = mask
            for i in range(1, k):
                ap_starts &= mask >> (i * d)
            if ap_starts:
                return True
    return False


def van_der_waerden_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """W(r,k) >= value is witnessed by an r-coloring of value - 1 consecutive
    integers with no monochromatic arithmetic progression of length k."""
    r, k = params["r"], params["k"]
    if k < 2:
        raise CertificateError("Van der Waerden witnesses need k >= 2")
    colors = read_coloring(cert, r)
    if len(colors) != value - 1:
        raise CertificateError(f"Coloring has {len(colors)} integers, but W(r,k) >= {value} needs {value - 1}")
    if has_monochromatic_ap(colors, k):
        raise CertificateError(f"Coloring has a monochromatic arithmetic progression of length {k}")


FAMILIES = {
    "van-der-waerden": Family(
        id_pattern=re.compile(r"van-der-waerden-(?P<r>\d+)-(?P<k>\d+)"),
        lean_module="LeapsInBounds.Statements.VanDerWaerden",
        lean_statement=van_der_waerden_lean_statement,
        check_witness=van_der_waerden_check_witness,
        witness_bound="lower",
    ),
}
