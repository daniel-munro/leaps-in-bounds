"""How to check certificates for a family of constants."""

import re
from dataclasses import dataclass
from typing import Any, Callable, Mapping


@dataclass
class Family:
    """How to check certificates for one family of constants."""
    # Matches constant IDs, capturing the parameters as named groups.
    id_pattern: re.Pattern[str]
    # Lean module containing the formal statements.
    lean_module: str
    # (params, bound, value) -> Lean constant stating the bound, and its
    # arguments: natural numbers, or lists of [integer, natural number] pairs
    # (List (ℤ × ℕ) in Lean).
    lean_statement: Callable[[Mapping[str, int], str, int | str], tuple[str, list[Any]]]
    # (params, bound, value, cert) -> None, raising CertificateError if invalid.
    check_witness: Callable[[Mapping[str, int], str, int | str, Mapping[str, Any]], None]
    # Which bound a witness can certify ("lower" or "upper"), or None if only
    # Lean proofs are accepted.
    witness_bound: str | None
    # Which values are allowed: "integer", "sqrt" (also `\sqrt{m}`), or
    # "radical" (sums of rational multiples of square roots, read by
    # parse_radical).
    values: str = "integer"
