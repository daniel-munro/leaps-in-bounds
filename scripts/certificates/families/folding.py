"""Stamp folding and map folding."""

import re
from typing import Any, Mapping, Sequence

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


def stamp_folding_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "StampLowerBound" if bound == "lower" else "StampUpperBound"
    return f"LeapsInBounds.Folding.{name}", [params['n'], value]


def map_folding_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.Folding.{name}", [params['m'], params['n'], value]


def map_creases(m: int, n: int) -> dict[tuple[int, int], list[tuple[int, int]]]:
    """The creases of an m × n map, with its cells numbered 0 to mn - 1 row by
    row, grouped by the edge of the folded stack they end up on: the creases
    between rows i and i + 1, or columns j and j + 1, are on one of two
    opposite edges, depending on the parity of i or j."""
    creases: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for i in range(m):
        for j in range(n):
            cell = i * n + j
            if i + 1 < m:
                creases.setdefault((0, i % 2), []).append((cell, cell + n))
            if j + 1 < n:
                creases.setdefault((1, j % 2), []).append((cell, cell + 1))
    return creases


def is_folding(stack: Sequence[int], creases: Mapping[tuple[int, int], list[tuple[int, int]]]) -> bool:
    """Whether a stack of cells (from the bottom up) is a folding: no two
    creases on the same edge of the stack interleave. Each crease joins the
    levels of its two cells, so on each edge they must be nested or disjoint,
    like brackets."""
    level = {c: k for k, c in enumerate(stack)}
    for group in creases.values():
        # Nested or disjoint intervals are balanced brackets: scan the levels,
        # opening an interval at its lower end and closing it at its upper end.
        ends = [0] * len(stack)
        for k, (a, b) in enumerate(group, 1):
            lo, hi = sorted((level[a], level[b]))
            ends[lo], ends[hi] = k, -k
        open_intervals = []
        for e in ends:
            if e > 0:
                open_intervals.append(e)
            elif e < 0 and open_intervals.pop() != -e:
                return False
    return True


def folding_witness(m: int, n: int, value: int, cert: Mapping[str, Any]) -> None:
    """There are at least `value` foldings of an m × n map when `value`
    distinct stacks of its cells are foldings."""
    if cert["witness"].get("format") != "stacks":
        raise CertificateError("Folding witnesses must use format: stacks")
    cells = m * n
    tokens = read_witness_data(cert).lower().split()
    if len(tokens) != value:
        raise CertificateError(f"Witness has {len(tokens)} stacks, not {value}")
    stacks = []
    for k, token in enumerate(tokens, 1):
        # One base-36 character per cell, or decimal cells separated by commas
        # for maps of more than 36 cells.
        try:
            stack = tuple(int(c) for c in token.split(",")) if "," in token else tuple(int(c, 36) for c in token)
        except ValueError:
            raise CertificateError(f"Stack {k} ({token[:40]!r}) isn't base-36 digits or comma-separated integers")
        if sorted(stack) != list(range(cells)):
            raise CertificateError(f"Stack {k} ({token[:40]!r}) doesn't list each of the {cells} cells once")
        stacks.append(stack)
    if len(set(stacks)) != len(stacks):
        raise CertificateError("Stacks aren't distinct")
    creases = map_creases(m, n)
    for k, stack in enumerate(stacks, 1):
        if not is_folding(stack, creases):
            raise CertificateError(f"Stack {k} ({tokens[k - 1][:40]!r}) isn't a folding: two creases on the same edge cross")


def stamp_folding_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    folding_witness(1, params["n"], value, cert)


def map_folding_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    folding_witness(params["m"], params["n"], value, cert)


FAMILIES = {
    "stamp-folding": Family(
        id_pattern=re.compile(r"stamp-folding-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Folding",
        lean_statement=stamp_folding_lean_statement,
        check_witness=stamp_folding_check_witness,
        witness_bound="lower",
    ),
    "map-folding": Family(
        id_pattern=re.compile(r"map-folding-(?P<m>\d+)-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.Folding",
        lean_statement=map_folding_lean_statement,
        check_witness=map_folding_check_witness,
        witness_bound="lower",
    ),
}
