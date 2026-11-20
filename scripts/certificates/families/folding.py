"""Stamp folding and map folding."""

import hashlib
import re
from typing import Any, Mapping, Sequence

import numpy as np

from ..errors import CertificateError
from ..family import Family
from ..streaming import count_distinct, map_batches
from ..witness import witness_lines


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


BATCH_ROWS = 10_000

# The value of each base-36 digit, by its ASCII code, or 255 if not a digit
DIGIT_VALUE = np.full(256, 255, dtype=np.uint16)
for _d, _c in enumerate("0123456789abcdefghijklmnopqrstuvwxyz"):
    DIGIT_VALUE[ord(_c)] = DIGIT_VALUE[ord(_c.upper())] = _d


def parse_stacks(tokens: list[str], cells: int) -> np.ndarray:
    """The stacks, as an array with one row per stack, from tokens of one
    base-36 character per cell, two per cell (for maps of more than 36 cells),
    or decimal cells separated by commas. A token that isn't one of these gets
    a row that isn't a permutation, so it fails the next check."""
    stacks = np.full((len(tokens), cells), cells, dtype=np.int64)
    width = 1 if cells <= 36 else 2
    plain = [k for k, t in enumerate(tokens) if len(t) == width * cells and "," not in t]
    if plain:
        try:
            data = "".join(tokens[k] for k in plain).encode("ascii")
        except UnicodeEncodeError:
            data = b""
        if len(data) == len(plain) * width * cells:
            digits = DIGIT_VALUE[np.frombuffer(data, dtype=np.uint8)].reshape(len(plain), cells, width).astype(np.int64)
            # An invalid digit, of value 255, makes a value of at least 255
            # here, which a permutation of fewer than 255 cells can't have;
            # with more cells, mark the row as bad directly.
            values = digits[:, :, 0] if width == 1 else digits[:, :, 0] * 36 + digits[:, :, 1]
            values[(digits == 255).any(axis=2)] = cells
            stacks[plain] = values
    for k, token in enumerate(tokens):
        if "," in token:
            try:
                row = [int(c) for c in token.split(",")]
            except ValueError:
                continue
            if len(row) == cells:
                stacks[k] = row
    return stacks


def crossing_stacks(stacks: np.ndarray, groups: list[tuple[np.ndarray, np.ndarray]]) -> np.ndarray:
    """Whether each stack (a row of cells, from the bottom up) has two
    creases on the same edge that cross, by is_folding's test in another
    form. Each crease joins the levels of its two cells, its interval, and on
    each edge these must be nested or disjoint. They are exactly when every
    interval has as many other intervals open at its lower end as at its upper
    end: those open at only one of them cross it, from below or above, so the
    counts are equal when it's crossed as many times from below as from
    above. (If some intervals cross, take one with the lowest upper end among
    them. None crosses it from below, since that one would have a lower upper
    end, so by the counts none crosses it from above either, and it crosses
    nothing after all.) The number of intervals open at each level is a cumulative
    sum, so this takes time proportional to the number of cells."""
    level = np.argsort(stacks, axis=1)
    rows = np.arange(len(stacks))[:, None]
    bad = np.zeros(len(stacks), dtype=bool)
    for a, b in groups:
        la, lb = level[:, a], level[:, b]
        lo, hi = np.minimum(la, lb), np.maximum(la, lb)
        step = np.zeros(stacks.shape, dtype=np.int16)
        step[rows, lo] = 1
        step[rows, hi] = -1
        # open[:, k]: the intervals open just after level k
        open_ = np.cumsum(step, axis=1, dtype=np.int16)
        bad |= (open_[rows, hi] != open_[rows, lo] - 1).any(axis=1)
    return bad


def stack_digests(rows: list[str], m: int, n: int, first: int) -> bytes:
    """Check a batch of rows of stacks, numbered from first, and return an
    8-byte hash of each stack."""
    cells = m * n
    tokens: list[str] = []
    row_of: list[int] = []
    for k, row in enumerate(rows, first):
        for token in row.lower().split():
            tokens.append(token)
            row_of.append(k)
    stacks = parse_stacks(tokens, cells)
    bad = (np.sort(stacks, axis=1) != np.arange(cells)).any(axis=1)
    if bad.any():
        k = int(np.argmax(bad))
        raise CertificateError(f"Stack on row {row_of[k]} ({tokens[k][:40]!r}) doesn't list each of the {cells} cells once, "
                               "as base-36 digits or comma-separated integers")
    groups = [(np.array([c for c, _ in g]), np.array([d for _, d in g])) for g in map_creases(m, n).values()]
    bad = crossing_stacks(stacks, groups)
    if bad.any():
        k = int(np.argmax(bad))
        raise CertificateError(f"Stack on row {row_of[k]} ({tokens[k][:40]!r}) isn't a folding: two creases on the same edge cross")
    # Hash a canonical encoding of each stack, so that the different ways of
    # writing it are the same stack
    data = stacks.astype("<u2").tobytes()
    width = 2 * cells
    return b"".join(hashlib.blake2b(data[k:k + width], digest_size=8).digest() for k in range(0, len(data), width))


def folding_witness(m: int, n: int, value: int, cert: Mapping[str, Any]) -> None:
    """There are at least `value` foldings of an m × n map when the witness has
    at least `value` distinct stacks of its cells that are foldings. Stacks
    can repeat, and are counted by an 8-byte hash: two sharing a hash would
    only be undercounted. The witness is read as a stream, so a generator can
    print any amount."""
    if cert["witness"].get("format") != "stacks":
        raise CertificateError("Folding witnesses must use format: stacks")
    total, distinct = count_distinct(map_batches(stack_digests, witness_lines(cert), BATCH_ROWS, m, n))
    if distinct < value:
        raise CertificateError(f"Witness has {total} stacks, of which {distinct} are distinct, fewer than {value}")


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
