"""The size and depth of sorting networks."""

import itertools
import re
from typing import Any, Mapping

import numpy as np

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


def sorting_network_size_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "SizeLowerBound" if bound == "lower" else "SizeUpperBound"
    return f"LeapsInBounds.SortingNetwork.{name}", [params['n'], value]


def sorting_network_depth_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "DepthLowerBound" if bound == "lower" else "DepthUpperBound"
    return f"LeapsInBounds.SortingNetwork.{name}", [params['n'], value]


def read_comparators(data: str) -> list[tuple[int, int]]:
    """Parse a comparator network: comparators `i,j`, in the order they're
    applied, separated by whitespace (newlines can separate layers, but don't
    have to)."""
    comparators = []
    for word in data.split():
        match = re.fullmatch(r"(\d+),(\d+)", word)
        if not match:
            raise CertificateError(f"Comparators must be written i,j, not {word[:40]!r}")
        comparators.append((int(match.group(1)), int(match.group(2))))
    return comparators


def network_depth(comparators: list[tuple[int, int]]) -> int:
    """The number of parallel steps the network takes: each comparator acts
    one step after the later of the last comparators on its two wires."""
    step: dict[int, int] = {}
    for i, j in comparators:
        step[i] = step[j] = max(step.get(i, 0), step.get(j, 0)) + 1
    return max(step.values(), default=0)


# Most 0-1 inputs a sorting network is run on in one batch, as bits
SORTING_BATCH_BITS = 1 << 24


def sorts(n: int, comparators: list[tuple[int, int]]) -> bool:
    """Check that a network of comparators on wires 0, ..., n - 1 sorts every
    input, each comparator putting the smaller value on the lower wire.

    By the 0-1 principle, it's enough to check inputs of 0s and 1s, and only
    those the network's first comparators can output: those that come before
    any other comparator on their wires take 3 inputs to 3 outputs, so they
    leave 3^p 2^(n - 2p) of the 2^n inputs, for p of them. These are run in
    batches, bit-sliced: wire k holds bit k of each input, as an array of bits
    in which a comparator is an `and` and an `or`.
    """
    if any(not (0 <= i < n and 0 <= j < n and i != j) for i, j in comparators):
        return False
    comparators = [(min(i, j), max(i, j)) for i, j in comparators]
    # The leading comparators: each the first comparator on both its wires
    # (which commute with any comparators before them, on other wires)
    used: set[int] = set()
    first, rest = [], []
    for i, j in comparators:
        (first if i not in used and j not in used else rest).append((i, j))
        used.update((i, j))
    paired = {w for c in first for w in c}
    # Digits of the mixed-radix index of an input: 3 outputs of each leading
    # comparator (0,0), (0,1) and (1,1), and 2 values of each other wire
    digits: list[tuple[int, list[tuple[int, list[int]]]]] = [
        (3, [(i, [0, 0, 1]), (j, [0, 1, 1])]) for i, j in first
    ] + [(2, [(k, [0, 1])]) for k in range(n) if k not in paired]
    # The last digits vary within a batch, the others between batches
    inner_size, split = 1, len(digits)
    while split > 0 and inner_size * digits[split - 1][0] <= SORTING_BATCH_BITS:
        split -= 1
        inner_size *= digits[split][0]
    inner_size = max(inner_size, 8)
    inner_wires: dict[int, np.ndarray] = {}
    stride = 1
    for radix, wires in reversed(digits[split:]):
        for wire, values in wires:
            pattern = np.repeat(np.array(values, dtype=bool), stride)
            inner_wires[wire] = np.packbits(np.resize(pattern, inner_size))
        stride *= radix
    ones = np.full((inner_size + 7) // 8, 0xFF, dtype=np.uint8)
    zeros = np.zeros_like(ones)
    for outer in itertools.product(*(range(radix) for radix, _ in digits[:split])):
        wires = dict(inner_wires)
        for digit, (_, assignments) in zip(outer, digits[:split]):
            for wire, values in assignments:
                wires[wire] = ones if values[digit] else zeros
        for i, j in rest:
            wires[i], wires[j] = wires[i] & wires[j], wires[i] | wires[j]
        if any((wires[k] & ~wires[k + 1]).any() for k in range(n - 1)):
            return False
    return True


def sorting_network_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], metric: str) -> None:
    if cert["witness"].get("format") != "comparators":
        raise CertificateError("Sorting network witnesses must use format: comparators")
    n = params["n"]
    comparators = read_comparators(read_witness_data(cert))
    if metric == "size" and len(comparators) > value:
        raise CertificateError(f"Network has {len(comparators)} comparators, more than {value}")
    if metric == "depth" and network_depth(comparators) > value:
        raise CertificateError(f"Network has depth {network_depth(comparators)}, more than {value}")
    if not sorts(n, comparators):
        raise CertificateError(f"Comparators must join two different wires from 0 to {n - 1}, and sort every input")


def sorting_network_size_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """S(n) <= value is witnessed by a sorting network on n wires with at most
    value comparators."""
    sorting_network_witness(params, bound, value, cert, "size")


def sorting_network_depth_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    """D(n) <= value is witnessed by a sorting network on n wires of depth at
    most value."""
    sorting_network_witness(params, bound, value, cert, "depth")


FAMILIES = {
    "sorting-network-size": Family(
        id_pattern=re.compile(r"sorting-network-size-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SortingNetwork",
        lean_statement=sorting_network_size_lean_statement,
        check_witness=sorting_network_size_check_witness,
        witness_bound="upper",
    ),
    "sorting-network-depth": Family(
        id_pattern=re.compile(r"sorting-network-depth-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SortingNetwork",
        lean_statement=sorting_network_depth_lean_statement,
        check_witness=sorting_network_depth_check_witness,
        witness_bound="upper",
    ),
}
