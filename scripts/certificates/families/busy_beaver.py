"""The busy beaver functions: maximum shifts and ones."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import read_witness_data


def busy_beaver_shift_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "ShiftLowerBound" if bound == "lower" else "ShiftUpperBound"
    return f"LeapsInBounds.BusyBeaver.{name}", [params['n'], value]


def busy_beaver_ones_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "OnesLowerBound" if bound == "lower" else "OnesUpperBound"
    return f"LeapsInBounds.BusyBeaver.{name}", [params['n'], value]


TURING_TRANSITION = re.compile(r"([01])([LR])([A-Z])|---")

# Simulating 10⁹ steps takes a minute or two.
MAX_TURING_STEPS = 10**9


def read_turing_machine(data: str, n: int) -> list[tuple[int, int, int]]:
    """Parse an n-state, 2-symbol Turing machine in the standard text format,
    such as `1RB1LB_1LA1RZ`: for each state A, B, … in turn, separated by `_`,
    its transitions on reading 0 and 1, each written as the symbol to write,
    the direction to move (L or R) and the next state. A next state after the
    first n letters, conventionally Z or H, halts, and an undefined transition
    `---` halts the same as `1RZ`. Returns (write, move, next) for state q
    reading s at index 2q + s, with move ±1 and next -1 for halting."""
    rows = "".join(data.split()).upper().split("_")
    if len(rows) != n:
        raise CertificateError(f"Machine has {len(rows)} states, not {n}")
    table = []
    for q, row in enumerate(rows):
        if len(row) != 6:
            raise CertificateError(f"State {chr(65 + q)} must have two transitions of 3 characters, not {row!r}")
        for transition in (row[:3], row[3:]):
            if not TURING_TRANSITION.fullmatch(transition):
                raise CertificateError(f"Can't read transition {transition!r}")
            if transition == "---":
                transition = "1RZ"
            target = ord(transition[2]) - ord("A")
            table.append((int(transition[0]), 1 if transition[1] == "R" else -1, target if target < n else -1))
    return table


def run_turing_machine(table: list[tuple[int, int, int]], limit: int) -> tuple[int, int] | None:
    """Run a machine from state A on a blank tape. Returns the number of steps
    it takes to halt, counting the halting transition, and the number of 1s
    then on the tape, or None if it doesn't halt within `limit` steps."""
    write = [w for w, _, _ in table]
    move = [m for _, m, _ in table]
    target = [t for _, _, t in table]
    size = 1 << 16
    tape = bytearray(size)
    head, state, steps = size // 2, 0, 0
    while steps < limit:
        i = 2 * state + tape[head]
        tape[head] = write[i]
        head += move[i]
        state = target[i]
        steps += 1
        if state < 0:
            return steps, tape.count(1)
        if not 0 <= head < size:
            if head < 0:
                tape = bytearray(size) + tape
                head += size
            else:
                tape += bytearray(size)
            size *= 2
    return None


def busy_beaver_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], ones: bool) -> None:
    """BB(n) >= value is witnessed by an n-state, 2-symbol machine that halts
    after at least value steps from a blank tape, and Σ(n) >= value by one
    that halts with at least value 1s on the tape."""
    if cert["witness"].get("format") != "turing-machine":
        raise CertificateError("Busy beaver witnesses must use format: turing-machine")
    table = read_turing_machine(read_witness_data(cert), params["n"])
    result = run_turing_machine(table, MAX_TURING_STEPS)
    if result is None:
        raise CertificateError(f"Machine doesn't halt within {MAX_TURING_STEPS} steps, the most the checker runs")
    steps, count = result
    if ones and count < value:
        raise CertificateError(f"Machine halts with {count} 1s, fewer than {value}")
    if not ones and steps < value:
        raise CertificateError(f"Machine halts after {steps} steps, fewer than {value}")


def busy_beaver_shift_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    busy_beaver_witness(params, bound, value, cert, ones=False)


def busy_beaver_ones_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    busy_beaver_witness(params, bound, value, cert, ones=True)


FAMILIES = {
    "busy-beaver-shift": Family(
        id_pattern=re.compile(r"busy-beaver-shift-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.BusyBeaver",
        lean_statement=busy_beaver_shift_lean_statement,
        check_witness=busy_beaver_shift_check_witness,
        witness_bound="lower",
    ),
    "busy-beaver-ones": Family(
        id_pattern=re.compile(r"busy-beaver-ones-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.BusyBeaver",
        lean_statement=busy_beaver_ones_lean_statement,
        check_witness=busy_beaver_ones_check_witness,
        witness_bound="lower",
    ),
}
