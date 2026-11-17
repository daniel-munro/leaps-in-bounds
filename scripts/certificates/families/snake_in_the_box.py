"""Snakes and coils in the hypercube."""

import re
from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..witness import BASE36, read_witness_data


def snake_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "LowerBound" if bound == "lower" else "UpperBound"
    return f"LeapsInBounds.SnakeInTheBox.{name}", [params['n'], value]


def coil_lean_statement(params: Mapping[str, int], bound: str, value: int) -> tuple[str, list[int]]:
    name = "CoilLowerBound" if bound == "lower" else "CoilUpperBound"
    return f"LeapsInBounds.SnakeInTheBox.{name}", [params['n'], value]


def read_transitions(data: str, n: int) -> list[int]:
    """Parse a transition sequence: one character per coordinate, from 0 to
    n - 1, written in base 36 (0 to 9, then a to z). Whitespace is ignored."""
    digits = BASE36[:n]
    transitions = "".join(data.split()).lower()
    if not set(transitions) <= set(digits):
        raise CertificateError(f"Transitions must be coordinates from 0 to {digits[-1]}")
    return [digits.index(c) for c in transitions]


def transition_vertices(transitions: list[int]) -> list[int]:
    """The vertices of Q_n, as bitmasks, visited by flipping each coordinate
    in turn, starting at 0."""
    vertices = [0]
    for c in transitions:
        vertices.append(vertices[-1] ^ (1 << c))
    return vertices


def is_snake(transitions: list[int], n: int, coil: bool = False) -> bool:
    """Check that the transitions trace an induced path in Q_n (an induced
    cycle, back to the start, if coil): its vertices are distinct and
    adjacent only when they're consecutive."""
    vertices = transition_vertices(transitions)
    if coil:
        if len(vertices) < 4 or vertices.pop() != 0:
            return False
    position = {v: i for i, v in enumerate(vertices)}
    if len(position) != len(vertices):
        return False
    length = len(vertices)
    for i, v in enumerate(vertices):
        for c in range(n):
            j = position.get(v ^ (1 << c))
            if j is None:
                continue
            gap = abs(i - j)
            if gap != 1 and not (coil and gap == length - 1):
                return False
    return True


def snake_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any], coil: bool) -> None:
    """A snake (or coil) of length L in Q_n witnesses that the longest one has
    length at least L. It's given by its transition sequence: the coordinate
    that changes along each edge, starting from the vertex 0."""
    kind = "Coil" if coil else "Snake"
    if cert["witness"].get("format") != "transitions":
        raise CertificateError(f"{kind} witnesses must use format: transitions")
    n = params["n"]
    if n > 36:
        raise CertificateError(f"{kind} witnesses need n <= 36")
    transitions = read_transitions(read_witness_data(cert), n)
    if len(transitions) != value:
        raise CertificateError(f"{kind} has {len(transitions)} edges, but a lower bound of {value} needs {value}")
    if not is_snake(transitions, n, coil):
        if coil:
            raise CertificateError("Transitions don't trace an induced cycle in the hypercube")
        raise CertificateError("Transitions don't trace an induced path in the hypercube")


def snake_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    snake_witness(params, bound, value, cert, coil=False)


def coil_check_witness(params: Mapping[str, int], bound: str, value: int, cert: Mapping[str, Any]) -> None:
    snake_witness(params, bound, value, cert, coil=True)


FAMILIES = {
    "snake-in-the-box": Family(
        id_pattern=re.compile(r"snake-in-the-box-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SnakeInTheBox",
        lean_statement=snake_lean_statement,
        check_witness=snake_check_witness,
        witness_bound="lower",
    ),
    "coil-in-the-box": Family(
        id_pattern=re.compile(r"coil-in-the-box-(?P<n>\d+)"),
        lean_module="LeapsInBounds.Statements.SnakeInTheBox",
        lean_statement=coil_lean_statement,
        check_witness=coil_check_witness,
        witness_bound="lower",
    ),
}
