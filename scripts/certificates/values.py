r"""Bound values.

Bounds are integers, or for some families square roots `\sqrt{m}` or sums of
rational multiples of square roots, such as `4+2\sqrt{3}+\frac{4\sqrt{6}}{3}`
or `0.6094` (see Family.values).
"""

import math
import re
from fractions import Fraction
from typing import Any, Mapping

from .errors import CertificateError


SQRT_PATTERN = re.compile(r"\\sqrt\{(\d+)\}")
RADICAL_TERM = re.compile(r"([+-]?)(?:\\frac\{(\d*)(?:\\sqrt\{(\d+)\})?\}\{(\d+)\}|(\d*(?:\.\d+)?)(?:\\sqrt\{(\d+)\})?)")
MAX_RADICAND = 10**9


def squarefree_part(m: int) -> tuple[int, int]:
    """Write m = k² r with r squarefree, returning (k, r)."""
    k, r, p = 1, 1, 2
    while p * p <= m:
        while m % (p * p) == 0:
            m //= p * p
            k *= p
        if m % p == 0:
            m //= p
            r *= p
        p += 1
    return k, r * m


def prime_factors(m: int) -> list[int]:
    """The distinct prime factors of m, in increasing order."""
    primes, p = [], 2
    while p * p <= m:
        if m % p == 0:
            primes.append(p)
            while m % p == 0:
                m //= p
        p += 1
    return primes + [m] if m > 1 else primes


class Radical:
    """An exact real number ∑ cᵢ √mᵢ, with rational cᵢ and distinct squarefree
    mᵢ (mᵢ = 1 for the rational part), stored as {mᵢ: cᵢ}."""

    def __init__(self, terms: Mapping[int, Fraction] | None = None) -> None:
        self.terms = {m: Fraction(c) for m, c in (terms or {}).items() if c}

    @classmethod
    def sqrt(cls, m: int, c: Fraction | int = 1) -> "Radical":
        """c √m."""
        k, r = squarefree_part(m)
        return cls({r: Fraction(c) * k})

    def __add__(self, other: "Radical | Fraction | int") -> "Radical":
        terms = dict(self.terms)
        for m, c in to_radical(other).terms.items():
            terms[m] = terms.get(m, 0) + c
        return Radical(terms)

    __radd__ = __add__

    def __neg__(self) -> "Radical":
        return Radical({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: "Radical | Fraction | int") -> "Radical":
        return self + -to_radical(other)

    def __rsub__(self, other: "Radical | Fraction | int") -> "Radical":
        return to_radical(other) + -self

    def __mul__(self, other: "Radical | Fraction | int") -> "Radical":
        out = Radical()
        for m, c in self.terms.items():
            for n, d in to_radical(other).terms.items():
                g = math.gcd(m, n)  # √m √n = g √(mn / g²)
                out += Radical({m * n // (g * g): c * d * g})
        return out

    __rmul__ = __mul__

    def sign(self) -> int:
        """The exact sign: -1, 0 or 1.

        For the largest prime p in a radicand, write x = u + v √p with no √p
        in u or v. If u and v have the same sign (or one is 0), so does x.
        Otherwise x has the sign of u times that of u² - p v², since
        x (u - v √p) = u² - p v² and u - v √p has the sign of u.
        """
        if not self.terms:
            return 0
        p = max(max(prime_factors(m), default=1) for m in self.terms)
        if p == 1:
            return 1 if self.terms[1] > 0 else -1
        u = Radical({m: c for m, c in self.terms.items() if m % p})
        v = Radical({m // p: c for m, c in self.terms.items() if m % p == 0})
        su, sv = u.sign(), v.sign()
        if su == 0 or su == sv:
            return sv
        if sv == 0:
            return su
        return su * (u * u - p * v * v).sign()

    def inverse(self) -> "Radical":
        """1 / self, for nonzero self.

        For the largest prime p in a radicand, write x = u + v √p with no √p
        in u or v. Then 1 / x = (u - v √p) / (u² - p v²), where the
        denominator has fewer primes in its radicands.
        """
        if not self.terms:
            raise ZeroDivisionError("Radical division by zero")
        p = max(max(prime_factors(m), default=1) for m in self.terms)
        if p == 1:
            return Radical({1: 1 / self.terms[1]})
        u = Radical({m: c for m, c in self.terms.items() if m % p})
        v = Radical({m // p: c for m, c in self.terms.items() if m % p == 0})
        conjugate = u - v * Radical.sqrt(p)
        return conjugate * (u * u - p * v * v).inverse()

    def __eq__(self, other: object) -> bool:
        return isinstance(other, (Radical, Fraction, int)) and self.terms == to_radical(other).terms

    def __hash__(self) -> int:
        return hash(frozenset(self.terms.items()))

    def __float__(self) -> float:
        return math.fsum(float(c) * math.sqrt(m) for m, c in self.terms.items())

    def lean_args(self) -> tuple[list[list[int]], int]:
        """The terms [[c₁, m₁], ...] and denominator d with self = (∑ cᵢ √mᵢ) / d,
        for integers cᵢ, d the least common denominator, and mᵢ increasing."""
        d = math.lcm(*(c.denominator for c in self.terms.values()))
        return [[int(c * d), m] for m, c in sorted(self.terms.items())], d


def to_radical(x: "Radical | Fraction | int") -> Radical:
    return x if isinstance(x, Radical) else Radical({1: Fraction(x)})


def parse_radical(text: Any) -> Radical:
    """Parse an integer, or a string summing terms `a`, `a\\sqrt{m}` or
    `\\frac{a\\sqrt{m}}{b}`, each with an optional sign, where a can be
    omitted before a square root, and can be a decimal outside a fraction."""
    if isinstance(text, int) and not isinstance(text, bool):
        return to_radical(text)
    error = CertificateError(f"Can't read {text!r} as a sum of rational multiples of square roots")
    if not isinstance(text, str):
        raise error
    s = re.sub(r"\s*([+-])\s*", r"\1", text.strip())
    if not s or any(c.isspace() for c in s):
        raise error
    total, pos = Radical(), 0
    while pos < len(s):
        match = RADICAL_TERM.match(s, pos)
        if match.end() == pos or (pos > 0 and not match.group(1)):
            raise error
        sign, frac_coef, frac_root, den, coef, root = match.groups()
        if den is not None:
            coef, root = frac_coef, frac_root
        if not coef and not root:
            raise error
        c, m, d = Fraction(coef or 1), int(root or 1), int(den or 1)
        if d == 0 or m > MAX_RADICAND:
            raise error
        total += Radical.sqrt(m, Fraction(-c if sign == "-" else c, d))
        pos = match.end()
    return total


def value_approx(value: Any, path: Any = None) -> float:
    """Numeric value of a certificate's bound: an integer, or a string that
    parse_radical reads."""
    try:
        return float(parse_radical(value))
    except CertificateError:
        raise CertificateError(f"{path}: value must be an integer or a sum of rational multiples of square roots, not {value!r}")


def check_value_type(values: str, value: Any) -> None:
    """Check that a value has a form allowed by a family (see Family.values)."""
    if isinstance(value, int) and not isinstance(value, bool):
        return
    if values == "sqrt" and isinstance(value, str) and SQRT_PATTERN.fullmatch(value):
        return
    if values == "radical":
        parse_radical(value)
        return
    allowed = {"integer": "integers", "sqrt": "integers or '\\sqrt{m}'"}.get(values)
    raise CertificateError(f"Values for this family must be {allowed}")


def sqrt_argument(value: int | str) -> int:
    """The m with value = √m, for an integer value or one written `\\sqrt{m}`.
    Square roots of perfect squares must be written as integers."""
    if isinstance(value, int):
        return value * value
    m = int(SQRT_PATTERN.fullmatch(value).group(1))
    if math.isqrt(m) ** 2 == m:
        raise CertificateError(f"Write \\sqrt{{{m}}} as {math.isqrt(m)}")
    return m
