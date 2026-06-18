#!/usr/bin/env python3
"""
Experimental check for the non-cyclic Mazur exclusion Z/2 x Z/10.

We use the normalized Legendre family

    E_t : y^2 = x (x - 1) (x - t),       t != 0, 1,

which is obtained from y^2 = x (x-a) (x-b) by scaling x by b
when b != 0.  A rational point of order 5 must have x-coordinate
annihilated by the 5-division polynomial.

This script deliberately avoids Sage/Sympy so it can run in the
current lean workspace environment.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt


Monomial = tuple[int, int]  # x^i t^j


@dataclass(frozen=True)
class PolyXT:
    """A small integer polynomial type in variables x,t."""

    terms: dict[Monomial, int]

    def __post_init__(self) -> None:
        object.__setattr__(self, "terms", {k: v for k, v in self.terms.items() if v})

    @staticmethod
    def const(c: int) -> "PolyXT":
        return PolyXT({(0, 0): c}) if c else PolyXT({})

    @staticmethod
    def x() -> "PolyXT":
        return PolyXT({(1, 0): 1})

    @staticmethod
    def t() -> "PolyXT":
        return PolyXT({(0, 1): 1})

    def __add__(self, other: int | "PolyXT") -> "PolyXT":
        other = as_poly(other)
        out = defaultdict(int)
        out.update(self.terms)
        for monomial, coeff in other.terms.items():
            out[monomial] += coeff
        return PolyXT(dict(out))

    __radd__ = __add__

    def __neg__(self) -> "PolyXT":
        return PolyXT({monomial: -coeff for monomial, coeff in self.terms.items()})

    def __sub__(self, other: int | "PolyXT") -> "PolyXT":
        return self + (-as_poly(other))

    def __rsub__(self, other: int | "PolyXT") -> "PolyXT":
        return as_poly(other) + (-self)

    def __mul__(self, other: int | "PolyXT") -> "PolyXT":
        other = as_poly(other)
        out = defaultdict(int)
        for (i, j), a in self.terms.items():
            for (k, ell), b in other.terms.items():
                out[(i + k, j + ell)] += a * b
        return PolyXT(dict(out))

    __rmul__ = __mul__

    def __pow__(self, n: int) -> "PolyXT":
        if n < 0:
            raise ValueError("negative powers are not supported")
        out = PolyXT.const(1)
        base = self
        while n:
            if n & 1:
                out *= base
            base *= base
            n >>= 1
        return out

    def degree_x(self) -> int:
        return max((i for i, _ in self.terms), default=-1)

    def degree_t(self) -> int:
        return max((j for _, j in self.terms), default=-1)

    def eval(self, x_value: Fraction | int, t_value: Fraction | int) -> Fraction:
        x_value = Fraction(x_value)
        t_value = Fraction(t_value)
        total = Fraction(0)
        for (i, j), coeff in self.terms.items():
            total += coeff * x_value**i * t_value**j
        return total

    def coeffs_by_x(self) -> dict[int, dict[int, int]]:
        out: dict[int, dict[int, int]] = defaultdict(lambda: defaultdict(int))
        for (i, j), coeff in self.terms.items():
            out[i][j] += coeff
        return {i: dict(js) for i, js in out.items()}


def as_poly(value: int | PolyXT) -> PolyXT:
    return value if isinstance(value, PolyXT) else PolyXT.const(value)


def compute_psi5() -> PolyXT:
    """Return psi_5 for y^2 = x^3 + A x^2 + B x with A=-(t+1), B=t."""

    x = PolyXT.x()
    t = PolyXT.t()

    a2 = -(t + 1)
    a4 = t
    f = x**3 + a2 * x**2 + a4 * x

    b2 = 4 * a2
    b4 = 2 * a4
    b6 = PolyXT.const(0)
    b8 = -(a4**2)

    psi3 = 3 * x**4 + b2 * x**3 + 3 * b4 * x**2 + 3 * b6 * x + b8
    pre_psi4 = (
        2 * x**6
        + b2 * x**5
        + 5 * b4 * x**4
        + 10 * b6 * x**3
        + 10 * b8 * x**2
        + (b2 * b8 - b4 * b6) * x
        + (b4 * b8 - b6**2)
    )

    # Standard recurrence: psi_5 = psi_4 psi_2^3 - psi_3^3.
    # Since psi_4 = psi_2 * pre_psi4 and psi_2^4 = (2y)^4 = 16 f^2.
    return 16 * f**2 * pre_psi4 - psi3**3


def format_coeffs_by_x(poly: PolyXT) -> str:
    pieces: list[str] = []
    coeffs = poly.coeffs_by_x()
    for i in range(poly.degree_x(), -1, -1):
        if i not in coeffs:
            continue
        parts = []
        for j, coeff in sorted(coeffs[i].items()):
            if j == 0:
                term = str(coeff)
            elif j == 1:
                term = f"{coeff}*t"
            else:
                term = f"{coeff}*t^{j}"
            parts.append(term)
        pieces.append(f"x^{i}: " + " + ".join(parts))
    return "\n".join(pieces)


def rational_grid(bound: int) -> list[Fraction]:
    values = set()
    for den in range(1, bound + 1):
        for num in range(-bound, bound + 1):
            if gcd(num, den) == 1:
                values.add(Fraction(num, den))
    return sorted(values)


def is_square_q(value: Fraction) -> bool:
    if value < 0:
        return False
    return (
        isqrt(value.numerator) ** 2 == value.numerator
        and isqrt(value.denominator) ** 2 == value.denominator
    )


def bounded_rational_search(poly: PolyXT, bound: int) -> tuple[list[tuple[Fraction, Fraction]], list[tuple[Fraction, Fraction, Fraction]]]:
    """Search |num|,den <= bound for psi_5(u,t)=0.

    Returns all x-coordinate hits, and the subset where y^2=x(x-1)(x-t)
    is a rational square.
    """

    values = rational_grid(bound)
    hits: list[tuple[Fraction, Fraction]] = []
    square_hits: list[tuple[Fraction, Fraction, Fraction]] = []
    for t_value in values:
        if t_value in (0, 1):
            continue
        for x_value in values:
            if poly.eval(x_value, t_value) == 0:
                hits.append((t_value, x_value))
                rhs = x_value * (x_value - 1) * (x_value - t_value)
                if is_square_q(rhs):
                    square_hits.append((t_value, x_value, rhs))
    return hits, square_hits


def finite_field_affine_hits(poly: PolyXT, p: int) -> list[tuple[int, int]]:
    hits = []
    for t_value in range(p):
        if t_value in (0, 1):
            continue
        for x_value in range(p):
            if poly.eval(x_value, t_value) % p == 0:
                hits.append((t_value, x_value))
    return hits


def main() -> None:
    psi5 = compute_psi5()

    print("Normalized family: y^2 = x (x - 1) (x - t), t != 0, 1")
    print(f"psi_5 terms: {len(psi5.terms)}")
    print(f"degree_x={psi5.degree_x()}, degree_t={psi5.degree_t()}")
    print()
    print("psi_5 coefficients, grouped by powers of x:")
    print(format_coeffs_by_x(psi5))
    print()

    bound = 20
    hits, square_hits = bounded_rational_search(psi5, bound)
    print(f"Bounded rational search: |num|, den <= {bound}")
    print(f"psi_5 rational x-coordinate hits: {len(hits)}")
    print(f"hits with rational y: {len(square_hits)}")
    if hits:
        print("first x-coordinate hits:", hits[:20])
    if square_hits:
        print("first rational point hits:", square_hits[:20])
    print()

    print("Affine finite-field check for psi_5(x,t)=0 with t != 0,1:")
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        hits_p = finite_field_affine_hits(psi5, p)
        preview = hits_p[:5]
        print(f"F_{p}: {len(hits_p)} hits; first={preview}")


if __name__ == "__main__":
    main()
