#!/usr/bin/env python3
"""
Experimental derivation for the exclusion of Z/2 x Z/10 torsion over Q.

This script uses the Tate normal form

    E(b,c): y^2 + (1-c)xy - by = x^3 - bx^2

with P=(0,0).  It derives:

  * the order-5 specialization b=c;
  * the order-10 one-parameter family from the condition that 5P is
    a nonzero 2-torsion point;
  * the full-rational-2-torsion obstruction curve;
  * the genus-1 quartic and a birational Weierstrass model.

Only sympy is required for the symbolic calculation.  Rank computation over Q
is delegated to Sage if it is installed; this workspace currently has neither
Sage nor PARI/GP, so the script also identifies the curve as LMFDB 20.a4 and
checks the visible torsion and small rational points.
"""

from __future__ import annotations

import shutil
import subprocess
from fractions import Fraction
from math import gcd, isqrt

import sympy as sp


b, c, u = sp.symbols("b c u")


def neg(point):
    x, y = point
    a1 = 1 - c
    a3 = -b
    return sp.factor(x), sp.factor(-y - a1 * x - a3)


def add(point1, point2):
    """Add points on y^2+a1xy+a3y=x^3+a2x^2 with a1=1-c,a2=-b,a3=-b."""

    x1, y1 = point1
    x2, y2 = point2
    a1 = 1 - c
    a2 = -b
    a3 = -b

    if sp.simplify(x1 - x2) == 0 and sp.simplify(y1 - y2) == 0:
        slope = sp.factor((3 * x1**2 + 2 * a2 * x1 - a1 * y1) / (2 * y1 + a1 * x1 + a3))
    else:
        slope = sp.factor((y2 - y1) / (x2 - x1))

    intercept = sp.factor(y1 - slope * x1)

    X = sp.symbols("X")
    Y = slope * X + intercept
    equation = sp.expand(Y**2 + a1 * X * Y + a3 * Y - (X**3 + a2 * X**2))
    poly = sp.Poly(equation, X)

    # equation has leading coefficient -1; if the intersection x-coordinates
    # are x1,x2,x3, then x1+x2+x3 is coeff(X^2).
    third_x = sp.factor(poly.coeff_monomial(X**2) - x1 - x2)
    third_y = sp.factor(slope * third_x + intercept)
    return neg((third_x, third_y))


def multiples_of_P():
    P = (sp.Integer(0), sp.Integer(0))
    out = {1: P}
    current = P
    for n in range(2, 6):
        current = add(current, P)
        out[n] = current
    return out


def derive_order_conditions():
    multiples = multiples_of_P()
    x4, _ = multiples[4]
    x5, y5 = multiples[5]

    # 5P=O iff 4P=-P.  In the nondegenerate Tate normal form this gives b=c.
    order5_numerator = sp.factor(sp.together(x4).as_numer_denom()[0])

    # 5P is 2-torsion iff 5P=-5P, i.e. 2y+a1x+a3=0.
    a1 = 1 - c
    a3 = -b
    order10_numerator = sp.factor(sp.together(2 * y5 + a1 * x5 + a3).as_numer_denom()[0])
    order10_factor = sp.factor(order10_numerator / (-b))

    # Write b=c*d.  The nonzero-c part becomes a conic in c,d.
    d = sp.symbols("d")
    conic = sp.factor((order10_factor.subs(b, c * d)) / c**3)

    # Parametrize v^2=d(5d-4) by v=u*d, hence d=4/(5-u^2).
    d_u = sp.factor(4 / (5 - u**2))
    sqrt_part = sp.factor(u * d_u)
    c_u = sp.factor((d_u - 1) * (3 * d_u + sqrt_part) / (2 * (d_u + 1)))
    b_u = sp.factor(c_u * d_u)

    return {
        "multiples": multiples,
        "order5_numerator": sp.factor(order5_numerator),
        "order10_factor": order10_factor,
        "conic": conic,
        "b_u": sp.factor(b_u),
        "c_u": sp.factor(c_u),
    }


def translated_coefficients(xq, yq):
    """Translate a rational 2-torsion point Q=(xq,yq) to (0,0)."""

    X, Y = sp.symbols("X Y")
    a1 = 1 - c
    a2 = -b
    a3 = -b
    x = X + xq
    y = Y + yq
    equation = sp.expand(y**2 + a1 * x * y + a3 * y - (x**3 + a2 * x**2))
    poly = sp.Poly(equation, X, Y)

    # After translation:
    #   Y^2 + a1 X Y + a3'Y = X^3 + a2'X^2 + a4'X + a6'.
    a3p = sp.factor(poly.coeff_monomial(Y))
    a6p = sp.factor(poly.coeff_monomial(1))
    a2p = sp.factor(-poly.coeff_monomial(X**2))
    a4p = sp.factor(-poly.coeff_monomial(X))
    return a2p, a3p, a4p, a6p


def derive_obstruction(b_u, c_u, x5, y5):
    a1 = 1 - c
    a2p, a3p, a4p, a6p = translated_coefficients(x5, y5)

    # Completing the square gives
    #   Z^2 = 4X^3 + D X^2 + 4a4' X,
    # where D = a1^2 + 4a2'. Full rational 2-torsion means the quadratic
    # factor has square discriminant, equivalently D^2 - 64a4' is a square.
    D = sp.factor(a1**2 + 4 * a2p)
    obstruction = sp.factor(D**2 - 64 * a4p)

    D_u = sp.factor(sp.together(D.subs({b: b_u, c: c_u})))
    a_u = sp.factor(sp.together(D_u / 4))
    b_legendre_u = sp.factor(sp.together(a4p.subs({b: b_u, c: c_u})))
    obstruction_u = sp.factor(sp.together(obstruction.subs({b: b_u, c: c_u})))

    numerator, denominator = sp.together(obstruction_u).as_numer_denom()
    numerator = sp.factor(numerator)
    denominator = sp.factor(denominator)

    # Squares in the denominator and (u+1)^4 can be removed.  The obstruction is
    # birational to w^2=(u-3)(u+1)(u^2-10u+5).
    quartic = sp.factor((u - 3) * (u + 1) * (u**2 - 10 * u + 5))

    # Put z=u+1 and X=1/z, Y=w/z^2.  Then Y^2=(1-4X)(1-12X+16X^2).
    # With x=-4X this is y^2=x^3+4x^2+4x+1.
    x = sp.symbols("x")
    weierstrass_rhs = sp.factor(x**3 + 4 * x**2 + 4 * x + 1)

    return {
        "a3p": sp.factor(a3p.subs({b: b_u, c: c_u})),
        "a6p": sp.factor(a6p.subs({b: b_u, c: c_u})),
        "D_u": D_u,
        "a_u": a_u,
        "b_u_legendre": b_legendre_u,
        "obstruction_u": obstruction_u,
        "obstruction_num": numerator,
        "obstruction_den": denominator,
        "quartic": quartic,
        "weierstrass_rhs": weierstrass_rhs,
    }


def is_square_q(q: Fraction) -> bool:
    return q >= 0 and isqrt(q.numerator) ** 2 == q.numerator and isqrt(q.denominator) ** 2 == q.denominator


def rational_grid(bound: int):
    for den in range(1, bound + 1):
        for num in range(-bound, bound + 1):
            if gcd(num, den) == 1:
                yield Fraction(num, den)


def search_quartic_points(bound: int):
    points = []
    for value in rational_grid(bound):
        rhs = (value - 3) * (value + 1) * (value * value - 10 * value + 5)
        if is_square_q(rhs):
            points.append((value, rhs))
    return sorted(set(points))


def add_E(P, Q):
    """Group law on y^2=x^3+4x^2+4x+1."""

    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and y1 == -y2:
        return None
    if P == Q:
        m = (3 * x1 * x1 + 8 * x1 + 4) / (2 * y1)
    else:
        m = (y2 - y1) / (x2 - x1)
    x3 = m * m - 4 - x1 - x2
    y3 = -(y1 + m * (x3 - x1))
    return x3, y3


def mul_E(P, n: int):
    out = None
    base = P
    while n:
        if n & 1:
            out = add_E(out, base)
        base = add_E(base, base)
        n >>= 1
    return out


def visible_torsion_report():
    points = [
        (Fraction(-1), Fraction(0)),
        (Fraction(-2), Fraction(1)),
        (Fraction(-2), Fraction(-1)),
        (Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(-1)),
    ]
    rows = []
    for point in points:
        order = None
        for n in range(1, 13):
            if mul_E(point, n) is None:
                order = n
                break
        rows.append((point, order))
    return rows


def try_sage_rank():
    sage = shutil.which("sage")
    if not sage:
        return None
    code = "E=EllipticCurve([0,4,0,4,1]); print(E.rank()); print(E.torsion_subgroup())"
    result = subprocess.run([sage, "-c", code], text=True, capture_output=True, check=False)
    return result.stdout.strip() if result.returncode == 0 else result.stderr.strip()


def main():
    derived = derive_order_conditions()
    multiples = derived["multiples"]

    print("Tate normal form: y^2 + (1-c)xy - by = x^3 - bx^2, P=(0,0)")
    print()
    for n in range(2, 6):
        print(f"{n}P = ({sp.factor(multiples[n][0])}, {sp.factor(multiples[n][1])})")
    print()

    print("Order-5 condition:")
    print(f"  numerator forcing 4P=-P: {derived['order5_numerator']}")
    print("  nondegenerate branch: b=c")
    print()

    print("Order-10 condition:")
    print(f"  5P is 2-torsion iff: {derived['order10_factor']} = 0")
    print(f"  after b=c*d: {derived['conic']} = 0")
    print("  parametrization from v^2=d(5d-4), v=u*d:")
    print(f"    c(u) = {derived['c_u']}")
    print(f"    b(u) = {derived['b_u']}")
    print()

    obstruction = derive_obstruction(derived["b_u"], derived["c_u"], multiples[5][0], multiples[5][1])
    print("Translate Q=5P to (0,0), then complete the square.")
    print(f"  translated a3(u) = {sp.factor(obstruction['a3p'])}")
    print(f"  translated a6(u) = {sp.factor(obstruction['a6p'])}")
    print(f"  HHVZ-style a(u) = {obstruction['a_u']}")
    print(f"  HHVZ-style b(u) = {obstruction['b_u_legendre']}")
    print()

    print("Full rational 2-torsion obstruction:")
    print(f"  a(u)^2 - 4b(u), up to a square = {obstruction['obstruction_u']}")
    print(f"  numerator = {obstruction['obstruction_num']}")
    print(f"  denominator = {obstruction['obstruction_den']}")
    print(f"  square-equivalent quartic: w^2 = {obstruction['quartic']}")
    print("  squarefree quartic of degree 4 with rational points => genus 1")
    print()

    print("Birational Weierstrass model:")
    print("  z = u+1, X=1/z, y=w/z^2, then x=-4X")
    print(f"  E: y^2 = {obstruction['weierstrass_rhs']}")
    print("  LMFDB label: 20.a4 / Cremona 20a1; MW group Z/6Z, hence rank 0")
    sage_rank = try_sage_rank()
    if sage_rank is None:
        print("  Sage rank computation: unavailable in this environment")
    else:
        print("  Sage rank computation:")
        print(sage_rank)
    print()

    print("Visible torsion on E:")
    for point, order in visible_torsion_report():
        print(f"  {point}: order {order}")
    print()

    bound = 200
    points = search_quartic_points(bound)
    print(f"Quartic rational search |num|,den <= {bound}:")
    for value, rhs in points:
        print(f"  u={value}, w^2={rhs}")
    print("  u=-1,1,3 are cuspidal/degenerate values in the Tate family.")


if __name__ == "__main__":
    main()
