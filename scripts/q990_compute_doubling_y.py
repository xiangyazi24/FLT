#!/usr/bin/env python3
"""Q990: exact SymPy certificate for the Vélu doubling negAddY identity.

This script audits all sign and denominator conventions requested in Q990:

* `diff_std` uses the usual doubled Y-coordinate
    y3 = ell * (x1 - x3) - y1;
* `diff_neg` uses Mathlib's `negAddY`
    negAddY = -ell * (x1 - x3) + y1 = -y3;
* the reduced common denominator is normalized explicitly;
* the primitive numerator is divided by the translated curve equation;
* the resulting B-free coefficient is checked against both hcurve1 and htors;
* exact multivariate factorization and a Q971-Wronskian probe are reported.
"""

from __future__ import annotations

import hashlib

import sympy as sp


# ---------------------------------------------------------------------------
# 1. Full rational identity in the original variables
# ---------------------------------------------------------------------------
x1, y1, A, r, B = sp.symbols("x1 y1 A r B")
Z = sp.symbols("Z")

t = 3 * r**2 + A
Ap = A - 5 * t
Bp = B - 7 * r * t  # Kept for the complete quotient-curve setup.

u_full = 3 * x1**2 + A
ell = u_full / (2 * y1)
x3 = ell**2 - 2 * x1

y3_std = ell * (x1 - x3) - y1
neg_y3 = -ell * (x1 - x3) + y1

X1p = x1 + t / (x1 - r)
Y1p = y1 * ((x1 - r) ** 2 - t) / (x1 - r) ** 2
ellp = (3 * X1p**2 + Ap) / (2 * Y1p)
X3p = ellp**2 - 2 * X1p

Y3p_std = ellp * (X1p - X3p) - Y1p
neg_Y3p = -ellp * (X1p - X3p) + Y1p


def phiY(xx: sp.Expr, yy: sp.Expr) -> sp.Expr:
    return yy * ((xx - r) ** 2 - t) / (xx - r) ** 2


diff_std = phiY(x3, y3_std) - Y3p_std
diff_neg = phiY(x3, neg_y3) - neg_Y3p

# Mathlib negAddY is exactly the negative of the standard doubled Y-coordinate.
assert sp.cancel(sp.together(diff_neg + diff_std)) == 0


# ---------------------------------------------------------------------------
# 2. Compact polynomial names and reduced numerator normalization
# ---------------------------------------------------------------------------
z = y1**2
d = x1 - r
e = d**2 - t
u = 3 * x1**2 + A
m = x1 * d + t
p = 3 * m**2 + (A - 5 * t) * d**2
h = 2 * x1 + r
j = m + 2 * r * d
F = x1**3 + A * x1 + B
F0 = x1**3 + A * x1 - r**3 - A * r
D3 = u**2 - 4 * h * z

# Useful exact identities behind the compact names.
assert sp.expand(F0 - d * j) == 0
assert sp.cancel(x3 - r - D3 / (4 * z)) == 0
assert sp.cancel(ellp - p / (2 * y1 * e)) == 0

# This is the reduced denominator for the standard-coordinate difference.
denY = 2 * y1**3 * d**2 * e**3 * D3**2

rat_std = sp.cancel(sp.together(diff_std))
num_std_cas, den_std_cas = sp.fraction(rat_std)
scale_std = sp.cancel(den_std_cas / denY)
assert not scale_std.free_symbols and scale_std != 0
N_std = sp.expand(num_std_cas / scale_std)
assert sp.cancel(rat_std - N_std / denY) == 0

rat_neg = sp.cancel(sp.together(diff_neg))
num_neg_cas, den_neg_cas = sp.fraction(rat_neg)
scale_neg = sp.cancel(den_neg_cas / denY)
assert not scale_neg.free_symbols and scale_neg != 0
N_neg = sp.expand(num_neg_cas / scale_neg)
assert sp.cancel(rat_neg - N_neg / denY) == 0
assert sp.expand(N_neg + N_std) == 0

# Also retain the uncancelled `together` normalization and its exact multiplier.
raw_std = sp.together(diff_std)
raw_num_std, raw_den_std = sp.fraction(raw_std)
raw_multiplier_std = sp.factor(sp.cancel(raw_num_std / N_std))
assert sp.denom(sp.together(raw_multiplier_std)) == 1
assert sp.expand(raw_num_std - raw_multiplier_std * N_std) == 0
assert sp.expand(raw_num_std * denY - N_std * raw_den_std) == 0


# ---------------------------------------------------------------------------
# 3. Exact primitive numerator and equal B-free coefficient
# ---------------------------------------------------------------------------
b0 = d**2 * u**4 * t * j * (p**2 + p * e * u + e**2 * u**2)
b1 = (
    d**2 * e**3 * u**5 * (7 * x1 + 2 * r)
    - 3 * d * e**2 * p * j * u**4
    - 2 * d**2 * p**3 * u**2 * h
)
b2 = (
    -2 * d**2 * e**3 * u**3 * (2 * (h**2 - t) + 12 * x1 * h + u)
    + 24 * d * e**2 * p * j * u**2 * h
    + 4 * d**2 * p**3 * h**2
    + 2 * e**4 * u**4
)
b3 = (
    16 * d**2 * e**3 * u * (3 * x1 * (h**2 - t) + u * h)
    - 48 * d * e**2 * p * j * h**2
    - 16 * e**4 * u**2 * h
)
b4 = 32 * t * e**3 * (d**2 - h**2)

PZ = sp.expand(b0 + b1 * Z + b2 * Z**2 + b3 * Z**3 + b4 * Z**4)
P = sp.expand(PZ.subs(Z, z))
assert sp.expand(N_std - P) == 0
assert sp.expand(PZ.subs(Z, F0)) == 0

CYZ = sp.expand(
    b1
    + b2 * (Z + F0)
    + b3 * (Z**2 + Z * F0 + F0**2)
    + b4 * (Z**3 + Z**2 * F0 + Z * F0**2 + F0**3)
)
CY = sp.expand(CYZ.subs(Z, z))

q_poly, rem_poly = sp.div(
    sp.Poly(PZ, Z, domain=sp.QQ[x1, A, r]),
    sp.Poly(Z - F0, Z, domain=sp.QQ[x1, A, r]),
)
assert rem_poly.is_zero
assert sp.expand(q_poly.as_expr() - CYZ) == 0
assert sp.expand(N_std - CY * (z - F0)) == 0
assert sp.expand(N_neg - (-CY) * (z - F0)) == 0

hcurve1 = z - x1**3 - A * x1 - B
htors = r**3 + A * r + B
assert sp.expand((z - F0) - (hcurve1 + htors)) == 0
assert B not in CY.free_symbols
assert sp.expand(N_std - CY * hcurve1 - CY * htors) == 0
assert sp.expand(N_neg - (-CY) * hcurve1 - (-CY) * htors) == 0


# ---------------------------------------------------------------------------
# 4. Exact factorization audit
# ---------------------------------------------------------------------------
def term_count(expr: sp.Expr) -> int:
    expanded = sp.expand(expr)
    return 0 if expanded == 0 else len(expanded.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


content_CY, factors_CY = sp.factor_list(CYZ)
factored_CY = sp.factor(CYZ)
assert sp.expand(factored_CY - CYZ) == 0

# Q971's primitive X-coordinate coefficient, now with independent Z.
k = 2 * t - d * h
CXZ = sp.expand(
    d * h * p**2
    + e**2 * (u**2 * k - 12 * t * (x1 + r) * (Z + F0))
)
denXZ = sp.expand(d * Z * e**2 * (u**2 - 4 * h * Z))

# The natural curve derivation has delta(x1)=1 and delta(Z)=u.
def delta(expr: sp.Expr) -> sp.Expr:
    return sp.expand(sp.diff(expr, x1) + u * sp.diff(expr, Z))


wronskian_num = sp.expand(denXZ * delta(CXZ) - CXZ * delta(denXZ))
wronskian_q, wronskian_rem = sp.div(
    sp.Poly(wronskian_num, Z, x1, A, r, domain=sp.QQ),
    sp.Poly(e, Z, x1, A, r, domain=sp.QQ),
)
assert wronskian_rem.is_zero
CY_wronskian = sp.expand(wronskian_q.as_expr())
wronskian_difference = sp.factor(sp.expand(CYZ - CY_wronskian))

gcd_CY_CX = sp.factor(sp.gcd(sp.Poly(CYZ, Z, x1, A, r), sp.Poly(CXZ, Z, x1, A, r)).as_expr())


# ---------------------------------------------------------------------------
# 5. Reproducible report
# ---------------------------------------------------------------------------
print("## Q990 exact result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- reduced denominator scale for standard Y: `{scale_std}`")
print(f"- reduced denominator scale for negAddY: `{scale_neg}`")
print(f"- raw/reduced standard-numerator multiplier: `{sp.sstr(raw_multiplier_std, order='lex')}`")
print(f"- primitive standard numerator terms: `{term_count(N_std)}`")
print(f"- compact coefficient expanded terms: `{term_count(CYZ)}`")
print(f"- compact coefficient degree in Z: `{sp.degree(CYZ, Z)}`")
print(f"- compact coefficient SHA-256: `{digest(CYZ)}`")
print("- standard-coordinate identity: `N_std = CY * (z - F0)` verified exactly")
print("- Mathlib identity: `N_neg = (-CY) * (z - F0)` verified exactly")
print("- original hypotheses: `N_neg = (-CY)*hcurve1 + (-CY)*htors` verified exactly")
print()
print("## Exact factorization over QQ[x1,A,r,Z]")
print()
print(f"- content: `{content_CY}`")
print(f"- nonconstant factor count: `{len(factors_CY)}`")
for index, (factor, exponent) in enumerate(factors_CY, start=1):
    print(f"- factor {index}: exponent `{exponent}`, expanded terms `{term_count(factor)}`")
    print(f"  - `{sp.sstr(factor, order='lex')}`")
print(f"- gcd(CY, Q971_CX): `{sp.sstr(gcd_CY_CX, order='lex')}`")
print()
print("## Q971 derivation/Wronskian probe")
print()
print("The candidate `(denX*delta(CX) - CX*delta(denX))/e` is polynomial.")
print(f"- exact difference `CY - candidate`: `{sp.sstr(wronskian_difference, order='lex')}`")
print()
print("## Compact coefficient definitions")
print()
print("```text")
print("z  = y1^2")
print("t  = 3*r^2 + A")
print("d  = x1 - r")
print("e  = d^2 - t")
print("u  = 3*x1^2 + A")
print("m  = x1*d + t")
print("p  = 3*m^2 + (A - 5*t)*d^2")
print("h  = 2*x1 + r")
print("j  = m + 2*r*d")
print("F0 = x1^3 + A*x1 - r^3 - A*r")
print()
print("b1 = d^2*e^3*u^5*(7*x1 + 2*r)")
print("     - 3*d*e^2*p*j*u^4")
print("     - 2*d^2*p^3*u^2*h")
print()
print("b2 = -2*d^2*e^3*u^3*(2*(h^2 - t) + 12*x1*h + u)")
print("     + 24*d*e^2*p*j*u^2*h")
print("     + 4*d^2*p^3*h^2")
print("     + 2*e^4*u^4")
print()
print("b3 = 16*d^2*e^3*u*(3*x1*(h^2 - t) + u*h)")
print("     - 48*d*e^2*p*j*h^2")
print("     - 16*e^4*u^2*h")
print()
print("b4 = 32*t*e^3*(d^2 - h^2)")
print()
print("CY = b1")
print("     + b2*(z + F0)")
print("     + b3*(z^2 + z*F0 + F0^2)")
print("     + b4*(z^3 + z^2*F0 + z*F0^2 + F0^3)")
print("```")
print()
print("For the requested `LHS - RHS` with Mathlib `negAddY`:")
print()
print("```text")
print("c1 = c2 = -CY")
print("```")
