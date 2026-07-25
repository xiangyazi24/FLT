#!/usr/bin/env python3
"""Q996: exact Vélu doubling-X denominator audit.

This script deliberately separates two operations that are easy to conflate:

* field/common-denominator clearing: the normalization matched by Lean's
  `field_simp` after rewriting x3-r = D3/(4*y1^2);
* literal side cross multiplication: den(lhs)*den(rhs).

Both are exact polynomial multiples of the Q971 primitive numerator N.
"""

from __future__ import annotations

import sympy as sp


# ---------------------------------------------------------------------------
# Full rational doubling X-coordinate identity
# ---------------------------------------------------------------------------
x1, y1, A, B, r = sp.symbols("x1 y1 A B r")

t = 3 * r**2 + A
Ap = A - 5 * t
Bp = B - 7 * r * t  # retained for the complete quotient-curve setup

ell = (3 * x1**2 + A) / (2 * y1)
x3 = ell**2 - 2 * x1

X1p = x1 + t / (x1 - r)
Y1p = y1 * ((x1 - r) ** 2 - t) / (x1 - r) ** 2
ellp = (3 * X1p**2 + Ap) / (2 * Y1p)
X3p = ellp**2 - 2 * X1p

lhs = x3 + t / (x3 - r)
rhs = X3p
diff = lhs - rhs


# ---------------------------------------------------------------------------
# Q971 compact notation, primitive numerator, and primitive certificate
# ---------------------------------------------------------------------------
z = y1**2
d = x1 - r
e = d**2 - t
u = 3 * x1**2 + A
m = x1 * d + t
p = 3 * m**2 + (A - 5 * t) * d**2
h = 2 * x1 + r
q = 2 * t - d * h
F0 = x1**3 + A * x1 - r**3 - A * r
D3 = u**2 - 4 * h * z

primitive_den = d * z * e**2 * D3

reduced = sp.cancel(sp.together(diff))
num_cas, den_cas = sp.fraction(reduced)
unit = sp.cancel(den_cas / primitive_den)
assert not unit.free_symbols and unit != 0
N = sp.expand(num_cas / unit)
assert sp.cancel(diff - N / primitive_den) == 0

C = sp.expand(
    d * h * p**2
    + e**2 * (u**2 * q - 12 * t * (x1 + r) * (z + F0))
)
assert sp.expand(N - C * (z - F0)) == 0

hcurve1 = z - x1**3 - A * x1 - B
htors = r**3 + A * r + B
assert sp.expand((z - F0) - (hcurve1 + htors)) == 0
assert B not in C.free_symbols
assert sp.expand(N - C * hcurve1 - C * htors) == 0


# ---------------------------------------------------------------------------
# A. Lean/field_simp common-denominator normalization
# ---------------------------------------------------------------------------
# Exact compact identities used by the denominator ledger.
assert sp.cancel(x3 - r - D3 / (4 * z)) == 0
assert sp.cancel(X1p - m / d) == 0
assert sp.cancel(Y1p - y1 * e / d**2) == 0
assert sp.cancel(ellp - p / (2 * y1 * e)) == 0

# After those normalizations, the top-level denominator LCM, retaining the
# integer content 4, is 4*z*d*e^2*D3 = 4*primitive_den.
field_den = 4 * primitive_den
field_num_rat = sp.cancel(field_den * diff)
field_num_expr, field_residual_den = sp.fraction(field_num_rat)
assert sp.expand(field_residual_den - 1) == 0
field_num = sp.expand(field_num_expr)
k_field = sp.factor(sp.cancel(field_num / N))
assert k_field == 4
assert sp.expand(field_num - 4 * N) == 0
assert sp.expand(field_num - (4 * C) * hcurve1 - (4 * C) * htors) == 0

# SymPy's uncancelled numerator(together(diff)) is the same 4*N normalization.
raw_num_expr, raw_den_expr = sp.fraction(sp.together(diff))
raw_num = sp.expand(raw_num_expr)
raw_den = sp.expand(raw_den_expr)
assert sp.expand(raw_num - field_num) == 0
assert sp.expand(raw_den - field_den) == 0


# ---------------------------------------------------------------------------
# B. Literal cross multiplication by den(lhs)*den(rhs)
# ---------------------------------------------------------------------------
lhs_num_expr, lhs_den_expr = sp.fraction(sp.together(lhs))
rhs_num_expr, rhs_den_expr = sp.fraction(sp.together(rhs))
lhs_num, lhs_den = sp.expand(lhs_num_expr), sp.expand(lhs_den_expr)
rhs_num, rhs_den = sp.expand(rhs_num_expr), sp.expand(rhs_den_expr)

product_den = sp.expand(lhs_den * rhs_den)
product_num = sp.expand(lhs_num * rhs_den - rhs_num * lhs_den)
k_product = sp.factor(sp.cancel(product_num / N))
assert sp.denom(sp.together(k_product)) == 1
assert sp.expand(k_product - 16 * z) == 0
assert sp.expand(product_den - 16 * z * primitive_den) == 0
assert sp.expand(product_num - 16 * z * N) == 0
assert sp.expand(
    product_num
    - (16 * z * C) * hcurve1
    - (16 * z * C) * htors
) == 0

# The product of the four top-level summand denominators gives the same result:
# diff = x3 + t/(x3-r) - ellp^2 + 2*X1p.
summands = [x3, t / (x3 - r), -ellp**2, 2 * X1p]
summand_dens = []
for term in summands:
    _, term_den = sp.fraction(sp.together(term))
    summand_dens.append(sp.expand(term_den))
summand_product_den = sp.expand(sp.prod(summand_dens))
assert sp.expand(summand_product_den - product_den) == 0
summand_product_num_rat = sp.cancel(summand_product_den * diff)
summand_product_num, summand_residual_den = sp.fraction(summand_product_num_rat)
assert sp.expand(summand_residual_den - 1) == 0
assert sp.expand(summand_product_num - product_num) == 0


# ---------------------------------------------------------------------------
# Reproducible report
# ---------------------------------------------------------------------------
print("SymPy", sp.__version__)
print("primitive_den =", sp.factor(primitive_den))
print("field_den     =", sp.factor(field_den))
print("lhs_den       =", sp.factor(lhs_den))
print("rhs_den       =", sp.factor(rhs_den))
print("product_den   =", sp.factor(product_den))
print("summand_dens  =", [sp.factor(v) for v in summand_dens])
print("k_field       =", sp.factor(k_field))
print("k_product     =", sp.factor(k_product))
print("field coefficient   =", sp.factor(4 * C))
print("product coefficient =", sp.factor(16 * z * C))
print("ALL ASSERTIONS PASSED")
