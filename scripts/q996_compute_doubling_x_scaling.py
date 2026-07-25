#!/usr/bin/env python3
"""Q996: exact denominator-scaling audit for the Vélu doubling X identity.

The script keeps four exact numerator conventions:

1. primitive: the Q971 normalization N/den;
2. together: numerator(together(lhs-rhs));
3. side-product: cross multiplication by den(lhs)*den(rhs), where each side
   is first combined without cancellation;
4. summand-product: multiplication by the product of the four top-level
   summand denominators in lhs-rhs.

Every convention is proved to be an exact polynomial multiple of Q971's N,
and the corresponding equal hcurve1/htors coefficient is printed.
"""

from __future__ import annotations

import hashlib
import sympy as sp


# ---------------------------------------------------------------------------
# 1. Full rational identity
# ---------------------------------------------------------------------------
x1, y1, A, r, B = sp.symbols("x1 y1 A r B")

t = 3 * r**2 + A
Ap = A - 5 * t
Bp = B - 7 * r * t  # retained for the complete quotient-curve setup

ell = (3 * x1**2 + A) / (2 * y1)
x3 = ell**2 - 2 * x1
lhs = x3 + t / (x3 - r)

X1p = x1 + t / (x1 - r)
Y1p = y1 * ((x1 - r) ** 2 - t) / (x1 - r) ** 2
ellp = (3 * X1p**2 + Ap) / (2 * Y1p)
rhs = ellp**2 - 2 * X1p

diff = lhs - rhs


# ---------------------------------------------------------------------------
# 2. Q971 primitive normalization and certificate
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

reduced_rat = sp.cancel(sp.together(diff))
num_cas, den_cas = sp.fraction(reduced_rat)
normalization_unit = sp.cancel(den_cas / primitive_den)
assert not normalization_unit.free_symbols and normalization_unit != 0
N = sp.expand(num_cas / normalization_unit)
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
# 3. Three unreduced cross-multiplication conventions
# ---------------------------------------------------------------------------
def exact_polynomial_multiplier(poly: sp.Expr, base: sp.Expr, label: str) -> sp.Expr:
    ratio = sp.factor(sp.cancel(poly / base))
    assert sp.denom(sp.together(ratio)) == 1, f"{label}: non-polynomial ratio {ratio}"
    assert sp.expand(poly - ratio * base) == 0, f"{label}: multiplier check failed"
    return ratio


# A. SymPy's uncancelled whole-expression `together` numerator.
whole_together = sp.together(diff)
whole_num_expr, whole_den_expr = sp.fraction(whole_together)
whole_num = sp.expand(whole_num_expr)
whole_den = sp.expand(whole_den_expr)
k_whole = exact_polynomial_multiplier(whole_num, N, "whole together")
assert sp.expand(whole_den - k_whole * primitive_den) == 0
assert sp.cancel(diff - whole_num / whole_den) == 0

# B. Product of the two fully combined side denominators.
lhs_num_expr, lhs_den_expr = sp.fraction(sp.together(lhs))
rhs_num_expr, rhs_den_expr = sp.fraction(sp.together(rhs))
lhs_num, lhs_den = sp.expand(lhs_num_expr), sp.expand(lhs_den_expr)
rhs_num, rhs_den = sp.expand(rhs_num_expr), sp.expand(rhs_den_expr)
side_product_den = sp.expand(lhs_den * rhs_den)
side_product_num = sp.expand(lhs_num * rhs_den - rhs_num * lhs_den)
k_side = exact_polynomial_multiplier(side_product_num, N, "side product")
assert sp.expand(side_product_den - k_side * primitive_den) == 0
assert sp.cancel(diff - side_product_num / side_product_den) == 0

# C. Literal product of the four top-level summand denominators in lhs-rhs.
#    diff = x3 + t/(x3-r) - ellp^2 + 2*X1p.
summands = [x3, t / (x3 - r), -ellp**2, 2 * X1p]
summand_denominators: list[sp.Expr] = []
for term in summands:
    _, term_den = sp.fraction(sp.together(term))
    summand_denominators.append(sp.expand(term_den))

summand_product_den = sp.expand(sp.prod(summand_denominators))
summand_product_num_rat = sp.cancel(summand_product_den * diff)
summand_product_num_expr, residual_den = sp.fraction(summand_product_num_rat)
assert sp.expand(residual_den - 1) == 0
summand_product_num = sp.expand(summand_product_num_expr)
k_summand = exact_polynomial_multiplier(summand_product_num, N, "summand product")
assert sp.expand(summand_product_den - k_summand * primitive_den) == 0
assert sp.cancel(diff - summand_product_num / summand_product_den) == 0

# All scaled coefficients give exact original-hypothesis certificates.
for label, multiplier, scaled_num in (
    ("whole", k_whole, whole_num),
    ("side", k_side, side_product_num),
    ("summand", k_summand, summand_product_num),
):
    scaled_C = sp.expand(multiplier * C)
    assert B not in scaled_C.free_symbols
    assert sp.expand(scaled_num - scaled_C * hcurve1 - scaled_C * htors) == 0, label


# ---------------------------------------------------------------------------
# 4. Reproducible report
# ---------------------------------------------------------------------------
def term_count(expr: sp.Expr) -> int:
    expanded = sp.expand(expr)
    return 0 if expanded == 0 else len(expanded.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


print("## Q996 exact scaling result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- primitive normalization unit: `{sp.sstr(normalization_unit, order='lex')}`")
print(f"- primitive numerator terms: `{term_count(N)}`")
print(f"- primitive numerator SHA-256: `{digest(N)}`")
print()
print("### Exact denominators")
print()
print(f"- primitive denominator: `{sp.sstr(sp.factor(primitive_den), order='lex')}`")
print(f"- whole-together denominator: `{sp.sstr(sp.factor(whole_den), order='lex')}`")
print(f"- left-side denominator: `{sp.sstr(sp.factor(lhs_den), order='lex')}`")
print(f"- right-side denominator: `{sp.sstr(sp.factor(rhs_den), order='lex')}`")
print(f"- side-product denominator: `{sp.sstr(sp.factor(side_product_den), order='lex')}`")
for index, term_den in enumerate(summand_denominators, start=1):
    print(f"- summand denominator {index}: `{sp.sstr(sp.factor(term_den), order='lex')}`")
print(f"- summand-product denominator: `{sp.sstr(sp.factor(summand_product_den), order='lex')}`")
print()
print("### Exact scaling factors relative to Q971 N")
print()
print(f"- k_whole = `{sp.sstr(sp.factor(k_whole), order='lex')}`")
print(f"- k_side = `{sp.sstr(sp.factor(k_side), order='lex')}`")
print(f"- k_summand = `{sp.sstr(sp.factor(k_summand), order='lex')}`")
print()
print("### Verification")
print()
print("- whole_num = k_whole * N: `True`")
print("- whole_den = k_whole * primitive_den: `True`")
print("- side_product_num = k_side * N: `True`")
print("- side_product_den = k_side * primitive_den: `True`")
print("- summand_product_num = k_summand * N: `True`")
print("- summand_product_den = k_summand * primitive_den: `True`")
print("- every scaled numerator equals (k*C)*hcurve1 + (k*C)*htors: `True`")
print()
print("### Compact Q971 coefficient")
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
print("q  = 2*t - d*h")
print("F0 = x1^3 + A*x1 - r^3 - A*r")
print("C  = d*h*p^2 + e^2*(u^2*q - 12*t*(x1+r)*(z+F0))")
print("```")
print()
print("### Exact scaled coefficients")
print()
print(f"- whole-together coefficient factorization: `{sp.sstr(sp.factor(k_whole * C), order='lex')}`")
print(f"- side-product coefficient factorization: `{sp.sstr(sp.factor(k_side * C), order='lex')}`")
print(f"- summand-product coefficient factorization: `{sp.sstr(sp.factor(k_summand * C), order='lex')}`")
