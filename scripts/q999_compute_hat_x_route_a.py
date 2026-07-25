#!/usr/bin/env python3
"""Q999: exact B-free Route A certificate and field_simp scaling audit.

This script verifies the full Vélu hat X-coordinate identity, the branch and
curve syzygies, the compact saturated identity

    u^2 * N0 = cE * E + cM * m,

and several exact denominator-clearing conventions.  It deliberately works
with the torsion and hat substitutions already made in the rational goal,
because the requested final linear_combination is allowed to use only hE and
hm.
"""

from __future__ import annotations

import hashlib
import sympy as sp


# ---------------------------------------------------------------------------
# 1. Original variables and full rational hat X-coordinate defect
# ---------------------------------------------------------------------------
x1, x2, y1, y2, A, B, r = sp.symbols("x1 x2 y1 y2 A B r")

u = x1 - r
v = x2 - r
s = x1 - x2                 # exactly u-v
U = u + v
T = x1 + x2 + r             # exactly 3*r+U
p = y1
q = y2
d = p - q

# Hat specialization.  This is exactly what Lean obtains from hA.
t_hat = u * v
A_hat = u * v - 3 * r**2
Ap_hat = A_hat - 5 * t_hat
B_hat = -(r**3 + A * r)      # requested B elimination, kept for audit

X1 = x1 + t_hat / u
Y1 = y1 * (u**2 - t_hat) / u**2
ellp = (3 * X1**2 + Ap_hat) / (2 * Y1)
target_double_x = ellp**2 - 2 * X1

ell = (y1 - y2) / (x1 - x2)
x3 = ell**2 - x1 - x2
source_phi_x = x3 + t_hat / (x3 - r)

# Q973 orientation: E'-side doubling X minus phi_X(source chord sum).
diff_hat = target_double_x - source_phi_x


# ---------------------------------------------------------------------------
# 2. Compact Q973 numerator and Route A certificate
# ---------------------------------------------------------------------------
z = d**2 - s**2 * T
g = s**2 + 2 * U * T

N0 = sp.expand(
    u**2 * g**2 * z
    - 4 * p**2 * d**2 * z
    - 4 * p**2 * U * s**2 * z
    - 4 * p**2 * u * v * s**4
)

mbranch = p * v + q * u
hbranch = p * v - q * u
E = p**2 - u**2 * T
K = u * d + U * p

cE = sp.expand(
    u**2 * s**6
    - 4 * z * (p**2 * U**2 + u**2 * U * (s**2 + U * T))
)
cM = sp.expand(K * (4 * z * p**2 - u**2 * s**4))

# Full rational identity and compact saturation certificate.
assert sp.cancel(diff_hat - N0 / (4 * p**2 * s**2 * z)) == 0
assert sp.expand(u**2 * N0 - cE * E - cM * mbranch) == 0
assert B not in cE.free_symbols and B not in cM.free_symbols
assert A not in cE.free_symbols and A not in cM.free_symbols


# ---------------------------------------------------------------------------
# 3. Verify hm, hE, hA, and hB certificates in the original polynomial ring
# ---------------------------------------------------------------------------
C1 = y1**2 - x1**3 - A * x1 - B
C2 = y2**2 - x2**3 - A * x2 - B
H = r**3 + A * r + B
G = u * v - (3 * r**2 + A)

branch_rhs = v**2 * C1 - u**2 * C2 + (v**2 - u**2) * H + u * v * s * G
assert sp.expand(hbranch * mbranch - branch_rhs) == 0
assert sp.expand(E - (C1 + H - u * G)) == 0
assert sp.expand((A - (u * v - 3 * r**2)) + G) == 0
assert sp.expand((B + r**3 + A * r) - H) == 0


# ---------------------------------------------------------------------------
# 4. Exact denominator-clearing multipliers for u^2 * diff_hat
# ---------------------------------------------------------------------------
primitive_num = sp.expand(u**2 * N0)
primitive_den = sp.expand(4 * p**2 * s**2 * z)
assert sp.cancel(u**2 * diff_hat - primitive_num / primitive_den) == 0


def exact_polynomial_multiplier(poly: sp.Expr, base: sp.Expr, label: str) -> sp.Expr:
    ratio = sp.factor(sp.cancel(poly / base))
    assert sp.denom(sp.together(ratio)) == 1, f"{label}: non-polynomial ratio {ratio}"
    assert sp.expand(poly - ratio * base) == 0, f"{label}: multiplier check failed"
    return ratio


# A. One whole-expression together, with no cancellation afterward.
whole_rat = sp.together(u**2 * diff_hat)
whole_num_expr, whole_den_expr = sp.fraction(whole_rat)
whole_num = sp.expand(whole_num_expr)
whole_den = sp.expand(whole_den_expr)
k_whole = exact_polynomial_multiplier(whole_num, primitive_num, "whole together")
assert sp.expand(whole_den - k_whole * primitive_den) == 0

# B. Product of the two fully combined side denominators.
left_scaled = u**2 * target_double_x
right_scaled = u**2 * source_phi_x
ln_expr, ld_expr = sp.fraction(sp.together(left_scaled))
rn_expr, rd_expr = sp.fraction(sp.together(right_scaled))
ln, ld = sp.expand(ln_expr), sp.expand(ld_expr)
rn, rd = sp.expand(rn_expr), sp.expand(rd_expr)
side_den = sp.expand(ld * rd)
side_num = sp.expand(ln * rd - rn * ld)
k_side = exact_polynomial_multiplier(side_num, primitive_num, "side product")
assert sp.expand(side_den - k_side * primitive_den) == 0

# C. Product of denominators of the four additive summands after distributing u^2.
summands = [u**2 * ellp**2, -2 * u**2 * X1, -u**2 * x3, -u**2 * t_hat / (x3 - r)]
summand_dens: list[sp.Expr] = []
for term in summands:
    _, den = sp.fraction(sp.together(term))
    summand_dens.append(sp.expand(den))
summand_den = sp.expand(sp.prod(summand_dens))
summand_num_rat = sp.cancel(summand_den * u**2 * diff_hat)
summand_num_expr, summand_residual_den = sp.fraction(summand_num_rat)
assert sp.expand(summand_residual_den - 1) == 0
summand_num = sp.expand(summand_num_expr)
k_summand = exact_polynomial_multiplier(summand_num, primitive_num, "summand product")
assert sp.expand(summand_den - k_summand * primitive_den) == 0

# Every scaled numerator has the requested two-hypothesis certificate.
for label, multiplier, scaled_num in (
    ("whole", k_whole, whole_num),
    ("side", k_side, side_num),
    ("summand", k_summand, summand_num),
):
    lhs_cert = sp.expand(multiplier * cE * E + multiplier * cM * mbranch)
    assert sp.expand(scaled_num - lhs_cert) == 0, label


# ---------------------------------------------------------------------------
# 5. Reproducible report
# ---------------------------------------------------------------------------
def term_count(expr: sp.Expr) -> int:
    e = sp.expand(expr)
    return 0 if e == 0 else len(e.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


print("# Q999 exact B-free Route A audit")
print()
print(f"- SymPy version: `{sp.__version__}`")
print("- full rational hat X identity: `verified`")
print("- branch-product certificate for hm: `verified`")
print("- hE, hA, and hB polynomial certificates: `verified`")
print("- compact identity `u^2*N0 = cE*E + cM*m`: `verified`")
print(f"- primitive `u^2*N0` terms: `{term_count(primitive_num)}`")
print(f"- primitive `u^2*N0` SHA-256: `{digest(primitive_num)}`")
print()
print("## Exact scaling factors relative to u^2*N0")
print()
print(f"- k_whole = `{sp.sstr(sp.factor(k_whole), order='lex')}`")
print(f"- k_side = `{sp.sstr(sp.factor(k_side), order='lex')}`")
print(f"- k_summand = `{sp.sstr(sp.factor(k_summand), order='lex')}`")
print()
print("## Exact denominators")
print()
print(f"- primitive: `{sp.sstr(sp.factor(primitive_den), order='lex')}`")
print(f"- whole together: `{sp.sstr(sp.factor(whole_den), order='lex')}`")
print(f"- left side: `{sp.sstr(sp.factor(ld), order='lex')}`")
print(f"- right side: `{sp.sstr(sp.factor(rd), order='lex')}`")
print(f"- side product: `{sp.sstr(sp.factor(side_den), order='lex')}`")
for i, den in enumerate(summand_dens, start=1):
    print(f"- summand {i}: `{sp.sstr(sp.factor(den), order='lex')}`")
print(f"- summand product: `{sp.sstr(sp.factor(summand_den), order='lex')}`")
print()
print("## Compact coefficients")
print()
print("```text")
print("u = x1-r; v = x2-r; s = x1-x2; U = u+v; T = x1+x2+r")
print("d = y1-y2; z = d^2-s^2*T; g = s^2+2*U*T")
print("K = u*d+U*y1")
print("cE = u^2*s^6 - 4*z*(y1^2*U^2 + u^2*U*(s^2+U*T))")
print("cM = K*(4*z*y1^2-u^2*s^4)")
print("```")
print()
print("## Candidate field_simp-scaled coefficients")
print()
print(f"- side-scaled cE multiplier: `{sp.sstr(sp.factor(k_side), order='lex')}`")
print(f"- side-scaled cM multiplier: `{sp.sstr(sp.factor(k_side), order='lex')}`")
print(f"- summand-scaled cE multiplier: `{sp.sstr(sp.factor(k_summand), order='lex')}`")
print(f"- summand-scaled cM multiplier: `{sp.sstr(sp.factor(k_summand), order='lex')}`")
