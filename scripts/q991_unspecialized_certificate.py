#!/usr/bin/env python3
"""Q991 certificate with A retained and `hat` used as a generator."""

from __future__ import annotations

import sympy as sp

import q991_hat_y_final as q

u, v, p = q.u, q.v, q.p
A, r = q.A, q.r

# Substitute only the selected Y branch and translated x coordinates; retain A.
branch_sub = {
    q.x1: r+u,
    q.x2: r+v,
    q.y1: p,
    q.y2: -p*v/u,
}
D0 = q.std_defect.subs(branch_sub, simultaneous=True)

raw_rat = sp.together(D0)
raw_num_expr, raw_den_expr = sp.fraction(raw_rat)
raw_num = sp.expand(raw_num_expr)
raw_den = sp.factor(raw_den_expr)

red_rat = sp.cancel(raw_rat)
red_num_expr, red_den_expr = sp.fraction(red_rat)
red_num = sp.expand(red_num_expr)
red_den = sp.factor(red_den_expr)

raw_multiplier = sp.factor(sp.cancel(raw_num/red_num))
assert sp.denom(sp.together(raw_multiplier)) == 1
assert sp.expand(raw_num-raw_multiplier*red_num) == 0

# F is hcurve1 + htors in translated coordinates. G is the hat equation.
F = p**2-u*(u**2+3*r*u+3*r**2+A)
G = u*v-(3*r**2+A)

# Divide first by the monic curve equation in p, then by the linear hat equation
# in A.  This gives an exact linear_combination certificate.
qF, remF = sp.div(red_num, F, p)
qG, remG = sp.div(sp.expand(remF), G, A)
qF = sp.expand(qF)
qG = sp.expand(qG)
remG = sp.expand(remG)

assert remG == 0
assert sp.expand(red_num-qF*F-qG*G) == 0

# Original-coordinate generators.
C1 = q.y1**2-q.x1**3-A*q.x1-q.B
H = r**3+A*r+q.B
G_original = (q.x1-r)*(q.x2-r)-(3*r**2+A)
assert sp.expand(F.subs({u:q.x1-r, p:q.y1})-(C1+H)) == 0
assert sp.expand(G.subs({u:q.x1-r, v:q.x2-r})-G_original) == 0

# Compare with the compact certificate after actually imposing hat.
hatA = u*v-3*r**2
red_num_hat = sp.expand(red_num.subs(A, hatA))
qF_hat = sp.expand(qF.subs(A, hatA))
qG_hat = sp.expand(qG.subs(A, hatA))

hat_scale = sp.factor(sp.cancel(red_num_hat/(q.qYfull*q.E)))
assert sp.denom(sp.together(hat_scale)) == 1
assert sp.expand(red_num_hat-hat_scale*q.qYfull*q.E) == 0
assert sp.expand(qF_hat-hat_scale*q.qYfull) == 0

# Raw coefficients are the reduced coefficients times the exact clearing scale.
raw_qF = sp.expand(raw_multiplier*qF)
raw_qG = sp.expand(raw_multiplier*qG)
assert sp.expand(raw_num-raw_qF*F-raw_qG*G) == 0


def nterms(expr: sp.Expr) -> int:
    e = sp.expand(expr)
    return 0 if e == 0 else len(e.as_ordered_terms())


print()
print("Q991 unspecialized-A certificate")
print("================================")
print(f"reduced numerator terms: {nterms(red_num)}")
print(f"qF terms: {nterms(qF)}")
print(f"qG terms: {nterms(qG)}")
print(f"raw/reduced multiplier: {sp.sstr(raw_multiplier, order='lex')}")
print(f"hat-specialization scale: {sp.sstr(hat_scale, order='lex')}")
print("verified: red_num = qF*F + qG*G")
print("verified: F = hcurve1 + htors")
print()
print("qF factorization:")
print(sp.sstr(sp.factor(qF), order="lex"))
print()
print("qG factorization:")
print(sp.sstr(sp.factor(qG), order="lex"))
