#!/usr/bin/env python3
"""Q991: final self-contained SymPy audit for the hat Vélu Y identity.

It constructs the full source-chord / target-doubling identity, imposes

    (x1-r)(x2-r) = 3*r^2 + A,
    y2 = -y1*(x2-r)/(x1-r),

checks both the uncancelled and reduced numerators, and gives compact
linear-combination coefficients for the remaining curve equation.
"""

from __future__ import annotations

import sympy as sp

# ---------------------------------------------------------------------------
# 1. Full rational identity in original coordinates
# ---------------------------------------------------------------------------
x1, x2, y1, y2, A, B, r = sp.symbols("x1 x2 y1 y2 A B r")
t = 3*r**2 + A
Aprime = A - 5*t
Bprime = B - 7*r*t  # recorded for the quotient curve; Y addition uses Aprime


def phiX(x: sp.Expr) -> sp.Expr:
    return x + t/(x-r)


def phiY(x: sp.Expr, y: sp.Expr) -> sp.Expr:
    return y*((x-r)**2-t)/(x-r)**2


# Source side: chord addition.
ell = (y1-y2)/(x1-x2)
x3 = ell**2-x1-x2
addY = ell*(x1-x3)-y1
negAddY = -ell*(x1-x3)+y1

# Hat target side: X1'=X2', hence tangent doubling at phi(P1).
X1p = phiX(x1)
Y1p = phiY(x1, y1)
ellp = (3*X1p**2+Aprime)/(2*Y1p)
X3p = ellp**2-2*X1p
addYp = ellp*(X1p-X3p)-Y1p
negAddYp = -ellp*(X1p-X3p)+Y1p

std_defect = phiY(x3, addY)-addYp
neg_defect = phiY(x3, negAddY)-negAddYp
assert sp.cancel(sp.together(neg_defect+std_defect)) == 0

# ---------------------------------------------------------------------------
# 2. Impose hat and the selected branch parametrically
# ---------------------------------------------------------------------------
u, v, p = sp.symbols("u v p")
hat_branch_sub = {
    x1: r+u,
    x2: r+v,
    y1: p,
    y2: -p*v/u,
    A: u*v-3*r**2,
}

Dstd0 = std_defect.subs(hat_branch_sub, simultaneous=True)
Dneg0 = neg_defect.subs(hat_branch_sub, simultaneous=True)
assert sp.cancel(sp.together(Dneg0+Dstd0)) == 0

raw_rat = sp.together(Dstd0)
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
assert sp.expand(raw_num*red_den-red_num*raw_den) == 0

is_pure_ring_identity = sp.Poly(
    red_num, p, u, v, r, domain=sp.QQ
).is_zero
assert not is_pure_ring_identity

# ---------------------------------------------------------------------------
# 3. Compact translated certificate
# ---------------------------------------------------------------------------
s = u-v
U = u+v
T = 3*r+U
E = p**2-u**2*T

g = s**2+2*U*T
z = p**2*U**2-u**2*s**2*T  # x3-r = z/(u^2*s^2)

qYline = (
    (z-u**3*s**2)
    * (z-u**2*v*s**2)
    * (u**2*g*s**2-2*p**2*U**3)
)

qX = u**4*s**6 - 4*z*(p**2*U**2 + u**2*U*(s**2+U*T))
qYfull = 4*p**2*qYline + u**2*z*g*qX

expected_red_den = 8*p**3*u**3*s**3*z**2
assert sp.expand(red_den-expected_red_den) == 0
assert sp.expand(red_num-qYfull*E) == 0

q_div, rem_div = sp.div(red_num, E, p)
assert sp.expand(rem_div) == 0
assert sp.expand(q_div-qYfull) == 0

raw_coeff = sp.factor(raw_multiplier*qYfull)
assert sp.expand(raw_num-raw_coeff*E) == 0

# ---------------------------------------------------------------------------
# 4. Check the decomposition through the already-proved hat-X identity
# ---------------------------------------------------------------------------
lam = p*U/(u*s)
w = lam**2-T
P = p*s/u
mu = u*g/(2*p*s)
W = mu**2-(3*r+2*U)
y3 = lam*(u-w)-p
psi_w = w+u*v/w

line_defect = (
    y3*(w**2-u*v)/w**2
    - (mu*(U-psi_w)-P)
)
x_defect = W-psi_w
manual_full_defect = y3*(w**2-u*v)/w**2-(mu*(U-W)-P)

assert sp.cancel(sp.together(Dstd0-manual_full_defect)) == 0
assert sp.cancel(sp.together(
    manual_full_defect-line_defect-mu*x_defect
)) == 0
assert sp.cancel(sp.together(
    line_defect-qYline*E/(2*p*u**3*s**3*z**2)
)) == 0
assert sp.cancel(sp.together(
    x_defect-qX*E/(4*p**2*u**2*s**2*z)
)) == 0

# ---------------------------------------------------------------------------
# 5. Translate E to the original hypotheses
# ---------------------------------------------------------------------------
C1 = y1**2-x1**3-A*x1-B
C2 = y2**2-x2**3-A*x2-B
H = r**3+A*r+B
G = (x1-r)*(x2-r)-(3*r**2+A)
E_original = y1**2-(x1-r)**2*(x1+x2+r)
assert sp.expand(E_original-(C1+H-(x1-r)*G)) == 0

back = {u: x1-r, v: x2-r, p: y1}
qYfull_original = sp.expand(qYfull.subs(back, simultaneous=True))

c_curve1 = qYfull_original
c_curve2 = sp.Integer(0)
c_tors = qYfull_original
c_hat = -(x1-r)*qYfull_original
assert sp.expand(
    qYfull_original*E_original
    - c_curve1*C1
    - c_curve2*C2
    - c_tors*H
    - c_hat*G
) == 0

# ---------------------------------------------------------------------------
# 6. Reproducible report
# ---------------------------------------------------------------------------
def nterms(expr: sp.Expr) -> int:
    e = sp.expand(expr)
    return 0 if e == 0 else len(e.as_ordered_terms())


print("Q991 exact SymPy result")
print("========================")
print(f"SymPy version: {sp.__version__}")
print(f"pure ring identity after only hat + branch: {is_pure_ring_identity}")
print(f"reduced numerator terms: {nterms(red_num)}")
print(f"compact qYfull expanded terms: {nterms(qYfull)}")
print(f"raw/reduced multiplier: {sp.sstr(raw_multiplier, order='lex')}")
print("verified: red_num = qYfull * E")
print("verified: raw_num = raw_multiplier * qYfull * E")
print()
print("u = x1-r; v = x2-r; s = u-v; U = u+v; T = 3*r+U; p = y1")
print("E = p^2-u^2*T")
print("g = s^2+2*U*T")
print("z = p^2*U^2-u^2*s^2*T")
print("qYline = (z-u^3*s^2)*(z-u^2*v*s^2)*(u^2*g*s^2-2*p^2*U^3)")
print("qX = u^4*s^6-4*z*(p^2*U^2+u^2*U*(s^2+U*T))")
print("qYfull = 4*p^2*qYline+u^2*z*g*qX")
print("red_den = 8*p^3*u^3*s^3*z^2")
print()
print("E_original = C1 + H - (x1-r)*G")
print("standard-addY reduced-numerator coefficients:")
print("  hcurve1: qYfull_original")
print("  hcurve2: 0")
print("  htors:   qYfull_original")
print("  hat:    -(x1-r)*qYfull_original")
print("For negAddY or the opposite defect orientation, negate all coefficients.")
