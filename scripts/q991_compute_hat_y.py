#!/usr/bin/env python3
"""Q991: exact SymPy audit for the hat Vélu Y-coordinate identity.

The script uses the standard affine sum Y-coordinate
    addY = ell * (x1 - x3) - y1.
It also checks Mathlib's negated convention for sign control.

After imposing
    (x1-r)(x2-r) = 3*r^2 + A
and
    y2 = -y1*(x2-r)/(x1-r),
we test whether the full rational defect is identically zero.  If not, we
factor its reduced and uncancelled numerators by the remaining translated
curve equation
    E = y1^2 - (x1-r)^2*(x1+x2+r).
"""

from __future__ import annotations

import hashlib
import sympy as sp


# ---------------------------------------------------------------------------
# 1. Full original-coordinate identity
# ---------------------------------------------------------------------------
x1, x2, y1, y2, A, B, r = sp.symbols("x1 x2 y1 y2 A B r")
t = 3*r**2 + A
Ap = A - 5*t
Bp = B - 7*r*t  # included to record the quotient curve completely


def phiX(x: sp.Expr) -> sp.Expr:
    return x + t/(x-r)


def phiY(x: sp.Expr, y: sp.Expr) -> sp.Expr:
    return y*((x-r)**2-t)/(x-r)**2


ell = (y1-y2)/(x1-x2)
x3 = ell**2-x1-x2
addY = ell*(x1-x3)-y1
negAddY = -ell*(x1-x3)+y1

X1p = phiX(x1)
Y1p = phiY(x1, y1)
ellp = (3*X1p**2+Ap)/(2*Y1p)
X3p = ellp**2-2*X1p
addYp = ellp*(X1p-X3p)-Y1p
negAddYp = -ellp*(X1p-X3p)+Y1p

lhs_std = phiY(x3, addY)
rhs_std = addYp
defect_std = lhs_std-rhs_std

defect_neg = phiY(x3, negAddY)-negAddYp
assert sp.cancel(sp.together(defect_neg+defect_std)) == 0


# ---------------------------------------------------------------------------
# 2. Parametric imposition of hat and the selected equal-image branch
# ---------------------------------------------------------------------------
u, v, p = sp.symbols("u v p")
hat_sub = {
    x1: r+u,
    x2: r+v,
    y1: p,
    y2: -p*v/u,
    A: u*v-3*r**2,
}

sub_std = defect_std.subs(hat_sub, simultaneous=True)
sub_neg = defect_neg.subs(hat_sub, simultaneous=True)

# Translated abbreviations.
aa = 3*r
ss = u-v
UU = u+v
TT = aa+UU
EE = p**2-u**2*TT

gg = ss**2+2*UU*TT
lam = p*UU/(u*ss)
w3 = lam**2-TT
Pp = p*ss/u
mu = u*gg/(2*p*ss)
W3 = mu**2-(aa+2*UU)
y3 = lam*(u-w3)-p
Y3 = mu*(UU-W3)-Pp
manual_std = y3*(w3**2-u*v)/w3**2-Y3

assert sp.cancel(sp.together(sub_std-manual_std)) == 0
assert sp.cancel(sp.together(sub_neg+sub_std)) == 0


# ---------------------------------------------------------------------------
# 3. Reduced and uncancelled numerator tests
# ---------------------------------------------------------------------------
raw_rat = sp.together(sub_std)
raw_num_expr, raw_den_expr = sp.fraction(raw_rat)
raw_num = sp.expand(raw_num_expr)
raw_den = sp.factor(raw_den_expr)

red_rat = sp.cancel(raw_rat)
red_num_expr, red_den_expr = sp.fraction(red_rat)
red_num = sp.expand(red_num_expr)
red_den = sp.factor(red_den_expr)

assert sp.expand(raw_num*red_den-red_num*raw_den) == 0
raw_multiplier = sp.factor(sp.cancel(raw_num/red_num))
assert sp.denom(sp.together(raw_multiplier)) == 1
assert sp.expand(raw_num-raw_multiplier*red_num) == 0

pure_polynomial_zero = sp.Poly(red_num, p, u, v, r, domain=sp.QQ).is_zero
assert not pure_polynomial_zero

red_coeff = sp.factor(sp.cancel(red_num/EE))
assert sp.denom(sp.together(red_coeff)) == 1
assert sp.expand(red_num-red_coeff*EE) == 0

raw_coeff = sp.factor(raw_multiplier*red_coeff)
assert sp.expand(raw_num-raw_coeff*EE) == 0

# The negAddY orientation is exactly the negative certificate.
neg_red = sp.cancel(sp.together(sub_neg))
neg_num_expr, neg_den_expr = sp.fraction(neg_red)
assert sp.factor(neg_den_expr/red_den) in (1, -1)
neg_scale = sp.cancel(neg_den_expr/red_den)
neg_num_normalized = sp.expand(neg_num_expr/neg_scale)
assert sp.expand(neg_num_normalized+red_num) == 0


# ---------------------------------------------------------------------------
# 4. Original-hypothesis translation
# ---------------------------------------------------------------------------
C1 = y1**2-x1**3-A*x1-B
C2 = y2**2-x2**3-A*x2-B
H = r**3+A*r+B
G = (x1-r)*(x2-r)-(3*r**2+A)
E_original = y1**2-(x1-r)**2*(x1+x2+r)
assert sp.expand(E_original-(C1+H-(x1-r)*G)) == 0

# Reverse translated variables in the coefficient.  This coefficient is meant
# after the hat rewrite A=(x1-r)(x2-r)-3r^2, so it contains no independent A.
back = {u: x1-r, v: x2-r, p: y1}
red_coeff_original = sp.factor(red_coeff.subs(back, simultaneous=True))
raw_coeff_original = sp.factor(raw_coeff.subs(back, simultaneous=True))

# Exact certificate in the original polynomial ring for the hat-specialized
# numerator: coefficient * (C1+H-(x1-r)G).
assert sp.expand(
    red_coeff_original*E_original
    - red_coeff_original*C1
    - red_coeff_original*H
    + red_coeff_original*(x1-r)*G
) == 0


# ---------------------------------------------------------------------------
# 5. Optional decomposition through the already-proved hat X identity
# ---------------------------------------------------------------------------
psi_w = w3+u*v/w3
x_defect = W3-psi_w
line_defect = (
    y3*(w3**2-u*v)/w3**2
    - (mu*(UU-psi_w)-Pp)
)
assert sp.cancel(sp.together(manual_std-line_defect-mu*x_defect)) == 0

line_red = sp.cancel(sp.together(line_defect))
line_num_expr, line_den_expr = sp.fraction(line_red)
line_num = sp.expand(line_num_expr)
line_den = sp.factor(line_den_expr)
line_coeff = sp.factor(sp.cancel(line_num/EE))
assert sp.denom(sp.together(line_coeff)) == 1
assert sp.expand(line_num-line_coeff*EE) == 0


# ---------------------------------------------------------------------------
# 6. Reporting helpers
# ---------------------------------------------------------------------------
def term_count(expr: sp.Expr) -> int:
    expr = sp.expand(expr)
    return 0 if expr == 0 else len(expr.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def print_factor_list(label: str, expr: sp.Expr) -> None:
    content, factors = sp.factor_list(expr)
    print(f"- {label} content: `{content}`")
    print(f"- {label} nonconstant factors: `{len(factors)}`")
    for i, (factor, exponent) in enumerate(factors, start=1):
        print(
            f"  - factor {i}, exponent `{exponent}`, terms `{term_count(factor)}`: "
            f"`{sp.sstr(factor, order='lex')}`"
        )


print("## Q991 exact result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- after hat + y2 substitution, reduced numerator identically zero: `{pure_polynomial_zero}`")
print(f"- reduced numerator terms: `{term_count(red_num)}`")
print(f"- reduced coefficient terms: `{term_count(red_coeff)}`")
print(f"- raw numerator terms: `{term_count(raw_num)}`")
print(f"- raw/reduced multiplier: `{sp.sstr(raw_multiplier, order='lex')}`")
print(f"- reduced numerator SHA-256: `{digest(red_num)}`")
print(f"- reduced coefficient SHA-256: `{digest(red_coeff)}`")
print("- exact reduced identity: `red_num = red_coeff * E` verified")
print("- exact raw identity: `raw_num = raw_coeff * E` verified")
print("- standard addY and Mathlib negAddY defects are exact negatives")
print()
print("Translated variables:")
print()
print("```text")
print("u = x1-r")
print("v = x2-r")
print("s = u-v")
print("U = u+v")
print("T = 3*r+U")
print("p = y1")
print("E = p^2-u^2*T")
print("```")
print()
print("Reduced denominator:")
print()
print("```text")
print(sp.sstr(red_den, order="lex"))
print("```")
print()
print("Uncancelled together denominator:")
print()
print("```text")
print(sp.sstr(raw_den, order="lex"))
print("```")
print()
print("Reduced coefficient factorization:")
print()
print_factor_list("red_coeff", red_coeff)
print()
print("Raw coefficient factorization:")
print()
print_factor_list("raw_coeff", raw_coeff)
print()
print("Reduced coefficient as one factored expression:")
print()
print("```text")
print(sp.sstr(red_coeff, order="lex"))
print("```")
print()
print("Raw coefficient as one factored expression:")
print()
print("```text")
print(sp.sstr(raw_coeff, order="lex"))
print("```")
print()
print("After first rewriting the target X-coordinate by the hat X identity,")
print("the remaining line defect has:")
print()
print(f"- reduced line numerator terms: `{term_count(line_num)}`")
print(f"- line coefficient terms: `{term_count(line_coeff)}`")
print("- exact identity: `line_num = line_coeff * E` verified")
print()
print("Line-only reduced denominator:")
print()
print("```text")
print(sp.sstr(line_den, order="lex"))
print("```")
print()
print("Line-only coefficient factorization:")
print()
print_factor_list("line_coeff", line_coeff)
print()
print("Line-only coefficient as one factored expression:")
print()
print("```text")
print(sp.sstr(line_coeff, order="lex"))
print("```")
print()
print("Original-coordinate hypothesis identity:")
print()
print("```text")
print("E_original = y1^2-(x1-r)^2*(x1+x2+r)")
print("           = C1 + H - (x1-r)*G")
print("```")
print()
print("Thus, for the standard `LHS-RHS` reduced numerator, use")
print("`red_coeff_original` on `hcurve1`, the same coefficient on `htors`,")
print("and `-(x1-r)*red_coeff_original` on `hat`.  Negate all three for")
print("Mathlib `negAddY` or for the opposite defect orientation.")
