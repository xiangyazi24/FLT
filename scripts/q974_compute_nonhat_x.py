#!/usr/bin/env python3
"""Q974: exact SymPy certificate for the non-hat Vélu X-coordinate identity.

Two denominator-clearing conventions are reported:

1. reduced: numerator(cancel(together(lhs - rhs)));
2. raw:     numerator(together(lhs - rhs)).

The raw numerator is checked to be an exact polynomial multiple of the reduced
one. The rational identity itself is formed after eliminating
    B = -(r^3 + A*r).
For the final Lean certificate we retain an independent symbol B and use
    g_i = hcurve_i + htors.
Therefore, if numerator = c1*g1 + c2*g2, then exactly
    numerator = c1*hcurve1 + c2*hcurve2 + (c1+c2)*htors.
This produces coefficients containing only x1,x2,y1,y2,A,r, as requested.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import sympy as sp


# ---------------------------------------------------------------------------
# 1. Variables and the Vélu formulas
# ---------------------------------------------------------------------------
x1, x2, y1, y2, A, B, r = sp.symbols("x1 x2 y1 y2 A B r")
B0 = -(r**3 + A*r)
t = 3*r**2 + A

ell = (y1 - y2) / (x1 - x2)
x3 = ell**2 - x1 - x2

X1p = x1 + t / (x1 - r)
X2p = x2 + t / (x2 - r)
Y1p = y1 * ((x1 - r) ** 2 - t) / (x1 - r) ** 2
Y2p = y2 * ((x2 - r) ** 2 - t) / (x2 - r) ** 2
ellp = (Y1p - Y2p) / (X1p - X2p)
X3p = ellp**2 - X1p - X2p

lhs = x3 + t / (x3 - r)
rhs = X3p

# Keep both exact conventions. The reduced one is the primary certificate.
together_diff = sp.together(lhs - rhs)
raw_num_expr, raw_den_expr = sp.fraction(together_diff)
raw_num = sp.expand(raw_num_expr)
raw_den = sp.factor(raw_den_expr)

reduced_diff = sp.cancel(together_diff)
num_expr, den_expr = sp.fraction(reduced_diff)
num = sp.expand(num_expr)
den = sp.factor(den_expr)

raw_multiplier = sp.factor(sp.cancel(raw_num / num))
assert sp.denom(sp.together(raw_multiplier)) == 1
assert sp.expand(raw_num - raw_multiplier*num) == 0
assert sp.expand(raw_num*den - num*raw_den) == 0


# ---------------------------------------------------------------------------
# 2. B-eliminated curve equations, division in y1 and then y2
# ---------------------------------------------------------------------------
# These are exactly the two curve equations after B := -(r^3 + A*r).
g1 = sp.expand(y1**2 - x1**3 - A*x1 - B0)
g2 = sp.expand(y2**2 - x2**3 - A*x2 - B0)

c1_raw, rem1 = sp.div(num, g1, y1)
c2_raw, rem2 = sp.div(sp.expand(rem1), g2, y2)

c1 = sp.expand(c1_raw)
c2 = sp.expand(c2_raw)
c3 = sp.expand(c1 + c2)
rem1 = sp.expand(rem1)
rem2 = sp.expand(rem2)

# Original, non-eliminated hypotheses used by Lean.
hcurve1 = y1**2 - x1**3 - A*x1 - B
hcurve2 = y2**2 - x2**3 - A*x2 - B
htors = r**3 + A*r + B

assert sp.expand(g1 - (hcurve1 + htors)) == 0
assert sp.expand(g2 - (hcurve2 + htors)) == 0
assert rem2 == 0
assert sp.expand(num - c1*g1 - c2*g2) == 0
assert sp.expand(num - c1*hcurve1 - c2*hcurve2 - c3*htors) == 0
assert sp.expand(
    raw_num
    - raw_multiplier*c1*hcurve1
    - raw_multiplier*c2*hcurve2
    - raw_multiplier*c3*htors
) == 0
assert all(B not in c.free_symbols for c in (c1, c2, c3))
assert all(sp.denom(sp.together(c)) == 1 for c in (c1, c2, c3))

# Exact factorizations used for the readable Lean output.
f1 = sp.factor(c1)
f2 = sp.factor(c2)
f3 = sp.factor(c3)
assert sp.expand(f1 - c1) == 0
assert sp.expand(f2 - c2) == 0
assert sp.expand(f3 - c3) == 0


# ---------------------------------------------------------------------------
# 3. Lean 4 printer
# ---------------------------------------------------------------------------
LEAN_NAMES = {
    "x1": "x₁",
    "x2": "x₂",
    "y1": "y₁",
    "y2": "y₂",
    "A": "A",
    "r": "r",
}


def lean_expr(expr: sp.Expr) -> str:
    """Print a small SymPy expression in Lean 4 syntax."""
    text = sp.sstr(expr, order="lex").replace("**", "^")
    for old, new in LEAN_NAMES.items():
        text = re.sub(rf"\b{re.escape(old)}\b", new, text)
    return text


def lean_sum_lines(expr: sp.Expr, continuation_indent: str) -> list[str]:
    """Print an expanded polynomial, one signed monomial per line."""
    expr = sp.expand(expr)
    if expr == 0:
        return ["0"]

    terms = expr.as_ordered_terms(order="lex")
    lines: list[str] = []
    for i, term in enumerate(terms):
        negative = term.could_extract_minus_sign()
        body = lean_expr(-term if negative else term)
        if i == 0:
            lines.append(("- " if negative else "") + body)
        else:
            lines.append(continuation_indent + ("- " if negative else "+ ") + body)
    return lines


def term_count(expr: sp.Expr) -> int:
    expr = sp.expand(expr)
    return 0 if expr == 0 else len(expr.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def factor_summary(expr: sp.Expr) -> str:
    content, factors = sp.factor_list(expr)
    pieces = []
    if content != 1:
        pieces.append(lean_expr(content))
    for factor, exponent in factors:
        pieces.append(f"({lean_expr(factor)})^{exponent}[{term_count(factor)} terms]")
    return " * ".join(pieces)


def emit_factorized_definition(name: str, expr: sp.Expr) -> list[str]:
    """Emit `let name : ℚ := ...` with any large factor printed multiline."""
    content, factors = sp.factor_list(expr)
    components: list[tuple[str, sp.Expr | str, int]] = []

    if content != 1:
        components.append(("inline", lean_expr(content), 1))
    for factor, exponent in factors:
        if term_count(factor) <= 4:
            token = f"({lean_expr(factor)})"
            if exponent != 1:
                token += f"^{exponent}"
            components.append(("inline", token, 1))
        else:
            components.append(("poly", factor, exponent))

    lines = [f"let {name} : ℚ :="]
    for i, (kind, value, exponent) in enumerate(components):
        suffix = " *" if i + 1 < len(components) else ""
        if kind == "inline":
            lines.append("  " + str(value) + suffix)
            continue

        poly = sp.sympify(value)
        lines.append("  (")
        body = lean_sum_lines(poly, "    ")
        lines.append("    " + body[0])
        lines.extend(body[1:])
        close = "  )"
        if exponent != 1:
            close += f"^{exponent}"
        lines.append(close + suffix)
    return lines


# ---------------------------------------------------------------------------
# 4. Reproducible report
# ---------------------------------------------------------------------------
print("## Exact result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- raw together numerator terms: `{term_count(raw_num)}`")
print(f"- reduced cancelled numerator terms: `{term_count(num)}`")
print(f"- exact raw/reduced multiplier: `{sp.sstr(raw_multiplier, order='lex')}`")
print(f"- reduced numerator degree in `y1`: `{sp.degree(num, y1)}`")
print(f"- reduced numerator degree in `y2`: `{sp.degree(num, y2)}`")
print(f"- reduced `c1` expanded terms: `{term_count(c1)}`")
print(f"- reduced `c2` expanded terms: `{term_count(c2)}`")
print(f"- reduced `c3` expanded terms: `{term_count(c3)}`")
print(f"- reduced `c1` factorization: `{factor_summary(c1)}`")
print(f"- reduced `c2` factorization: `{factor_summary(c2)}`")
print(f"- reduced `c3` factorization: `{factor_summary(c3)}`")
print(f"- final division remainder: `{rem2}`")
print("- exact reduced-curve verification: `0`")
print("- exact original-hypothesis verification: `0`")
print("- exact raw-numerator verification using the multiplier: `0`")
print("- all three reduced coefficients are B-free: `True`")
print(f"- raw numerator SHA-256: `{digest(raw_num)}`")
print(f"- reduced numerator SHA-256: `{digest(num)}`")
print(f"- reduced c1 SHA-256: `{digest(c1)}`")
print(f"- reduced c2 SHA-256: `{digest(c2)}`")
print(f"- reduced c3 SHA-256: `{digest(c3)}`")
print()
print("The reduced denominator returned by `fraction(cancel(together(lhs - rhs)))` factors as:")
print()
print("```text")
print(sp.sstr(den, order="lex"))
print("```")
print()
print("The uncancelled denominator returned by `fraction(together(lhs - rhs))` factors as:")
print()
print("```text")
print(sp.sstr(raw_den, order="lex"))
print("```")
print()
print("The first remainder (after division in `y1`) has")
print(f"`{term_count(rem1)}` expanded terms; division of it by `g2` in `y2` has zero remainder.")
print()
print("Because `g1 = hcurve₁ + htors` and `g2 = hcurve₂ + htors`, the third coefficient is exactly `c1 + c2`.")
print()

print("## Exact SymPy script")
print()
print("```python")
print(Path(__file__).read_text(encoding="utf-8").rstrip())
print("```")
print()

print("## Exact factorized Lean 4 coefficients")
print()
print("```lean")
for definition in (
    emit_factorized_definition("q974_c1", c1),
    emit_factorized_definition("q974_c2", c2),
    emit_factorized_definition("q974_c3", c3),
):
    for line in definition:
        print(line)
    print()
print("```")
print()

print("## Lean command for the reduced numerator")
print()
print("Use this when the target is the numerator of `cancel(together(lhs - rhs))`:")
print()
print("```lean")
print("linear_combination")
print("  q974_c1 * hcurve₁ +")
print("  q974_c2 * hcurve₂ +")
print("  q974_c3 * htors")
print("```")
print()

print("## Lean command for the raw `together` numerator")
print()
print("The raw numerator is the reduced numerator multiplied by")
print(f"`{lean_expr(raw_multiplier)}`. With the same definitions above, use:")
print()
print("```lean")
print("linear_combination")
print(f"  ({lean_expr(raw_multiplier)} * q974_c1) * hcurve₁ +")
print(f"  ({lean_expr(raw_multiplier)} * q974_c2) * hcurve₂ +")
print(f"  ({lean_expr(raw_multiplier)} * q974_c3) * htors")
print("```")
