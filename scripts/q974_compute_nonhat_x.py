#!/usr/bin/env python3
"""Q974: exact SymPy certificate for the non-hat Vélu X-coordinate identity.

The rational identity itself is formed after eliminating
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
diff = sp.together(lhs - rhs)
num_raw, den_raw = sp.fraction(diff)
num = sp.expand(num_raw)
den = sp.factor(den_raw)


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
assert all(B not in c.free_symbols for c in (c1, c2, c3))
assert all(sp.denom(sp.together(c)) == 1 for c in (c1, c2, c3))


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


def lean_monomial(expr: sp.Expr) -> str:
    """Print one expanded monomial in syntax accepted by Lean 4."""
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
        body = lean_monomial(-term if negative else term)
        if i == 0:
            lines.append(("- " if negative else "") + body)
        else:
            lines.append(continuation_indent + ("- " if negative else "+ ") + body)
    return lines


def emit_coefficient(expr: sp.Expr, outer_indent: str = "  ") -> list[str]:
    inner_indent = outer_indent + "  "
    body = lean_sum_lines(expr, inner_indent)
    return [outer_indent + "(", inner_indent + body[0], *body[1:], outer_indent + ")"]


def term_count(expr: sp.Expr) -> int:
    expr = sp.expand(expr)
    return 0 if expr == 0 else len(expr.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


# ---------------------------------------------------------------------------
# 4. Reproducible report
# ---------------------------------------------------------------------------
print("## Exact result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- numerator terms: `{term_count(num)}`")
print(f"- degree in `y1`: `{sp.degree(num, y1)}`")
print(f"- degree in `y2`: `{sp.degree(num, y2)}`")
print(f"- `c1` terms: `{term_count(c1)}`")
print(f"- `c2` terms: `{term_count(c2)}`")
print(f"- `c3` terms after expansion: `{term_count(c3)}`")
print(f"- final division remainder: `{rem2}`")
print("- exact reduced-curve verification: `0`")
print("- exact original-hypothesis verification: `0`")
print("- all three coefficients are B-free: `True`")
print(f"- numerator SHA-256: `{digest(num)}`")
print(f"- c1 SHA-256: `{digest(c1)}`")
print(f"- c2 SHA-256: `{digest(c2)}`")
print(f"- c3 SHA-256: `{digest(c3)}`")
print()
print("The denominator returned by `fraction(together(lhs - rhs))` factors as:")
print()
print("```text")
print(sp.sstr(den, order="lex"))
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

print("## Exact Lean 4 command")
print()
print("```lean")
print("linear_combination")
for line in emit_coefficient(c1):
    print(line)
print("  * hcurve₁ +")
for line in emit_coefficient(c2):
    print(line)
print("  * hcurve₂ +")
for line in emit_coefficient(c3):
    print(line)
print("  * htors")
print("```")
