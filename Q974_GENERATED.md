## Exact result

- SymPy version: `1.14.0`
- raw together numerator terms: `1178`
- reduced cancelled numerator terms: `614`
- exact raw/reduced multiplier: `-(x1 - x2)**3`
- reduced numerator degree in `y1`: `4`
- reduced numerator degree in `y2`: `4`
- reduced `c1` terms: `196`
- reduced `c2` terms: `167`
- reduced `c3` terms after expansion: `200`
- final division remainder: `0`
- exact reduced-curve verification: `0`
- exact original-hypothesis verification: `0`
- exact raw-numerator verification using the multiplier: `0`
- all three reduced coefficients are B-free: `True`
- raw numerator SHA-256: `c6cb5b6215ca1402ac09cad9012eb81d4a3f8621b57b97c0fd4ca5eb5395ab1b`
- reduced numerator SHA-256: `6a0ffae81d4e9a12ff6e5d9f5b63e7f69f527eee02a88bb326a6564def8fc9b2`
- reduced c1 SHA-256: `745c4cfb73225c45df6c6b689c6aa49d51c998bf4b93d5e2ba50d238c4b3b7f1`
- reduced c2 SHA-256: `bcc6fcdc3bf5c824d8912ff7bd08b65c244778ef6060c363151daaa7494df50a`
- reduced c3 SHA-256: `d9ffd0fcceb901d3f60bcab861eb30047baae7f7badbaa163855f8bf88d9a61b`

The reduced denominator returned by `fraction(cancel(together(lhs - rhs)))` factors as:

```text
(-r + x1)**2*(-r + x2)**2*(x1 - x2)*(-A - 2*r**2 - r*x1 - r*x2 + x1*x2)**2*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)
```

The uncancelled denominator returned by `fraction(together(lhs - rhs))` factors as:

```text
-(-r + x1)**2*(-r + x2)**2*(x1 - x2)**4*(-A - 2*r**2 - r*x1 - r*x2 + x1*x2)**2*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)
```

The first remainder (after division in `y1`) has
`439` expanded terms; division of it by `g2` in `y2` has zero remainder.

Because `g1 = hcurve₁ + htors` and `g2 = hcurve₂ + htors`, the third coefficient is exactly `c1 + c2`.

## Exact SymPy script

```python
#!/usr/bin/env python3
"""Q974: exact SymPy certificate for the non-hat Vélu X-coordinate identity.

Two denominator-clearing conventions are reported:

1. reduced: numerator(cancel(together(lhs - rhs)));
2. raw:     numerator(together(lhs - rhs)).

The raw numerator is checked to be an exact polynomial multiple of the reduced
one.  The rational identity itself is formed after eliminating
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

# Keep both exact conventions.  The reduced one is the primary certificate.
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


def lean_expr(expr: sp.Expr) -> str:
    """Print any small SymPy expression in Lean syntax."""
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


def emit_scaled_coefficient(
    multiplier: sp.Expr, coeff: sp.Expr, outer_indent: str = "  "
) -> list[str]:
    inner_indent = outer_indent + "  "
    coeff_indent = inner_indent + "  "
    body = lean_sum_lines(coeff, coeff_indent)
    return [
        outer_indent + "(",
        inner_indent + lean_expr(multiplier) + " * (",
        coeff_indent + body[0],
        *body[1:],
        inner_indent + ")",
        outer_indent + ")",
    ]


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
print(f"- raw together numerator terms: `{term_count(raw_num)}`")
print(f"- reduced cancelled numerator terms: `{term_count(num)}`")
print(f"- exact raw/reduced multiplier: `{sp.sstr(raw_multiplier, order='lex')}`")
print(f"- reduced numerator degree in `y1`: `{sp.degree(num, y1)}`")
print(f"- reduced numerator degree in `y2`: `{sp.degree(num, y2)}`")
print(f"- reduced `c1` terms: `{term_count(c1)}`")
print(f"- reduced `c2` terms: `{term_count(c2)}`")
print(f"- reduced `c3` terms after expansion: `{term_count(c3)}`")
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

print("## Exact Lean 4 command for the reduced numerator")
print()
print("This is the numerator of `cancel(together(lhs - rhs))`.")
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
print()

print("## Exact Lean 4 command for the raw `together` numerator")
print()
print("The raw numerator is the reduced numerator multiplied by")
print(f"`{lean_expr(raw_multiplier)}`.  Therefore use:")
print()
print("```lean")
print("linear_combination")
for line in emit_scaled_coefficient(raw_multiplier, c1):
    print(line)
print("  * hcurve₁ +")
for line in emit_scaled_coefficient(raw_multiplier, c2):
    print(line)
print("  * hcurve₂ +")
for line in emit_scaled_coefficient(raw_multiplier, c3):
    print(line)
print("  * htors")
print("```")
```

## Exact Lean 4 command for the reduced numerator

This is the numerator of `cancel(together(lhs - rhs))`.

```lean
linear_combination
  (
    - 2*A^3*r^4
    + 5*A^3*r^3*x₁
    + 3*A^3*r^3*x₂
    - 4*A^3*r^2*x₁^2
    - 7*A^3*r^2*x₁*x₂
    - A^3*r^2*x₂^2
    + A^3*r*x₁^3
    + 5*A^3*r*x₁^2*x₂
    + 2*A^3*r*x₁*x₂^2
    - A^3*x₁^3*x₂
    - A^3*x₁^2*x₂^2
    - 12*A^2*r^6
    + 27*A^2*r^5*x₁
    + 15*A^2*r^5*x₂
    - 19*A^2*r^4*x₁^2
    - 22*A^2*r^4*x₁*x₂
    - 7*A^2*r^4*x₂^2
    + 10*A^2*r^3*x₁^2*x₂
    - 5*A^2*r^3*x₁*x₂^2
    + 7*A^2*r^3*x₂^3
    + 2*A^2*r^3*y₁^2
    - 4*A^2*r^3*y₁*y₂
    + 2*A^2*r^2*x₁^4
    + 10*A^2*r^2*x₁^3*x₂
    + 6*A^2*r^2*x₁^2*x₂^2
    - 5*A^2*r^2*x₁*x₂^3
    - A^2*r^2*x₁*y₁^2
    + 2*A^2*r^2*x₁*y₁*y₂
    + 4*A^2*r^2*x₁*y₂^2
    - A^2*r^2*x₂^4
    - 5*A^2*r^2*x₂*y₁^2
    + 10*A^2*r^2*x₂*y₁*y₂
    - 4*A^2*r^2*x₂*y₂^2
    - 4*A^2*r*x₁^4*x₂
    - 11*A^2*r*x₁^3*x₂^2
    + 7*A^2*r*x₁^2*x₂^3
    - 4*A^2*r*x₁^2*y₂^2
    + 5*A^2*r*x₁*x₂^4
    + 2*A^2*r*x₁*x₂*y₁^2
    - 4*A^2*r*x₁*x₂*y₁*y₂
    - 3*A^2*r*x₂^5
    + 4*A^2*r*x₂^2*y₁^2
    - 8*A^2*r*x₂^2*y₁*y₂
    + 4*A^2*r*x₂^2*y₂^2
    + 2*A^2*x₁^4*x₂^2
    + A^2*x₁^3*x₂^3
    + A^2*x₁^3*y₂^2
    - 4*A^2*x₁^2*x₂^4
    + A^2*x₁^2*x₂*y₂^2
    - A^2*x₁*x₂^2*y₁^2
    + 2*A^2*x₁*x₂^2*y₁*y₂
    - A^2*x₁*x₂^2*y₂^2
    + A^2*x₂^6
    - A^2*x₂^3*y₁^2
    + 2*A^2*x₂^3*y₁*y₂
    - A^2*x₂^3*y₂^2
    - 22*A*r^8
    + 43*A*r^7*x₁
    + 19*A*r^7*x₂
    - 27*A*r^6*x₁^2
    + 11*A*r^6*x₁*x₂
    - 18*A*r^6*x₂^2
    - 16*A*r^5*x₁^3
    - 12*A*r^5*x₁^2*x₂
    - 51*A*r^5*x₁*x₂^2
    + 33*A*r^5*x₂^3
    + 10*A*r^5*y₁^2
    - 20*A*r^5*y₁*y₂
    + 9*A*r^4*x₁^4
    + 56*A*r^4*x₁^3*x₂
    + 9*A*r^4*x₁^2*x₂^2
    - 17*A*r^4*x₁*x₂^3
    - 2*A*r^4*x₁*y₁^2
    + 6*A*r^4*x₁*y₁*y₂
    + 18*A*r^4*x₁*y₂^2
    - A*r^4*x₂^4
    - 24*A*r^4*x₂*y₁^2
    + 46*A*r^4*x₂*y₁*y₂
    - 18*A*r^4*x₂*y₂^2
    + A*r^3*x₁^5
    - 17*A*r^3*x₁^4*x₂
    - 42*A*r^3*x₁^3*x₂^2
    + 38*A*r^3*x₁^2*x₂^3
    - 2*A*r^3*x₁^2*y₁^2
    - 12*A*r^3*x₁^2*y₂^2
    + 13*A*r^3*x₁*x₂^4
    - 15*A*r^3*x₂^5
    + 18*A*r^3*x₂^2*y₁^2
    - 32*A*r^3*x₂^2*y₁*y₂
    + 12*A*r^3*x₂^2*y₂^2
    - 3*A*r^2*x₁^5*x₂
    + 9*A*r^2*x₁^4*x₂^2
    + 10*A*r^2*x₁^3*x₂^3
    + 2*A*r^2*x₁^3*y₁*y₂
    - 3*A*r^2*x₁^2*x₂^4
    + 6*A*r^2*x₁^2*x₂*y₁^2
    - 6*A*r^2*x₁^2*x₂*y₁*y₂
    - 12*A*r^2*x₁^2*x₂*y₂^2
    - 3*A*r^2*x₁*x₂^5
    + 6*A*r^2*x₁*x₂^2*y₁^2
    - 18*A*r^2*x₁*x₂^2*y₁*y₂
    + 12*A*r^2*x₁*x₂^2*y₂^2
    + 4*A*r^2*x₂^6
    - 4*A*r^2*x₂^3*y₁^2
    + 6*A*r^2*x₂^3*y₁*y₂
    + 3*A*r*x₁^5*x₂^2
    - 3*A*r*x₁^4*x₂^3
    - 11*A*r*x₁^3*x₂^4
    - 4*A*r*x₁^3*x₂*y₁*y₂
    + 12*A*r*x₁^3*x₂*y₂^2
    - 3*A*r*x₁^2*x₂^5
    - 6*A*r*x₁^2*x₂^2*y₁^2
    + 12*A*r*x₁^2*x₂^2*y₁*y₂
    + 4*A*r*x₁*x₂^6
    - 4*A*r*x₁*x₂^3*y₁^2
    + 12*A*r*x₁*x₂^3*y₁*y₂
    - 12*A*r*x₁*x₂^3*y₂^2
    - A*x₁^5*x₂^3
    + 2*A*x₁^4*x₂^4
    + 3*A*x₁^3*x₂^5
    + 2*A*x₁^3*x₂^2*y₁*y₂
    - 6*A*x₁^3*x₂^2*y₂^2
    - 2*A*x₁^2*x₂^6
    + 2*A*x₁^2*x₂^3*y₁^2
    - 6*A*x₁^2*x₂^3*y₁*y₂
    + 6*A*x₁^2*x₂^3*y₂^2
    - 12*r^10
    + 21*r^9*x₁
    + 3*r^9*x₂
    - 18*r^8*x₁^2
    + 42*r^8*x₁*x₂
    - 18*r^8*x₂^2
    - 21*r^7*x₁^3
    + 9*r^7*x₁^2*x₂
    - 54*r^7*x₁*x₂^2
    + 36*r^7*x₂^3
    + 12*r^7*y₁^2
    - 24*r^7*y₁*y₂
    + 9*r^6*x₁^4
    + 51*r^6*x₁^3*x₂
    - 54*r^6*x₁^2*x₂^2
    - 6*r^6*x₁*x₂^3
    + 3*r^6*x₁*y₁^2
    + 18*r^6*x₁*y₂^2
    + 6*r^6*x₂^4
    - 27*r^6*x₂*y₁^2
    + 48*r^6*x₂*y₁*y₂
    - 18*r^6*x₂*y₂^2
    + 3*r^5*x₁^5
    - 15*r^5*x₁^4*x₂
    - 27*r^5*x₁^3*x₂^2
    + 51*r^5*x₁^2*x₂^3
    - 6*r^5*x₁^2*y₁^2
    - 6*r^5*x₁*x₂^4
    - 18*r^5*x₁*x₂*y₁^2
    + 36*r^5*x₁*x₂*y₁*y₂
    - 18*r^5*x₂^5
    + 18*r^5*x₂^2*y₁^2
    - 24*r^5*x₂^2*y₁*y₂
    - 9*r^4*x₁^5*x₂
    + 9*r^4*x₁^4*x₂^2
    + 21*r^4*x₁^3*x₂^3
    + 6*r^4*x₁^3*y₁*y₂
    - 9*r^4*x₁^3*y₂^2
    + 27*r^4*x₁^2*x₂^4
    + 18*r^4*x₁^2*x₂*y₁^2
    - 18*r^4*x₁^2*x₂*y₁*y₂
    - 45*r^4*x₁^2*x₂*y₂^2
    - 9*r^4*x₁*x₂^5
    + 27*r^4*x₁*x₂^2*y₁^2
    - 72*r^4*x₁*x₂^2*y₁*y₂
    + 45*r^4*x₁*x₂^2*y₂^2
    + 3*r^4*x₂^6
    - 3*r^4*x₂^3*y₁^2
    + 9*r^4*x₂^3*y₂^2
    + 9*r^3*x₁^5*x₂^2
    - 9*r^3*x₁^4*x₂^3
    - 33*r^3*x₁^3*x₂^4
    - 12*r^3*x₁^3*x₂*y₁*y₂
    + 36*r^3*x₁^3*x₂*y₂^2
    - 9*r^3*x₁^2*x₂^5
    - 18*r^3*x₁^2*x₂^2*y₁^2
    + 36*r^3*x₁^2*x₂^2*y₁*y₂
    + 12*r^3*x₁*x₂^6
    - 12*r^3*x₁*x₂^3*y₁^2
    + 36*r^3*x₁*x₂^3*y₁*y₂
    - 36*r^3*x₁*x₂^3*y₂^2
    - 3*r^2*x₁^5*x₂^3
    + 6*r^2*x₁^4*x₂^4
    + 9*r^2*x₁^3*x₂^5
    + 6*r^2*x₁^3*x₂^2*y₁*y₂
    - 18*r^2*x₁^3*x₂^2*y₂^2
    - 6*r^2*x₁^2*x₂^6
    + 6*r^2*x₁^2*x₂^3*y₁^2
    - 18*r^2*x₁^2*x₂^3*y₁*y₂
    + 18*r^2*x₁^2*x₂^3*y₂^2
  )
  * hcurve₁ +
  (
    2*A^3*r^4
    - 7*A^3*r^3*x₁
    - A^3*r^3*x₂
    + 9*A^3*r^2*x₁^2
    + 3*A^3*r^2*x₁*x₂
    - 5*A^3*r*x₁^3
    - 3*A^3*r*x₁^2*x₂
    + A^3*x₁^4
    + A^3*x₁^3*x₂
    + 12*A^2*r^6
    - 37*A^2*r^5*x₁
    - 5*A^2*r^5*x₂
    + 41*A^2*r^4*x₁^2
    + 4*A^2*r^4*x₁*x₂
    + 3*A^2*r^4*x₂^2
    - 20*A^2*r^3*x₁^3
    + 16*A^2*r^3*x₁^2*x₂
    - 9*A^2*r^3*x₁*x₂^2
    + A^2*r^3*x₂^3
    + 4*A^2*r^3*y₁*y₂
    - 2*A^2*r^3*y₂^2
    + 5*A^2*r^2*x₁^4
    - 23*A^2*r^2*x₁^3*x₂
    + 6*A^2*r^2*x₁^2*x₂^2
    + 2*A^2*r^2*x₁*x₂^3
    - 10*A^2*r^2*x₁*y₁*y₂
    + 5*A^2*r^2*x₁*y₂^2
    - 2*A^2*r^2*x₂^4
    - 2*A^2*r^2*x₂*y₁*y₂
    + A^2*r^2*x₂*y₂^2
    - A^2*r*x₁^5
    + 7*A^2*r*x₁^4*x₂
    + 3*A^2*r*x₁^3*x₂^2
    - 7*A^2*r*x₁^2*x₂^3
    + 8*A^2*r*x₁^2*y₁*y₂
    - 4*A^2*r*x₁^2*y₂^2
    + 4*A^2*r*x₁*x₂^4
    + 4*A^2*r*x₁*x₂*y₁*y₂
    - 2*A^2*r*x₁*x₂*y₂^2
    + A^2*x₁^5*x₂
    - 3*A^2*x₁^4*x₂^2
    + 4*A^2*x₁^3*x₂^3
    - 2*A^2*x₁^3*y₁*y₂
    + A^2*x₁^3*y₂^2
    - 2*A^2*x₁^2*x₂^4
    - 2*A^2*x₁^2*x₂*y₁*y₂
    + A^2*x₁^2*x₂*y₂^2
    + 22*A*r^8
    - 55*A*r^7*x₁
    - 7*A*r^7*x₂
    + 48*A*r^6*x₁^2
    - 29*A*r^6*x₁*x₂
    + 15*A*r^6*x₂^2
    - 24*A*r^5*x₁^3
    + 108*A*r^5*x₁^2*x₂
    - 45*A*r^5*x₁*x₂^2
    + 7*A*r^5*x₂^3
    + 20*A*r^5*y₁*y₂
    - 10*A*r^5*y₂^2
    + 10*A*r^4*x₁^4
    - 94*A*r^4*x₁^3*x₂
    + 36*A*r^4*x₁^2*x₂^2
    + A*r^4*x₁*x₂^3
    - 46*A*r^4*x₁*y₁*y₂
    + 24*A*r^4*x₁*y₂^2
    - 9*A*r^4*x₂^4
    - 6*A*r^4*x₂*y₁*y₂
    + 2*A*r^4*x₂*y₂^2
    + 3*A*r^3*x₁^5
    + 23*A*r^3*x₁^4*x₂
    - 2*A*r^3*x₁^3*x₂^2
    - 18*A*r^3*x₁^2*x₂^3
    + 32*A*r^3*x₁^2*y₁*y₂
    - 18*A*r^3*x₁^2*y₂^2
    + 17*A*r^3*x₁*x₂^4
    - A*r^3*x₂^5
    + 2*A*r^3*x₂^2*y₂^2
    - 4*A*r^2*x₁^6
    - 9*A*r^2*x₁^5*x₂
    - 3*A*r^2*x₁^4*x₂^2
    + 8*A*r^2*x₁^3*x₂^3
    - 6*A*r^2*x₁^3*y₁*y₂
    + 4*A*r^2*x₁^3*y₂^2
    - 9*A*r^2*x₁^2*x₂^4
    + 18*A*r^2*x₁^2*x₂*y₁*y₂
    - 6*A*r^2*x₁^2*x₂*y₂^2
    + 3*A*r^2*x₁*x₂^5
    + 6*A*r^2*x₁*x₂^2*y₁*y₂
    - 6*A*r^2*x₁*x₂^2*y₂^2
    - 2*A*r^2*x₂^3*y₁*y₂
    + 8*A*r*x₁^6*x₂
    + 3*A*r*x₁^5*x₂^2
    - A*r*x₁^4*x₂^3
    + 3*A*r*x₁^3*x₂^4
    - 12*A*r*x₁^3*x₂*y₁*y₂
    + 4*A*r*x₁^3*x₂*y₂^2
    - 3*A*r*x₁^2*x₂^5
    - 12*A*r*x₁^2*x₂^2*y₁*y₂
    + 6*A*r*x₁^2*x₂^2*y₂^2
    + 4*A*r*x₁*x₂^3*y₁*y₂
    - 4*A*x₁^6*x₂^2
    + 3*A*x₁^5*x₂^3
    - 2*A*x₁^4*x₂^4
    + A*x₁^3*x₂^5
    + 6*A*x₁^3*x₂^2*y₁*y₂
    - 2*A*x₁^3*x₂^2*y₂^2
    - 2*A*x₁^2*x₂^3*y₁*y₂
    + 12*r^10
    - 21*r^9*x₁
    - 3*r^9*x₂
    + 18*r^8*x₁^2
    - 42*r^8*x₁*x₂
    + 18*r^8*x₂^2
    - 27*r^7*x₁^3
    + 99*r^7*x₁^2*x₂
    - 54*r^7*x₁*x₂^2
    + 12*r^7*x₂^3
    + 24*r^7*y₁*y₂
    - 12*r^7*y₂^2
    + 12*r^6*x₁^4
    - 48*r^6*x₁^3*x₂
    + 54*r^6*x₁^2*x₂^2
    - 15*r^6*x₁*x₂^3
    - 48*r^6*x₁*y₁*y₂
    + 27*r^6*x₁*y₂^2
    - 9*r^6*x₂^4
    - 3*r^6*x₂*y₂^2
    + 18*r^5*x₁^5
    + 6*r^5*x₁^4*x₂
    - 33*r^5*x₁^3*x₂^2
    + 9*r^5*x₁^2*x₂^3
    + 24*r^5*x₁^2*y₁*y₂
    - 18*r^5*x₁^2*y₂^2
    + 15*r^5*x₁*x₂^4
    - 36*r^5*x₁*x₂*y₁*y₂
    + 18*r^5*x₁*x₂*y₂^2
    - 3*r^5*x₂^5
    + 6*r^5*x₂^2*y₂^2
    - 12*r^4*x₁^6
    - 36*r^4*x₁^5*x₂
    + 18*r^4*x₁^4*x₂^2
    - 12*r^4*x₁^3*x₂^3
    + 3*r^4*x₁^3*y₂^2
    - 9*r^4*x₁^2*x₂^4
    + 72*r^4*x₁^2*x₂*y₁*y₂
    - 27*r^4*x₁^2*x₂*y₂^2
    + 9*r^4*x₁*x₂^5
    + 18*r^4*x₁*x₂^2*y₁*y₂
    - 18*r^4*x₁*x₂^2*y₂^2
    - 6*r^4*x₂^3*y₁*y₂
    + 24*r^3*x₁^6*x₂
    + 9*r^3*x₁^5*x₂^2
    - 3*r^3*x₁^4*x₂^3
    + 9*r^3*x₁^3*x₂^4
    - 36*r^3*x₁^3*x₂*y₁*y₂
    + 12*r^3*x₁^3*x₂*y₂^2
    - 9*r^3*x₁^2*x₂^5
    - 36*r^3*x₁^2*x₂^2*y₁*y₂
    + 18*r^3*x₁^2*x₂^2*y₂^2
    + 12*r^3*x₁*x₂^3*y₁*y₂
    - 12*r^2*x₁^6*x₂^2
    + 9*r^2*x₁^5*x₂^3
    - 6*r^2*x₁^4*x₂^4
    + 3*r^2*x₁^3*x₂^5
    + 18*r^2*x₁^3*x₂^2*y₁*y₂
    - 6*r^2*x₁^3*x₂^2*y₂^2
    - 6*r^2*x₁^2*x₂^3*y₁*y₂
  )
  * hcurve₂ +
  (
    - 2*A^3*r^3*x₁
    + 2*A^3*r^3*x₂
    + 5*A^3*r^2*x₁^2
    - 4*A^3*r^2*x₁*x₂
    - A^3*r^2*x₂^2
    - 4*A^3*r*x₁^3
    + 2*A^3*r*x₁^2*x₂
    + 2*A^3*r*x₁*x₂^2
    + A^3*x₁^4
    - A^3*x₁^2*x₂^2
    - 10*A^2*r^5*x₁
    + 10*A^2*r^5*x₂
    + 22*A^2*r^4*x₁^2
    - 18*A^2*r^4*x₁*x₂
    - 4*A^2*r^4*x₂^2
    - 20*A^2*r^3*x₁^3
    + 26*A^2*r^3*x₁^2*x₂
    - 14*A^2*r^3*x₁*x₂^2
    + 8*A^2*r^3*x₂^3
    + 2*A^2*r^3*y₁^2
    - 2*A^2*r^3*y₂^2
    + 7*A^2*r^2*x₁^4
    - 13*A^2*r^2*x₁^3*x₂
    + 12*A^2*r^2*x₁^2*x₂^2
    - 3*A^2*r^2*x₁*x₂^3
    - A^2*r^2*x₁*y₁^2
    - 8*A^2*r^2*x₁*y₁*y₂
    + 9*A^2*r^2*x₁*y₂^2
    - 3*A^2*r^2*x₂^4
    - 5*A^2*r^2*x₂*y₁^2
    + 8*A^2*r^2*x₂*y₁*y₂
    - 3*A^2*r^2*x₂*y₂^2
    - A^2*r*x₁^5
    + 3*A^2*r*x₁^4*x₂
    - 8*A^2*r*x₁^3*x₂^2
    + 8*A^2*r*x₁^2*y₁*y₂
    - 8*A^2*r*x₁^2*y₂^2
    + 9*A^2*r*x₁*x₂^4
    + 2*A^2*r*x₁*x₂*y₁^2
    - 2*A^2*r*x₁*x₂*y₂^2
    - 3*A^2*r*x₂^5
    + 4*A^2*r*x₂^2*y₁^2
    - 8*A^2*r*x₂^2*y₁*y₂
    + 4*A^2*r*x₂^2*y₂^2
    + A^2*x₁^5*x₂
    - A^2*x₁^4*x₂^2
    + 5*A^2*x₁^3*x₂^3
    - 2*A^2*x₁^3*y₁*y₂
    + 2*A^2*x₁^3*y₂^2
    - 6*A^2*x₁^2*x₂^4
    - 2*A^2*x₁^2*x₂*y₁*y₂
    + 2*A^2*x₁^2*x₂*y₂^2
    - A^2*x₁*x₂^2*y₁^2
    + 2*A^2*x₁*x₂^2*y₁*y₂
    - A^2*x₁*x₂^2*y₂^2
    + A^2*x₂^6
    - A^2*x₂^3*y₁^2
    + 2*A^2*x₂^3*y₁*y₂
    - A^2*x₂^3*y₂^2
    - 12*A*r^7*x₁
    + 12*A*r^7*x₂
    + 21*A*r^6*x₁^2
    - 18*A*r^6*x₁*x₂
    - 3*A*r^6*x₂^2
    - 40*A*r^5*x₁^3
    + 96*A*r^5*x₁^2*x₂
    - 96*A*r^5*x₁*x₂^2
    + 40*A*r^5*x₂^3
    + 10*A*r^5*y₁^2
    - 10*A*r^5*y₂^2
    + 19*A*r^4*x₁^4
    - 38*A*r^4*x₁^3*x₂
    + 45*A*r^4*x₁^2*x₂^2
    - 16*A*r^4*x₁*x₂^3
    - 2*A*r^4*x₁*y₁^2
    - 40*A*r^4*x₁*y₁*y₂
    + 42*A*r^4*x₁*y₂^2
    - 10*A*r^4*x₂^4
    - 24*A*r^4*x₂*y₁^2
    + 40*A*r^4*x₂*y₁*y₂
    - 16*A*r^4*x₂*y₂^2
    + 4*A*r^3*x₁^5
    + 6*A*r^3*x₁^4*x₂
    - 44*A*r^3*x₁^3*x₂^2
    + 20*A*r^3*x₁^2*x₂^3
    - 2*A*r^3*x₁^2*y₁^2
    + 32*A*r^3*x₁^2*y₁*y₂
    - 30*A*r^3*x₁^2*y₂^2
    + 30*A*r^3*x₁*x₂^4
    - 16*A*r^3*x₂^5
    + 18*A*r^3*x₂^2*y₁^2
    - 32*A*r^3*x₂^2*y₁*y₂
    + 14*A*r^3*x₂^2*y₂^2
    - 4*A*r^2*x₁^6
    - 12*A*r^2*x₁^5*x₂
    + 6*A*r^2*x₁^4*x₂^2
    + 18*A*r^2*x₁^3*x₂^3
    - 4*A*r^2*x₁^3*y₁*y₂
    + 4*A*r^2*x₁^3*y₂^2
    - 12*A*r^2*x₁^2*x₂^4
    + 6*A*r^2*x₁^2*x₂*y₁^2
    + 12*A*r^2*x₁^2*x₂*y₁*y₂
    - 18*A*r^2*x₁^2*x₂*y₂^2
    + 6*A*r^2*x₁*x₂^2*y₁^2
    - 12*A*r^2*x₁*x₂^2*y₁*y₂
    + 6*A*r^2*x₁*x₂^2*y₂^2
    + 4*A*r^2*x₂^6
    - 4*A*r^2*x₂^3*y₁^2
    + 4*A*r^2*x₂^3*y₁*y₂
    + 8*A*r*x₁^6*x₂
    + 6*A*r*x₁^5*x₂^2
    - 4*A*r*x₁^4*x₂^3
    - 8*A*r*x₁^3*x₂^4
    - 16*A*r*x₁^3*x₂*y₁*y₂
    + 16*A*r*x₁^3*x₂*y₂^2
    - 6*A*r*x₁^2*x₂^5
    - 6*A*r*x₁^2*x₂^2*y₁^2
    + 6*A*r*x₁^2*x₂^2*y₂^2
    + 4*A*r*x₁*x₂^6
    - 4*A*r*x₁*x₂^3*y₁^2
    + 16*A*r*x₁*x₂^3*y₁*y₂
    - 12*A*r*x₁*x₂^3*y₂^2
    - 4*A*x₁^6*x₂^2
    + 2*A*x₁^5*x₂^3
    + 4*A*x₁^3*x₂^5
    + 8*A*x₁^3*x₂^2*y₁*y₂
    - 8*A*x₁^3*x₂^2*y₂^2
    - 2*A*x₁^2*x₂^6
    + 2*A*x₁^2*x₂^3*y₁^2
    - 8*A*x₁^2*x₂^3*y₁*y₂
    + 6*A*x₁^2*x₂^3*y₂^2
    - 48*r^7*x₁^3
    + 108*r^7*x₁^2*x₂
    - 108*r^7*x₁*x₂^2
    + 48*r^7*x₂^3
    + 12*r^7*y₁^2
    - 12*r^7*y₂^2
    + 21*r^6*x₁^4
    + 3*r^6*x₁^3*x₂
    - 21*r^6*x₁*x₂^3
    + 3*r^6*x₁*y₁^2
    - 48*r^6*x₁*y₁*y₂
    + 45*r^6*x₁*y₂^2
    - 3*r^6*x₂^4
    - 27*r^6*x₂*y₁^2
    + 48*r^6*x₂*y₁*y₂
    - 21*r^6*x₂*y₂^2
    + 21*r^5*x₁^5
    - 9*r^5*x₁^4*x₂
    - 60*r^5*x₁^3*x₂^2
    + 60*r^5*x₁^2*x₂^3
    - 6*r^5*x₁^2*y₁^2
    + 24*r^5*x₁^2*y₁*y₂
    - 18*r^5*x₁^2*y₂^2
    + 9*r^5*x₁*x₂^4
    - 18*r^5*x₁*x₂*y₁^2
    + 18*r^5*x₁*x₂*y₂^2
    - 21*r^5*x₂^5
    + 18*r^5*x₂^2*y₁^2
    - 24*r^5*x₂^2*y₁*y₂
    + 6*r^5*x₂^2*y₂^2
    - 12*r^4*x₁^6
    - 45*r^4*x₁^5*x₂
    + 27*r^4*x₁^4*x₂^2
    + 9*r^4*x₁^3*x₂^3
    + 6*r^4*x₁^3*y₁*y₂
    - 6*r^4*x₁^3*y₂^2
    + 18*r^4*x₁^2*x₂^4
    + 18*r^4*x₁^2*x₂*y₁^2
    + 54*r^4*x₁^2*x₂*y₁*y₂
    - 72*r^4*x₁^2*x₂*y₂^2
    + 27*r^4*x₁*x₂^2*y₁^2
    - 54*r^4*x₁*x₂^2*y₁*y₂
    + 27*r^4*x₁*x₂^2*y₂^2
    + 3*r^4*x₂^6
    - 3*r^4*x₂^3*y₁^2
    - 6*r^4*x₂^3*y₁*y₂
    + 9*r^4*x₂^3*y₂^2
    + 24*r^3*x₁^6*x₂
    + 18*r^3*x₁^5*x₂^2
    - 12*r^3*x₁^4*x₂^3
    - 24*r^3*x₁^3*x₂^4
    - 48*r^3*x₁^3*x₂*y₁*y₂
    + 48*r^3*x₁^3*x₂*y₂^2
    - 18*r^3*x₁^2*x₂^5
    - 18*r^3*x₁^2*x₂^2*y₁^2
    + 18*r^3*x₁^2*x₂^2*y₂^2
    + 12*r^3*x₁*x₂^6
    - 12*r^3*x₁*x₂^3*y₁^2
    + 48*r^3*x₁*x₂^3*y₁*y₂
    - 36*r^3*x₁*x₂^3*y₂^2
    - 12*r^2*x₁^6*x₂^2
    + 6*r^2*x₁^5*x₂^3
    + 12*r^2*x₁^3*x₂^5
    + 24*r^2*x₁^3*x₂^2*y₁*y₂
    - 24*r^2*x₁^3*x₂^2*y₂^2
    - 6*r^2*x₁^2*x₂^6
    + 6*r^2*x₁^2*x₂^3*y₁^2
    - 24*r^2*x₁^2*x₂^3*y₁*y₂
    + 18*r^2*x₁^2*x₂^3*y₂^2
  )
  * htors
```

## Exact Lean 4 command for the raw `together` numerator

The raw numerator is the reduced numerator multiplied by
`-(x₁ - x₂)^3`.  Therefore use:

```lean
linear_combination
  (
    -(x₁ - x₂)^3 * (
      - 2*A^3*r^4
      + 5*A^3*r^3*x₁
      + 3*A^3*r^3*x₂
      - 4*A^3*r^2*x₁^2
      - 7*A^3*r^2*x₁*x₂
      - A^3*r^2*x₂^2
      + A^3*r*x₁^3
      + 5*A^3*r*x₁^2*x₂
      + 2*A^3*r*x₁*x₂^2
      - A^3*x₁^3*x₂
      - A^3*x₁^2*x₂^2
      - 12*A^2*r^6
      + 27*A^2*r^5*x₁
      + 15*A^2*r^5*x₂
      - 19*A^2*r^4*x₁^2
      - 22*A^2*r^4*x₁*x₂
      - 7*A^2*r^4*x₂^2
      + 10*A^2*r^3*x₁^2*x₂
      - 5*A^2*r^3*x₁*x₂^2
      + 7*A^2*r^3*x₂^3
      + 2*A^2*r^3*y₁^2
      - 4*A^2*r^3*y₁*y₂
      + 2*A^2*r^2*x₁^4
      + 10*A^2*r^2*x₁^3*x₂
      + 6*A^2*r^2*x₁^2*x₂^2
      - 5*A^2*r^2*x₁*x₂^3
      - A^2*r^2*x₁*y₁^2
      + 2*A^2*r^2*x₁*y₁*y₂
      + 4*A^2*r^2*x₁*y₂^2
      - A^2*r^2*x₂^4
      - 5*A^2*r^2*x₂*y₁^2
      + 10*A^2*r^2*x₂*y₁*y₂
      - 4*A^2*r^2*x₂*y₂^2
      - 4*A^2*r*x₁^4*x₂
      - 11*A^2*r*x₁^3*x₂^2
      + 7*A^2*r*x₁^2*x₂^3
      - 4*A^2*r*x₁^2*y₂^2
      + 5*A^2*r*x₁*x₂^4
      + 2*A^2*r*x₁*x₂*y₁^2
      - 4*A^2*r*x₁*x₂*y₁*y₂
      - 3*A^2*r*x₂^5
      + 4*A^2*r*x₂^2*y₁^2
      - 8*A^2*r*x₂^2*y₁*y₂
      + 4*A^2*r*x₂^2*y₂^2
      + 2*A^2*x₁^4*x₂^2
      + A^2*x₁^3*x₂^3
      + A^2*x₁^3*y₂^2
      - 4*A^2*x₁^2*x₂^4
      + A^2*x₁^2*x₂*y₂^2
      - A^2*x₁*x₂^2*y₁^2
      + 2*A^2*x₁*x₂^2*y₁*y₂
      - A^2*x₁*x₂^2*y₂^2
      + A^2*x₂^6
      - A^2*x₂^3*y₁^2
      + 2*A^2*x₂^3*y₁*y₂
      - A^2*x₂^3*y₂^2
      - 22*A*r^8
      + 43*A*r^7*x₁
      + 19*A*r^7*x₂
      - 27*A*r^6*x₁^2
      + 11*A*r^6*x₁*x₂
      - 18*A*r^6*x₂^2
      - 16*A*r^5*x₁^3
      - 12*A*r^5*x₁^2*x₂
      - 51*A*r^5*x₁*x₂^2
      + 33*A*r^5*x₂^3
      + 10*A*r^5*y₁^2
      - 20*A*r^5*y₁*y₂
      + 9*A*r^4*x₁^4
      + 56*A*r^4*x₁^3*x₂
      + 9*A*r^4*x₁^2*x₂^2
      - 17*A*r^4*x₁*x₂^3
      - 2*A*r^4*x₁*y₁^2
      + 6*A*r^4*x₁*y₁*y₂
      + 18*A*r^4*x₁*y₂^2
      - A*r^4*x₂^4
      - 24*A*r^4*x₂*y₁^2
      + 46*A*r^4*x₂*y₁*y₂
      - 18*A*r^4*x₂*y₂^2
      + A*r^3*x₁^5
      - 17*A*r^3*x₁^4*x₂
      - 42*A*r^3*x₁^3*x₂^2
      + 38*A*r^3*x₁^2*x₂^3
      - 2*A*r^3*x₁^2*y₁^2
      - 12*A*r^3*x₁^2*y₂^2
      + 13*A*r^3*x₁*x₂^4
      - 15*A*r^3*x₂^5
      + 18*A*r^3*x₂^2*y₁^2
      - 32*A*r^3*x₂^2*y₁*y₂
      + 12*A*r^3*x₂^2*y₂^2
      - 3*A*r^2*x₁^5*x₂
      + 9*A*r^2*x₁^4*x₂^2
      + 10*A*r^2*x₁^3*x₂^3
      + 2*A*r^2*x₁^3*y₁*y₂
      - 3*A*r^2*x₁^2*x₂^4
      + 6*A*r^2*x₁^2*x₂*y₁^2
      - 6*A*r^2*x₁^2*x₂*y₁*y₂
      - 12*A*r^2*x₁^2*x₂*y₂^2
      - 3*A*r^2*x₁*x₂^5
      + 6*A*r^2*x₁*x₂^2*y₁^2
      - 18*A*r^2*x₁*x₂^2*y₁*y₂
      + 12*A*r^2*x₁*x₂^2*y₂^2
      + 4*A*r^2*x₂^6
      - 4*A*r^2*x₂^3*y₁^2
      + 6*A*r^2*x₂^3*y₁*y₂
      + 3*A*r*x₁^5*x₂^2
      - 3*A*r*x₁^4*x₂^3
      - 11*A*r*x₁^3*x₂^4
      - 4*A*r*x₁^3*x₂*y₁*y₂
      + 12*A*r*x₁^3*x₂*y₂^2
      - 3*A*r*x₁^2*x₂^5
      - 6*A*r*x₁^2*x₂^2*y₁^2
      + 12*A*r*x₁^2*x₂^2*y₁*y₂
      + 4*A*r*x₁*x₂^6
      - 4*A*r*x₁*x₂^3*y₁^2
      + 12*A*r*x₁*x₂^3*y₁*y₂
      - 12*A*r*x₁*x₂^3*y₂^2
      - A*x₁^5*x₂^3
      + 2*A*x₁^4*x₂^4
      + 3*A*x₁^3*x₂^5
      + 2*A*x₁^3*x₂^2*y₁*y₂
      - 6*A*x₁^3*x₂^2*y₂^2
      - 2*A*x₁^2*x₂^6
      + 2*A*x₁^2*x₂^3*y₁^2
      - 6*A*x₁^2*x₂^3*y₁*y₂
      + 6*A*x₁^2*x₂^3*y₂^2
      - 12*r^10
      + 21*r^9*x₁
      + 3*r^9*x₂
      - 18*r^8*x₁^2
      + 42*r^8*x₁*x₂
      - 18*r^8*x₂^2
      - 21*r^7*x₁^3
      + 9*r^7*x₁^2*x₂
      - 54*r^7*x₁*x₂^2
      + 36*r^7*x₂^3
      + 12*r^7*y₁^2
      - 24*r^7*y₁*y₂
      + 9*r^6*x₁^4
      + 51*r^6*x₁^3*x₂
      - 54*r^6*x₁^2*x₂^2
      - 6*r^6*x₁*x₂^3
      + 3*r^6*x₁*y₁^2
      + 18*r^6*x₁*y₂^2
      + 6*r^6*x₂^4
      - 27*r^6*x₂*y₁^2
      + 48*r^6*x₂*y₁*y₂
      - 18*r^6*x₂*y₂^2
      + 3*r^5*x₁^5
      - 15*r^5*x₁^4*x₂
      - 27*r^5*x₁^3*x₂^2
      + 51*r^5*x₁^2*x₂^3
      - 6*r^5*x₁^2*y₁^2
      - 6*r^5*x₁*x₂^4
      - 18*r^5*x₁*x₂*y₁^2
      + 36*r^5*x₁*x₂*y₁*y₂
      - 18*r^5*x₂^5
      + 18*r^5*x₂^2*y₁^2
      - 24*r^5*x₂^2*y₁*y₂
      - 9*r^4*x₁^5*x₂
      + 9*r^4*x₁^4*x₂^2
      + 21*r^4*x₁^3*x₂^3
      + 6*r^4*x₁^3*y₁*y₂
      - 9*r^4*x₁^3*y₂^2
      + 27*r^4*x₁^2*x₂^4
      + 18*r^4*x₁^2*x₂*y₁^2
      - 18*r^4*x₁^2*x₂*y₁*y₂
      - 45*r^4*x₁^2*x₂*y₂^2
      - 9*r^4*x₁*x₂^5
      + 27*r^4*x₁*x₂^2*y₁^2
      - 72*r^4*x₁*x₂^2*y₁*y₂
      + 45*r^4*x₁*x₂^2*y₂^2
      + 3*r^4*x₂^6
      - 3*r^4*x₂^3*y₁^2
      + 9*r^4*x₂^3*y₂^2
      + 9*r^3*x₁^5*x₂^2
      - 9*r^3*x₁^4*x₂^3
      - 33*r^3*x₁^3*x₂^4
      - 12*r^3*x₁^3*x₂*y₁*y₂
      + 36*r^3*x₁^3*x₂*y₂^2
      - 9*r^3*x₁^2*x₂^5
      - 18*r^3*x₁^2*x₂^2*y₁^2
      + 36*r^3*x₁^2*x₂^2*y₁*y₂
      + 12*r^3*x₁*x₂^6
      - 12*r^3*x₁*x₂^3*y₁^2
      + 36*r^3*x₁*x₂^3*y₁*y₂
      - 36*r^3*x₁*x₂^3*y₂^2
      - 3*r^2*x₁^5*x₂^3
      + 6*r^2*x₁^4*x₂^4
      + 9*r^2*x₁^3*x₂^5
      + 6*r^2*x₁^3*x₂^2*y₁*y₂
      - 18*r^2*x₁^3*x₂^2*y₂^2
      - 6*r^2*x₁^2*x₂^6
      + 6*r^2*x₁^2*x₂^3*y₁^2
      - 18*r^2*x₁^2*x₂^3*y₁*y₂
      + 18*r^2*x₁^2*x₂^3*y₂^2
    )
  )
  * hcurve₁ +
  (
    -(x₁ - x₂)^3 * (
      2*A^3*r^4
      - 7*A^3*r^3*x₁
      - A^3*r^3*x₂
      + 9*A^3*r^2*x₁^2
      + 3*A^3*r^2*x₁*x₂
      - 5*A^3*r*x₁^3
      - 3*A^3*r*x₁^2*x₂
      + A^3*x₁^4
      + A^3*x₁^3*x₂
      + 12*A^2*r^6
      - 37*A^2*r^5*x₁
      - 5*A^2*r^5*x₂
      + 41*A^2*r^4*x₁^2
      + 4*A^2*r^4*x₁*x₂
      + 3*A^2*r^4*x₂^2
      - 20*A^2*r^3*x₁^3
      + 16*A^2*r^3*x₁^2*x₂
      - 9*A^2*r^3*x₁*x₂^2
      + A^2*r^3*x₂^3
      + 4*A^2*r^3*y₁*y₂
      - 2*A^2*r^3*y₂^2
      + 5*A^2*r^2*x₁^4
      - 23*A^2*r^2*x₁^3*x₂
      + 6*A^2*r^2*x₁^2*x₂^2
      + 2*A^2*r^2*x₁*x₂^3
      - 10*A^2*r^2*x₁*y₁*y₂
      + 5*A^2*r^2*x₁*y₂^2
      - 2*A^2*r^2*x₂^4
      - 2*A^2*r^2*x₂*y₁*y₂
      + A^2*r^2*x₂*y₂^2
      - A^2*r*x₁^5
      + 7*A^2*r*x₁^4*x₂
      + 3*A^2*r*x₁^3*x₂^2
      - 7*A^2*r*x₁^2*x₂^3
      + 8*A^2*r*x₁^2*y₁*y₂
      - 4*A^2*r*x₁^2*y₂^2
      + 4*A^2*r*x₁*x₂^4
      + 4*A^2*r*x₁*x₂*y₁*y₂
      - 2*A^2*r*x₁*x₂*y₂^2
      + A^2*x₁^5*x₂
      - 3*A^2*x₁^4*x₂^2
      + 4*A^2*x₁^3*x₂^3
      - 2*A^2*x₁^3*y₁*y₂
      + A^2*x₁^3*y₂^2
      - 2*A^2*x₁^2*x₂^4
      - 2*A^2*x₁^2*x₂*y₁*y₂
      + A^2*x₁^2*x₂*y₂^2
      + 22*A*r^8
      - 55*A*r^7*x₁
      - 7*A*r^7*x₂
      + 48*A*r^6*x₁^2
      - 29*A*r^6*x₁*x₂
      + 15*A*r^6*x₂^2
      - 24*A*r^5*x₁^3
      + 108*A*r^5*x₁^2*x₂
      - 45*A*r^5*x₁*x₂^2
      + 7*A*r^5*x₂^3
      + 20*A*r^5*y₁*y₂
      - 10*A*r^5*y₂^2
      + 10*A*r^4*x₁^4
      - 94*A*r^4*x₁^3*x₂
      + 36*A*r^4*x₁^2*x₂^2
      + A*r^4*x₁*x₂^3
      - 46*A*r^4*x₁*y₁*y₂
      + 24*A*r^4*x₁*y₂^2
      - 9*A*r^4*x₂^4
      - 6*A*r^4*x₂*y₁*y₂
      + 2*A*r^4*x₂*y₂^2
      + 3*A*r^3*x₁^5
      + 23*A*r^3*x₁^4*x₂
      - 2*A*r^3*x₁^3*x₂^2
      - 18*A*r^3*x₁^2*x₂^3
      + 32*A*r^3*x₁^2*y₁*y₂
      - 18*A*r^3*x₁^2*y₂^2
      + 17*A*r^3*x₁*x₂^4
      - A*r^3*x₂^5
      + 2*A*r^3*x₂^2*y₂^2
      - 4*A*r^2*x₁^6
      - 9*A*r^2*x₁^5*x₂
      - 3*A*r^2*x₁^4*x₂^2
      + 8*A*r^2*x₁^3*x₂^3
      - 6*A*r^2*x₁^3*y₁*y₂
      + 4*A*r^2*x₁^3*y₂^2
      - 9*A*r^2*x₁^2*x₂^4
      + 18*A*r^2*x₁^2*x₂*y₁*y₂
      - 6*A*r^2*x₁^2*x₂*y₂^2
      + 3*A*r^2*x₁*x₂^5
      + 6*A*r^2*x₁*x₂^2*y₁*y₂
      - 6*A*r^2*x₁*x₂^2*y₂^2
      - 2*A*r^2*x₂^3*y₁*y₂
      + 8*A*r*x₁^6*x₂
      + 3*A*r*x₁^5*x₂^2
      - A*r*x₁^4*x₂^3
      + 3*A*r*x₁^3*x₂^4
      - 12*A*r*x₁^3*x₂*y₁*y₂
      + 4*A*r*x₁^3*x₂*y₂^2
      - 3*A*r*x₁^2*x₂^5
      - 12*A*r*x₁^2*x₂^2*y₁*y₂
      + 6*A*r*x₁^2*x₂^2*y₂^2
      + 4*A*r*x₁*x₂^3*y₁*y₂
      - 4*A*x₁^6*x₂^2
      + 3*A*x₁^5*x₂^3
      - 2*A*x₁^4*x₂^4
      + A*x₁^3*x₂^5
      + 6*A*x₁^3*x₂^2*y₁*y₂
      - 2*A*x₁^3*x₂^2*y₂^2
      - 2*A*x₁^2*x₂^3*y₁*y₂
      + 12*r^10
      - 21*r^9*x₁
      - 3*r^9*x₂
      + 18*r^8*x₁^2
      - 42*r^8*x₁*x₂
      + 18*r^8*x₂^2
      - 27*r^7*x₁^3
      + 99*r^7*x₁^2*x₂
      - 54*r^7*x₁*x₂^2
      + 12*r^7*x₂^3
      + 24*r^7*y₁*y₂
      - 12*r^7*y₂^2
      + 12*r^6*x₁^4
      - 48*r^6*x₁^3*x₂
      + 54*r^6*x₁^2*x₂^2
      - 15*r^6*x₁*x₂^3
      - 48*r^6*x₁*y₁*y₂
      + 27*r^6*x₁*y₂^2
      - 9*r^6*x₂^4
      - 3*r^6*x₂*y₂^2
      + 18*r^5*x₁^5
      + 6*r^5*x₁^4*x₂
      - 33*r^5*x₁^3*x₂^2
      + 9*r^5*x₁^2*x₂^3
      + 24*r^5*x₁^2*y₁*y₂
      - 18*r^5*x₁^2*y₂^2
      + 15*r^5*x₁*x₂^4
      - 36*r^5*x₁*x₂*y₁*y₂
      + 18*r^5*x₁*x₂*y₂^2
      - 3*r^5*x₂^5
      + 6*r^5*x₂^2*y₂^2
      - 12*r^4*x₁^6
      - 36*r^4*x₁^5*x₂
      + 18*r^4*x₁^4*x₂^2
      - 12*r^4*x₁^3*x₂^3
      + 3*r^4*x₁^3*y₂^2
      - 9*r^4*x₁^2*x₂^4
      + 72*r^4*x₁^2*x₂*y₁*y₂
      - 27*r^4*x₁^2*x₂*y₂^2
      + 9*r^4*x₁*x₂^5
      + 18*r^4*x₁*x₂^2*y₁*y₂
      - 18*r^4*x₁*x₂^2*y₂^2
      - 6*r^4*x₂^3*y₁*y₂
      + 24*r^3*x₁^6*x₂
      + 9*r^3*x₁^5*x₂^2
      - 3*r^3*x₁^4*x₂^3
      + 9*r^3*x₁^3*x₂^4
      - 36*r^3*x₁^3*x₂*y₁*y₂
      + 12*r^3*x₁^3*x₂*y₂^2
      - 9*r^3*x₁^2*x₂^5
      - 36*r^3*x₁^2*x₂^2*y₁*y₂
      + 18*r^3*x₁^2*x₂^2*y₂^2
      + 12*r^3*x₁*x₂^3*y₁*y₂
      - 12*r^2*x₁^6*x₂^2
      + 9*r^2*x₁^5*x₂^3
      - 6*r^2*x₁^4*x₂^4
      + 3*r^2*x₁^3*x₂^5
      + 18*r^2*x₁^3*x₂^2*y₁*y₂
      - 6*r^2*x₁^3*x₂^2*y₂^2
      - 6*r^2*x₁^2*x₂^3*y₁*y₂
    )
  )
  * hcurve₂ +
  (
    -(x₁ - x₂)^3 * (
      - 2*A^3*r^3*x₁
      + 2*A^3*r^3*x₂
      + 5*A^3*r^2*x₁^2
      - 4*A^3*r^2*x₁*x₂
      - A^3*r^2*x₂^2
      - 4*A^3*r*x₁^3
      + 2*A^3*r*x₁^2*x₂
      + 2*A^3*r*x₁*x₂^2
      + A^3*x₁^4
      - A^3*x₁^2*x₂^2
      - 10*A^2*r^5*x₁
      + 10*A^2*r^5*x₂
      + 22*A^2*r^4*x₁^2
      - 18*A^2*r^4*x₁*x₂
      - 4*A^2*r^4*x₂^2
      - 20*A^2*r^3*x₁^3
      + 26*A^2*r^3*x₁^2*x₂
      - 14*A^2*r^3*x₁*x₂^2
      + 8*A^2*r^3*x₂^3
      + 2*A^2*r^3*y₁^2
      - 2*A^2*r^3*y₂^2
      + 7*A^2*r^2*x₁^4
      - 13*A^2*r^2*x₁^3*x₂
      + 12*A^2*r^2*x₁^2*x₂^2
      - 3*A^2*r^2*x₁*x₂^3
      - A^2*r^2*x₁*y₁^2
      - 8*A^2*r^2*x₁*y₁*y₂
      + 9*A^2*r^2*x₁*y₂^2
      - 3*A^2*r^2*x₂^4
      - 5*A^2*r^2*x₂*y₁^2
      + 8*A^2*r^2*x₂*y₁*y₂
      - 3*A^2*r^2*x₂*y₂^2
      - A^2*r*x₁^5
      + 3*A^2*r*x₁^4*x₂
      - 8*A^2*r*x₁^3*x₂^2
      + 8*A^2*r*x₁^2*y₁*y₂
      - 8*A^2*r*x₁^2*y₂^2
      + 9*A^2*r*x₁*x₂^4
      + 2*A^2*r*x₁*x₂*y₁^2
      - 2*A^2*r*x₁*x₂*y₂^2
      - 3*A^2*r*x₂^5
      + 4*A^2*r*x₂^2*y₁^2
      - 8*A^2*r*x₂^2*y₁*y₂
      + 4*A^2*r*x₂^2*y₂^2
      + A^2*x₁^5*x₂
      - A^2*x₁^4*x₂^2
      + 5*A^2*x₁^3*x₂^3
      - 2*A^2*x₁^3*y₁*y₂
      + 2*A^2*x₁^3*y₂^2
      - 6*A^2*x₁^2*x₂^4
      - 2*A^2*x₁^2*x₂*y₁*y₂
      + 2*A^2*x₁^2*x₂*y₂^2
      - A^2*x₁*x₂^2*y₁^2
      + 2*A^2*x₁*x₂^2*y₁*y₂
      - A^2*x₁*x₂^2*y₂^2
      + A^2*x₂^6
      - A^2*x₂^3*y₁^2
      + 2*A^2*x₂^3*y₁*y₂
      - A^2*x₂^3*y₂^2
      - 12*A*r^7*x₁
      + 12*A*r^7*x₂
      + 21*A*r^6*x₁^2
      - 18*A*r^6*x₁*x₂
      - 3*A*r^6*x₂^2
      - 40*A*r^5*x₁^3
      + 96*A*r^5*x₁^2*x₂
      - 96*A*r^5*x₁*x₂^2
      + 40*A*r^5*x₂^3
      + 10*A*r^5*y₁^2
      - 10*A*r^5*y₂^2
      + 19*A*r^4*x₁^4
      - 38*A*r^4*x₁^3*x₂
      + 45*A*r^4*x₁^2*x₂^2
      - 16*A*r^4*x₁*x₂^3
      - 2*A*r^4*x₁*y₁^2
      - 40*A*r^4*x₁*y₁*y₂
      + 42*A*r^4*x₁*y₂^2
      - 10*A*r^4*x₂^4
      - 24*A*r^4*x₂*y₁^2
      + 40*A*r^4*x₂*y₁*y₂
      - 16*A*r^4*x₂*y₂^2
      + 4*A*r^3*x₁^5
      + 6*A*r^3*x₁^4*x₂
      - 44*A*r^3*x₁^3*x₂^2
      + 20*A*r^3*x₁^2*x₂^3
      - 2*A*r^3*x₁^2*y₁^2
      + 32*A*r^3*x₁^2*y₁*y₂
      - 30*A*r^3*x₁^2*y₂^2
      + 30*A*r^3*x₁*x₂^4
      - 16*A*r^3*x₂^5
      + 18*A*r^3*x₂^2*y₁^2
      - 32*A*r^3*x₂^2*y₁*y₂
      + 14*A*r^3*x₂^2*y₂^2
      - 4*A*r^2*x₁^6
      - 12*A*r^2*x₁^5*x₂
      + 6*A*r^2*x₁^4*x₂^2
      + 18*A*r^2*x₁^3*x₂^3
      - 4*A*r^2*x₁^3*y₁*y₂
      + 4*A*r^2*x₁^3*y₂^2
      - 12*A*r^2*x₁^2*x₂^4
      + 6*A*r^2*x₁^2*x₂*y₁^2
      + 12*A*r^2*x₁^2*x₂*y₁*y₂
      - 18*A*r^2*x₁^2*x₂*y₂^2
      + 6*A*r^2*x₁*x₂^2*y₁^2
      - 12*A*r^2*x₁*x₂^2*y₁*y₂
      + 6*A*r^2*x₁*x₂^2*y₂^2
      + 4*A*r^2*x₂^6
      - 4*A*r^2*x₂^3*y₁^2
      + 4*A*r^2*x₂^3*y₁*y₂
      + 8*A*r*x₁^6*x₂
      + 6*A*r*x₁^5*x₂^2
      - 4*A*r*x₁^4*x₂^3
      - 8*A*r*x₁^3*x₂^4
      - 16*A*r*x₁^3*x₂*y₁*y₂
      + 16*A*r*x₁^3*x₂*y₂^2
      - 6*A*r*x₁^2*x₂^5
      - 6*A*r*x₁^2*x₂^2*y₁^2
      + 6*A*r*x₁^2*x₂^2*y₂^2
      + 4*A*r*x₁*x₂^6
      - 4*A*r*x₁*x₂^3*y₁^2
      + 16*A*r*x₁*x₂^3*y₁*y₂
      - 12*A*r*x₁*x₂^3*y₂^2
      - 4*A*x₁^6*x₂^2
      + 2*A*x₁^5*x₂^3
      + 4*A*x₁^3*x₂^5
      + 8*A*x₁^3*x₂^2*y₁*y₂
      - 8*A*x₁^3*x₂^2*y₂^2
      - 2*A*x₁^2*x₂^6
      + 2*A*x₁^2*x₂^3*y₁^2
      - 8*A*x₁^2*x₂^3*y₁*y₂
      + 6*A*x₁^2*x₂^3*y₂^2
      - 48*r^7*x₁^3
      + 108*r^7*x₁^2*x₂
      - 108*r^7*x₁*x₂^2
      + 48*r^7*x₂^3
      + 12*r^7*y₁^2
      - 12*r^7*y₂^2
      + 21*r^6*x₁^4
      + 3*r^6*x₁^3*x₂
      - 21*r^6*x₁*x₂^3
      + 3*r^6*x₁*y₁^2
      - 48*r^6*x₁*y₁*y₂
      + 45*r^6*x₁*y₂^2
      - 3*r^6*x₂^4
      - 27*r^6*x₂*y₁^2
      + 48*r^6*x₂*y₁*y₂
      - 21*r^6*x₂*y₂^2
      + 21*r^5*x₁^5
      - 9*r^5*x₁^4*x₂
      - 60*r^5*x₁^3*x₂^2
      + 60*r^5*x₁^2*x₂^3
      - 6*r^5*x₁^2*y₁^2
      + 24*r^5*x₁^2*y₁*y₂
      - 18*r^5*x₁^2*y₂^2
      + 9*r^5*x₁*x₂^4
      - 18*r^5*x₁*x₂*y₁^2
      + 18*r^5*x₁*x₂*y₂^2
      - 21*r^5*x₂^5
      + 18*r^5*x₂^2*y₁^2
      - 24*r^5*x₂^2*y₁*y₂
      + 6*r^5*x₂^2*y₂^2
      - 12*r^4*x₁^6
      - 45*r^4*x₁^5*x₂
      + 27*r^4*x₁^4*x₂^2
      + 9*r^4*x₁^3*x₂^3
      + 6*r^4*x₁^3*y₁*y₂
      - 6*r^4*x₁^3*y₂^2
      + 18*r^4*x₁^2*x₂^4
      + 18*r^4*x₁^2*x₂*y₁^2
      + 54*r^4*x₁^2*x₂*y₁*y₂
      - 72*r^4*x₁^2*x₂*y₂^2
      + 27*r^4*x₁*x₂^2*y₁^2
      - 54*r^4*x₁*x₂^2*y₁*y₂
      + 27*r^4*x₁*x₂^2*y₂^2
      + 3*r^4*x₂^6
      - 3*r^4*x₂^3*y₁^2
      - 6*r^4*x₂^3*y₁*y₂
      + 9*r^4*x₂^3*y₂^2
      + 24*r^3*x₁^6*x₂
      + 18*r^3*x₁^5*x₂^2
      - 12*r^3*x₁^4*x₂^3
      - 24*r^3*x₁^3*x₂^4
      - 48*r^3*x₁^3*x₂*y₁*y₂
      + 48*r^3*x₁^3*x₂*y₂^2
      - 18*r^3*x₁^2*x₂^5
      - 18*r^3*x₁^2*x₂^2*y₁^2
      + 18*r^3*x₁^2*x₂^2*y₂^2
      + 12*r^3*x₁*x₂^6
      - 12*r^3*x₁*x₂^3*y₁^2
      + 48*r^3*x₁*x₂^3*y₁*y₂
      - 36*r^3*x₁*x₂^3*y₂^2
      - 12*r^2*x₁^6*x₂^2
      + 6*r^2*x₁^5*x₂^3
      + 12*r^2*x₁^3*x₂^5
      + 24*r^2*x₁^3*x₂^2*y₁*y₂
      - 24*r^2*x₁^3*x₂^2*y₂^2
      - 6*r^2*x₁^2*x₂^6
      + 6*r^2*x₁^2*x₂^3*y₁^2
      - 24*r^2*x₁^2*x₂^3*y₁*y₂
      + 18*r^2*x₁^2*x₂^3*y₂^2
    )
  )
  * htors
```
