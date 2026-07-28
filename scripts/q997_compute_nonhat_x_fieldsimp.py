#!/usr/bin/env python3
"""Q997: exact non-hat Vélu X-coordinate certificate and field_simp audit.

This script computes four distinct but related objects.

1. The reduced/primitive numerator
      numerator(cancel(together(lhs - rhs))).
2. Its exact certificate against hcurve1, hcurve2, and htors.
3. The uncancelled/direct numerator
      numerator(together(lhs - rhs)).
4. The compact-normalized common-denominator numerator obtained after exposing
   the common factor x1-x2 in X1'-X2' and rewriting x3-r by its polynomial
   numerator.

The two denominator-clearings differ by two powers of x1-x2:

    direct/raw multiplier     = -(x1-x2)^3,
    compact field multiplier  = -(x1-x2).

The script prints every coefficient fully expanded and emits a Lean file that
checks both normalizations with Mathlib's field_simp and linear_combination.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

import sympy as sp


# ---------------------------------------------------------------------------
# 1. Full rational identity
# ---------------------------------------------------------------------------
x1, x2, y1, y2, A, B, r = sp.symbols("x1 x2 y1 y2 A B r")
t = 3 * r**2 + A

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
diff = lhs - rhs

raw_rat = sp.together(diff)
raw_num_expr, raw_den_expr = sp.fraction(raw_rat)
raw_num = sp.expand(raw_num_expr)
raw_den = sp.expand(raw_den_expr)

reduced_rat = sp.cancel(raw_rat)
num_expr, den_expr = sp.fraction(reduced_rat)
num = sp.expand(num_expr)
den = sp.expand(den_expr)

s = x1 - x2
raw_multiplier = sp.factor(sp.cancel(raw_num / num))
assert raw_multiplier == -s**3
assert sp.expand(raw_num - raw_multiplier * num) == 0
assert sp.expand(raw_num * den - num * raw_den) == 0


# ---------------------------------------------------------------------------
# 2. Primitive certificate
# ---------------------------------------------------------------------------
B0 = -(r**3 + A * r)
g1 = sp.expand(y1**2 - x1**3 - A * x1 - B0)
g2 = sp.expand(y2**2 - x2**3 - A * x2 - B0)

c1_raw, rem1 = sp.div(num, g1, y1)
c2_raw, rem2 = sp.div(sp.expand(rem1), g2, y2)
c1 = sp.expand(c1_raw)
c2 = sp.expand(c2_raw)
c3 = sp.expand(c1 + c2)

hcurve1 = y1**2 - x1**3 - A * x1 - B
hcurve2 = y2**2 - x2**3 - A * x2 - B
htors = r**3 + A * r + B

assert sp.expand(rem2) == 0
assert sp.expand(g1 - (hcurve1 + htors)) == 0
assert sp.expand(g2 - (hcurve2 + htors)) == 0
assert sp.expand(num - c1 * hcurve1 - c2 * hcurve2 - c3 * htors) == 0
assert all(B not in c.free_symbols for c in (c1, c2, c3))

raw_c1 = sp.expand(raw_multiplier * c1)
raw_c2 = sp.expand(raw_multiplier * c2)
raw_c3 = sp.expand(raw_multiplier * c3)
assert sp.expand(raw_num - raw_c1 * hcurve1 - raw_c2 * hcurve2 - raw_c3 * htors) == 0


# ---------------------------------------------------------------------------
# 3. Compact denominator normalization
# ---------------------------------------------------------------------------
d1 = x1 - r
d2 = x2 - r
u = y1 - y2
k = d1 * d2 - t
D3 = u**2 - s**2 * (x1 + x2 + r)
e1 = d1**2 - t
e2 = d2**2 - t
m1 = x1 * d1 + t
m2 = x2 * d2 + t
P = y1 * e1 * d2**2 - y2 * e2 * d1**2

assert sp.cancel(x3 - r - D3 / s**2) == 0
assert sp.cancel(X1p - X2p - s * k / (d1 * d2)) == 0
assert sp.cancel(ellp - P / (d1 * d2 * s * k)) == 0

lhs_compact = u**2 / s**2 - x1 - x2 + t * s**2 / D3
rhs_compact = (P / (d1 * d2 * s * k)) ** 2 - m1 / d1 - m2 / d2
compact_diff = lhs_compact - rhs_compact
assert sp.cancel(compact_diff - diff) == 0

# This is the LCM after the shared s^2 has been exposed explicitly.
compact_den = sp.expand(d1**2 * d2**2 * s**2 * k**2 * D3)
compact_num_rat = sp.cancel(compact_den * compact_diff)
compact_num_expr, compact_residual_den = sp.fraction(compact_num_rat)
assert sp.expand(compact_residual_den - 1) == 0
compact_num = sp.expand(compact_num_expr)
compact_multiplier = sp.factor(sp.cancel(compact_num / num))
assert compact_multiplier == -s
assert sp.expand(compact_num - compact_multiplier * num) == 0

compact_c1 = sp.expand(compact_multiplier * c1)
compact_c2 = sp.expand(compact_multiplier * c2)
compact_c3 = sp.expand(compact_multiplier * c3)
assert sp.expand(
    compact_num
    - compact_c1 * hcurve1
    - compact_c2 * hcurve2
    - compact_c3 * htors
) == 0


# ---------------------------------------------------------------------------
# 4. Literal side cross multiplication
# ---------------------------------------------------------------------------
lhs_num_expr, lhs_den_expr = sp.fraction(sp.together(lhs))
rhs_num_expr, rhs_den_expr = sp.fraction(sp.together(rhs))
lhs_num, lhs_den = sp.expand(lhs_num_expr), sp.expand(lhs_den_expr)
rhs_num, rhs_den = sp.expand(rhs_num_expr), sp.expand(rhs_den_expr)

product_den = sp.expand(lhs_den * rhs_den)
product_num = sp.expand(lhs_num * rhs_den - rhs_num * lhs_den)
product_multiplier = sp.factor(sp.cancel(product_num / num))
assert sp.denom(sp.together(product_multiplier)) == 1
assert product_multiplier == raw_multiplier
assert sp.expand(product_num - raw_num) == 0
assert sp.expand(product_den - raw_den) == 0


# ---------------------------------------------------------------------------
# 5. Lean printer
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
    text = sp.sstr(expr, order="lex").replace("**", "^")
    for old, new in LEAN_NAMES.items():
        text = re.sub(rf"\b{re.escape(old)}\b", new, text)
    return text


def lean_sum_lines(expr: sp.Expr, continuation_indent: str) -> list[str]:
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


def emit_abbrev(name: str, expr: sp.Expr) -> list[str]:
    lines = [f"abbrev {name} (x₁ x₂ y₁ y₂ A r : Rat) : Rat :="]
    body = lean_sum_lines(expr, "  ")
    lines.append("  " + body[0])
    lines.extend(body[1:])
    return lines


def emit_lean_file() -> str:
    c1_call = "q997_c1 x₁ x₂ y₁ y₂ A r"
    c2_call = "q997_c2 x₁ x₂ y₁ y₂ A r"
    c3_call = "q997_c3 x₁ x₂ y₁ y₂ A r"

    lines: list[str] = [
        "import Mathlib",
        "",
        "set_option autoImplicit false",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
    ]
    for name, coeff in (("q997_c1", c1), ("q997_c2", c2), ("q997_c3", c3)):
        lines.extend(emit_abbrev(name, coeff))
        lines.append("")

    lines.extend([
        "/-- Direct syntactic form.  field_simp retains the hidden duplicate",
        "`(x₁-x₂)^2` coming from the denominator of `X₁-X₂`, so the exact",
        "certificate multiplier is `-(x₁-x₂)^3`. -/",
        "example",
        "    (x₁ x₂ y₁ y₂ A B r : Rat)",
        "    (hcurve₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B)",
        "    (hcurve₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)",
        "    (htors : r ^ 3 + A * r + B = 0)",
        "    (ha₁ : x₁ - r ≠ 0)",
        "    (ha₂ : x₂ - r ≠ 0)",
        "    (hd : x₁ - x₂ ≠ 0)",
        "    (hnh : (x₁ - r) * (x₂ - r) - (3 * r ^ 2 + A) ≠ 0)",
        "    (hx₃r :",
        "      (((y₁ - y₂) / (x₁ - x₂)) ^ 2 - x₁ - x₂) - r ≠ 0) :",
        "    let t : Rat := 3 * r ^ 2 + A",
        "    let ell : Rat := (y₁ - y₂) / (x₁ - x₂)",
        "    let x₃ : Rat := ell ^ 2 - x₁ - x₂",
        "    let X₁ : Rat := x₁ + t / (x₁ - r)",
        "    let X₂ : Rat := x₂ + t / (x₂ - r)",
        "    let Y₁ : Rat := y₁ * ((x₁ - r) ^ 2 - t) / (x₁ - r) ^ 2",
        "    let Y₂ : Rat := y₂ * ((x₂ - r) ^ 2 - t) / (x₂ - r) ^ 2",
        "    let ell' : Rat := (Y₁ - Y₂) / (X₁ - X₂)",
        "    x₃ + t / (x₃ - r) = ell' ^ 2 - X₁ - X₂ := by",
        "  dsimp",
        "  have hXeq :",
        "      (x₁ + (3 * r ^ 2 + A) / (x₁ - r))",
        "          - (x₂ + (3 * r ^ 2 + A) / (x₂ - r)) =",
        "        (x₁ - x₂) *",
        "            ((x₁ - r) * (x₂ - r) - (3 * r ^ 2 + A)) /",
        "          ((x₁ - r) * (x₂ - r)) := by",
        "    field_simp [ha₁, ha₂]",
        "    ring",
        "  have hX :",
        "      (x₁ + (3 * r ^ 2 + A) / (x₁ - r))",
        "          - (x₂ + (3 * r ^ 2 + A) / (x₂ - r)) ≠ 0 := by",
        "    rw [hXeq]",
        "    exact div_ne_zero (mul_ne_zero hd hnh) (mul_ne_zero ha₁ ha₂)",
        "  field_simp [ha₁, ha₂, hd, hX, hx₃r]",
        "  linear_combination",
        f"      (-((x₁ - x₂) ^ 3) * {c1_call}) * hcurve₁",
        f"    + (-((x₁ - x₂) ^ 3) * {c2_call}) * hcurve₂",
        f"    + (-((x₁ - x₂) ^ 3) * {c3_call}) * htors",
        "",
        "/-- Compact-normalized form.  Once `X₁-X₂` and `x₃-r` are exposed",
        "with their polynomial numerators, field_simp uses the true LCM and the",
        "exact multiplier drops to `-(x₁-x₂)`. -/",
        "example",
        "    (x₁ x₂ y₁ y₂ A B r : Rat)",
        "    (hcurve₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B)",
        "    (hcurve₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)",
        "    (htors : r ^ 3 + A * r + B = 0)",
        "    (ha₁ : x₁ - r ≠ 0)",
        "    (ha₂ : x₂ - r ≠ 0)",
        "    (hd : x₁ - x₂ ≠ 0)",
        "    (hnh : (x₁ - r) * (x₂ - r) - (3 * r ^ 2 + A) ≠ 0)",
        "    (hD3 :",
        "      (y₁ - y₂) ^ 2 -",
        "          (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) ≠ 0) :",
        "    let t : Rat := 3 * r ^ 2 + A",
        "    let d₁ : Rat := x₁ - r",
        "    let d₂ : Rat := x₂ - r",
        "    let s : Rat := x₁ - x₂",
        "    let u : Rat := y₁ - y₂",
        "    let k : Rat := d₁ * d₂ - t",
        "    let D3 : Rat := u ^ 2 - s ^ 2 * (x₁ + x₂ + r)",
        "    let e₁ : Rat := d₁ ^ 2 - t",
        "    let e₂ : Rat := d₂ ^ 2 - t",
        "    let m₁ : Rat := x₁ * d₁ + t",
        "    let m₂ : Rat := x₂ * d₂ + t",
        "    let P : Rat := y₁ * e₁ * d₂ ^ 2 - y₂ * e₂ * d₁ ^ 2",
        "    u ^ 2 / s ^ 2 - x₁ - x₂ + t * s ^ 2 / D3 =",
        "      (P / (d₁ * d₂ * s * k)) ^ 2 - m₁ / d₁ - m₂ / d₂ := by",
        "  dsimp",
        "  field_simp [ha₁, ha₂, hd, hnh, hD3]",
        "  linear_combination",
        f"      (-(x₁ - x₂) * {c1_call}) * hcurve₁",
        f"    + (-(x₁ - x₂) * {c2_call}) * hcurve₂",
        f"    + (-(x₁ - x₂) * {c3_call}) * htors",
        "",
    ])
    return "\n".join(lines)


def term_count(expr: sp.Expr) -> int:
    expr = sp.expand(expr)
    return 0 if expr == 0 else len(expr.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def print_definition(name: str, expr: sp.Expr) -> None:
    for line in emit_abbrev(name, expr):
        print(line)


def report(lean_output: Path) -> None:
    print("ANSWER Q997 59ff0e15")
    print()
    print("## Exact normalization results")
    print()
    print(f"- SymPy version: `{sp.__version__}`")
    print(f"- primitive numerator terms: `{term_count(num)}`")
    print(f"- direct/raw numerator terms: `{term_count(raw_num)}`")
    print(f"- primitive c1/c2/c3 terms: `{term_count(c1)}`, `{term_count(c2)}`, `{term_count(c3)}`")
    print(f"- direct/raw multiplier: `{sp.factor(raw_multiplier)}`")
    print(f"- compact field_simp multiplier: `{sp.factor(compact_multiplier)}`")
    print(f"- literal side-product multiplier: `{sp.factor(product_multiplier)}`")
    print(f"- direct/raw denominator: `{sp.factor(raw_den)}`")
    print(f"- reduced denominator: `{sp.factor(den)}`")
    print(f"- compact denominator: `{sp.factor(compact_den)}`")
    print(f"- lhs denominator: `{sp.factor(lhs_den)}`")
    print(f"- rhs denominator: `{sp.factor(rhs_den)}`")
    print(f"- generated Lean checker: `{lean_output}`")
    print()
    print("The exact relations are")
    print()
    print("```text")
    print("N_direct = -(x1-x2)^3 * N_primitive")
    print("N_compact = -(x1-x2)   * N_primitive")
    print("N_product = N_direct")
    print("```")
    print()
    print("## Exact Lean commands")
    print()
    print("### Primitive/cancelled numerator")
    print("```lean")
    print("linear_combination")
    print("    q997_c1 x₁ x₂ y₁ y₂ A r * hcurve₁")
    print("  + q997_c2 x₁ x₂ y₁ y₂ A r * hcurve₂")
    print("  + q997_c3 x₁ x₂ y₁ y₂ A r * htors")
    print("```")
    print()
    print("### Direct field_simp / literal side cross-product")
    print("```lean")
    print("linear_combination")
    print("    (-((x₁ - x₂) ^ 3) * q997_c1 x₁ x₂ y₁ y₂ A r) * hcurve₁")
    print("  + (-((x₁ - x₂) ^ 3) * q997_c2 x₁ x₂ y₁ y₂ A r) * hcurve₂")
    print("  + (-((x₁ - x₂) ^ 3) * q997_c3 x₁ x₂ y₁ y₂ A r) * htors")
    print("```")
    print()
    print("### Compact-normalized field_simp")
    print("```lean")
    print("linear_combination")
    print("    (-(x₁ - x₂) * q997_c1 x₁ x₂ y₁ y₂ A r) * hcurve₁")
    print("  + (-(x₁ - x₂) * q997_c2 x₁ x₂ y₁ y₂ A r) * hcurve₂")
    print("  + (-(x₁ - x₂) * q997_c3 x₁ x₂ y₁ y₂ A r) * htors")
    print("```")
    print()
    print("## Fully expanded primitive coefficients")
    print()
    print("```lean")
    print_definition("q997_c1", c1)
    print()
    print_definition("q997_c2", c2)
    print()
    print_definition("q997_c3", c3)
    print("```")
    print()
    print("## Fully expanded direct/raw coefficients")
    print()
    print("```lean")
    print_definition("q997_raw_c1", raw_c1)
    print()
    print_definition("q997_raw_c2", raw_c2)
    print()
    print_definition("q997_raw_c3", raw_c3)
    print("```")
    print()
    print("## Fully expanded compact-normalized coefficients")
    print()
    print("```lean")
    print_definition("q997_compact_c1", compact_c1)
    print()
    print_definition("q997_compact_c2", compact_c2)
    print()
    print_definition("q997_compact_c3", compact_c3)
    print("```")
    print()
    print("## Verification hashes")
    print()
    print(f"- primitive numerator: `{digest(num)}`")
    print(f"- direct numerator: `{digest(raw_num)}`")
    print(f"- c1: `{digest(c1)}`")
    print(f"- c2: `{digest(c2)}`")
    print(f"- c3: `{digest(c3)}`")
    print(f"- direct c1: `{digest(raw_c1)}`")
    print(f"- direct c2: `{digest(raw_c2)}`")
    print(f"- direct c3: `{digest(raw_c3)}`")
    print(f"- compact c1: `{digest(compact_c1)}`")
    print(f"- compact c2: `{digest(compact_c2)}`")
    print(f"- compact c3: `{digest(compact_c3)}`")
    print()
    print("All SymPy assertions passed.")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--lean-output",
        type=Path,
        default=Path("scripts/Q997GeneratedFieldSimpCheck.lean"),
    )
    args = parser.parse_args()
    args.lean_output.write_text(emit_lean_file(), encoding="utf-8")
    report(args.lean_output)


if __name__ == "__main__":
    main()
