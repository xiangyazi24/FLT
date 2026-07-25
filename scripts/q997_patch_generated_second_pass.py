#!/usr/bin/env python3
"""Patch the generated Q997 Lean checker with the exact second field_simp pass.

On the completely unnormalized source expression, the first `field_simp`
clears the denominators visible before normalization, but it then exposes two
new polynomial denominators:

* the numerator of `x3-r`, in the visible form
    u^2 - x1*s^2 - x2*s^2 - s^2*r;
* the numerator of `X1'-X2'`, in the visible form
    d2*m1 - d1*m2 = s*k.

This patch derives nonzeroness for exactly those two expressions and performs
a second `field_simp`.  The resulting polynomial is the direct/raw numerator,
namely `-(x1-x2)^3` times the primitive numerator.
"""

from pathlib import Path

path = Path("scripts/Q997GeneratedFieldSimpCheck.lean")
text = path.read_text(encoding="utf-8")

old = """  field_simp [ha₁, ha₂, hd, hX, hx₃r]
  linear_combination
"""

new = """  have hx3eq :
      (((y₁ - y₂) / (x₁ - x₂)) ^ 2 - x₁ - x₂) - r =
        ((y₁ - y₂) ^ 2 - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r)) /
          (x₁ - x₂) ^ 2 := by
    field_simp [hd]
    ring
  have hD3 :
      (y₁ - y₂) ^ 2 - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) ≠ 0 := by
    intro hzero
    apply hx₃r
    rw [hx3eq, hzero]
    simp
  have hD3_visible :
      (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 - x₂ * (x₁ - x₂) ^ 2 -
          (x₁ - x₂) ^ 2 * r ≠ 0 := by
    intro hzero
    apply hD3
    calc
      (y₁ - y₂) ^ 2 - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) =
          (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
              x₂ * (x₁ - x₂) ^ 2 - (x₁ - x₂) ^ 2 * r := by ring
      _ = 0 := hzero
  have hQ :
      (x₂ - r) * (x₁ * (x₁ - r) + (3 * r ^ 2 + A)) -
          (x₁ - r) * (x₂ * (x₂ - r) + (3 * r ^ 2 + A)) ≠ 0 := by
    have hQeq :
        (x₂ - r) * (x₁ * (x₁ - r) + (3 * r ^ 2 + A)) -
            (x₁ - r) * (x₂ * (x₂ - r) + (3 * r ^ 2 + A)) =
          (x₁ - x₂) *
            ((x₁ - r) * (x₂ - r) - (3 * r ^ 2 + A)) := by
      ring
    rw [hQeq]
    exact mul_ne_zero hd hnh
  field_simp [ha₁, ha₂, hd, hX, hx₃r]
  field_simp [hD3_visible, hQ]
  linear_combination
"""

if text.count(old) != 1:
    raise RuntimeError(
        f"expected exactly one direct field_simp snippet, found {text.count(old)}"
    )

path.write_text(text.replace(old, new), encoding="utf-8")
