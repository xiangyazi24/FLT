#!/usr/bin/env python3
"""Patch the generated Q997 Lean checker with the second D3 field_simp pass.

The first field_simp on the completely unnormalized source expression clears
all visible denominators but exposes one new inverse: the polynomial numerator
D3 of x3-r.  This patch inserts the exact nonzero derivation, identifies the
ring-normalized denominator left by the first pass, and runs field_simp again.
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
  have hden :
      (-(y₁ * y₂ * 2) + y₁ ^ 2 + y₂ ^ 2 + x₁ * x₂ * r * 2 +
            x₁ * x₂ ^ 2 + x₁ ^ 2 * x₂ - x₁ ^ 2 * r - x₁ ^ 3 -
            x₂ ^ 2 * r - x₂ ^ 3) =
        (y₁ - y₂) ^ 2 - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) := by
    ring
  field_simp [ha₁, ha₂, hd, hX, hx₃r]
  rw [hden]
  field_simp [hD3]
  linear_combination
"""

if text.count(old) != 1:
    raise RuntimeError(f"expected exactly one direct field_simp snippet, found {text.count(old)}")

path.write_text(text.replace(old, new), encoding="utf-8")
