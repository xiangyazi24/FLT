import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0

/-- Preliminary exact checks for the algebraic reductions used by Q999. -/
example
    (x₁ x₂ y₁ y₂ A B r : Rat)
    (hcurve₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B)
    (hcurve₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)
    (htors : r ^ 3 + A * r + B = 0)
    (hat : (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A)
    (h_ya_ne : y₁ * (x₂ - r) - y₂ * (x₁ - r) ≠ 0) :
    y₁ * (x₂ - r) + y₂ * (x₁ - r) = 0 := by
  have hprod :
      (y₁ * (x₂ - r) - y₂ * (x₁ - r)) *
          (y₁ * (x₂ - r) + y₂ * (x₁ - r)) = 0 := by
    linear_combination
        (x₂ - r) ^ 2 * hcurve₁
      - (x₁ - r) ^ 2 * hcurve₂
      + ((x₂ - r) ^ 2 - (x₁ - r) ^ 2) * htors
      + ((x₁ - r) * (x₂ - r) * (x₁ - x₂)) * hat
  exact (mul_eq_zero.mp hprod).resolve_left h_ya_ne

example
    (x₁ x₂ y₁ A B r : Rat)
    (hcurve₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B)
    (htors : r ^ 3 + A * r + B = 0)
    (hat : (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A) :
    y₁ ^ 2 - (x₁ - r) ^ 2 * (x₁ + x₂ + r) = 0 := by
  linear_combination hcurve₁ + htors - (x₁ - r) * hat

example
    (x₁ x₂ A r : Rat)
    (hat : (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A) :
    A = (x₁ - r) * (x₂ - r) - 3 * r ^ 2 := by
  linear_combination -hat

example
    (A B r : Rat)
    (htors : r ^ 3 + A * r + B = 0) :
    B = -(r ^ 3 + A * r) := by
  linear_combination htors

example
    (x₁ x₂ r : Rat)
    (ha₁ : x₁ - r ≠ 0)
    (hd : x₁ - x₂ ≠ 0) :
    (x₁ - r) ^ 2 - (x₁ - r) * (x₂ - r) ≠ 0 := by
  rw [show
    (x₁ - r) ^ 2 - (x₁ - r) * (x₂ - r) =
      (x₁ - r) * (x₁ - x₂) by ring]
  exact mul_ne_zero ha₁ hd
