import Mathlib

/-!
# Torsion order checks for `E20 : y² = x³ + x² - x`

This scratch file uses Mathlib's affine Weierstrass points and their group law.
-/

namespace Scratch.E20_TorsionOrder

open WeierstrassCurve

noncomputable section

/-- The curve `20.a4`: `y² = x³ + x² - x`. -/
def E20 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -1
  a₆ := 0

/-- The curve is elliptic; its discriminant is `80`. -/
instance E20_isElliptic : E20.IsElliptic where
  isUnit := by
    apply isUnit_iff_ne_zero.mpr
    norm_num [E20, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The affine point `(0,0)` satisfies the Weierstrass equation of `E20`. -/
theorem P0_equation : E20.Equation (0 : ℚ) (0 : ℚ) := by
  simp [E20]

/-- The affine point `(0,0)` is nonsingular on `E20`. -/
theorem P0_nonsingular : E20.Nonsingular (0 : ℚ) (0 : ℚ) := by
  simp [E20]

/-- The point `P0 = (0,0)` on `E20`. -/
def P0 : E20.Point :=
  WeierstrassCurve.Affine.Point.some (W' := E20) (0 : ℚ) (0 : ℚ) P0_nonsingular

/-- `P0` is not the point at infinity. -/
theorem P0_ne_zero : P0 ≠ 0 := by
  dsimp [P0]
  exact WeierstrassCurve.Affine.Point.some_ne_zero P0_nonsingular

/-- Doubling `(0,0)` gives the point at infinity. -/
theorem P0_add_self : P0 + P0 = 0 := by
  dsimp [P0]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (W := E20) (x₁ := (0 : ℚ)) (y₁ := (0 : ℚ)) (h₁ := P0_nonsingular)
    (by simp [E20])

/-- The known rational point `(0,0)` has additive order `2`. -/
theorem addOrderOf_P0 : addOrderOf P0 = 2 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 2)]
  constructor
  · simpa [two_nsmul] using P0_add_self
  · intro m hm hmpos
    have hm1 : m = 1 := by omega
    subst m
    simpa using P0_ne_zero

end

end Scratch.E20_TorsionOrder
