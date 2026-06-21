import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open WeierstrassCurve
open WeierstrassCurve.Affine

namespace Seam2Proto

/-- The completed-square affine `Y` coordinate. -/
def YsqCoord (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  2 * y + W.a₁ * x + W.a₃

/-- The right hand side of the completed-square Weierstrass equation. -/
def fY (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- The completed-square formula for `x(P + Q)` in affine coordinates. -/
def xPlusFormula (W : WeierstrassCurve ℚ) (x₁ x₂ Y₁ Y₂ : ℚ) : ℚ :=
  (((Y₁ - Y₂) / (x₁ - x₂)) ^ 2 - W.b₂) / 4 - x₁ - x₂

/-- The completed-square formula for `x(P - Q)` in affine coordinates. -/
def xMinusFormula (W : WeierstrassCurve ℚ) (x₁ x₂ Y₁ Y₂ : ℚ) : ℚ :=
  (((Y₁ + Y₂) / (x₁ - x₂)) ^ 2 - W.b₂) / 4 - x₁ - x₂

theorem YsqCoord_sq_of_equation (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hxy : W.toAffine.Equation x y) :
    YsqCoord W x y ^ 2 = fY W x := by
  rw [WeierstrassCurve.Affine.equation_iff] at hxy
  simp only [YsqCoord, fY, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  linear_combination (norm := ring1) 4 * hxy

theorem YsqCoord_negY (W : WeierstrassCurve ℚ) (x y : ℚ) :
    YsqCoord W x (W.toAffine.negY x y) = -YsqCoord W x y := by
  simp only [YsqCoord, WeierstrassCurve.Affine.negY]
  ring

theorem addX_eq_completed_square_formula_of_ne_x (W : WeierstrassCurve ℚ)
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      (((YsqCoord W x₁ y₁ - YsqCoord W x₂ y₂) / (x₁ - x₂)) ^ 2 - W.b₂) / 4
        - x₁ - x₂ := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, YsqCoord, WeierstrassCurve.b₂]
  field_simp [sub_ne_zero.mpr hx]
  ring

theorem subX_eq_completed_square_formula_of_ne_x (W : WeierstrassCurve ℚ)
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) =
      (((YsqCoord W x₁ y₁ + YsqCoord W x₂ y₂) / (x₁ - x₂)) ^ 2 - W.b₂) / 4
        - x₁ - x₂ := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, YsqCoord,
    WeierstrassCurve.b₂]
  field_simp [sub_ne_zero.mpr hx]
  ring

private theorem differential_addition_affine_sum_cert_core (W : WeierstrassCurve ℚ)
    {x₁ x₂ Y₁ Y₂ : ℚ}
    (hY₁ : Y₁ ^ 2 = fY W x₁) (hY₂ : Y₂ ^ 2 = fY W x₂) :
    Y₁ ^ 2 - 2 * W.b₄ * x₁ - W.b₂ * x₁ ^ 2 - 4 * x₁ ^ 3
      - W.b₂ * x₂ ^ 2 - 2 * W.b₄ * x₂ - 4 * x₂ ^ 3 + Y₂ ^ 2
      - 2 * W.b₆ = 0 := by
  unfold fY at hY₁ hY₂
  ring_nf at hY₁ hY₂ ⊢
  linear_combination (norm := ring1) (1 : ℚ) * hY₁ + (1 : ℚ) * hY₂

theorem differential_addition_affine_sum_cert (W : WeierstrassCurve ℚ)
    {x₁ x₂ Y₁ Y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hY₁ : Y₁ ^ 2 = fY W x₁) (hY₂ : Y₂ ^ 2 = fY W x₂) :
    (x₁ - x₂) ^ 2 * (xPlusFormula W x₁ x₂ Y₁ Y₂ + xMinusFormula W x₁ x₂ Y₁ Y₂) =
      2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆ := by
  unfold xPlusFormula xMinusFormula
  field_simp [sub_ne_zero.mpr hx]
  ring_nf
  have hcore := differential_addition_affine_sum_cert_core (W := W) (x₁ := x₁) (x₂ := x₂)
    (Y₁ := Y₁) (Y₂ := Y₂) hY₁ hY₂
  linear_combination (norm := ring1) (2 : ℚ) * hcore

theorem differential_addition_affine_prod_cert (W : WeierstrassCurve ℚ)
    {x₁ x₂ Y₁ Y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hY₁ : Y₁ ^ 2 = fY W x₁) (hY₂ : Y₂ ^ 2 = fY W x₂) :
    (x₁ - x₂) ^ 2 * xPlusFormula W x₁ x₂ Y₁ Y₂ * xMinusFormula W x₁ x₂ Y₁ Y₂ =
      x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈ := by
  unfold xPlusFormula xMinusFormula fY at *
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (norm := ring1)
    (Y₁ ^ 2 - 2 * Y₂ ^ 2 - W.b₂ * x₁ ^ 2 + 4 * W.b₂ * x₁ * x₂
      - 2 * W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₁ + W.b₆ - 4 * x₁ ^ 3
      + 8 * x₁ ^ 2 * x₂ + 8 * x₁ * x₂ ^ 2 - 8 * x₂ ^ 3) * hY₁
    + (Y₂ ^ 2 - 4 * W.b₂ * x₁ ^ 2 + 4 * W.b₂ * x₁ * x₂
      - W.b₂ * x₂ ^ 2 - 4 * W.b₄ * x₁ + 2 * W.b₄ * x₂ - W.b₆
      - 16 * x₁ ^ 3 + 8 * x₁ ^ 2 * x₂ + 8 * x₁ * x₂ ^ 2 - 4 * x₂ ^ 3)
        * hY₂
    + (4 * x₁ ^ 2 - 8 * x₁ * x₂ + 4 * x₂ ^ 2) * W.b_relation

end Seam2Proto
