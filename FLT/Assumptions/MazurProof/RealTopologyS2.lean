import FLT.Assumptions.MazurProof.RealTopologyS3

/-!
# Real topology route, S2: coordinate interface

This file gives stable names to the Mathlib affine group-law formulas used by
the S3 algebra and records the rational-to-real base-change map on points.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.RealTopology

/-- Non-vertical affine addition on the short model, with Mathlib's explicit coordinates. -/
theorem shortW_point_add_some
    {A B x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂)) :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
      WeierstrassCurve.Affine.Point.some
        (WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
          (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂))
        (WeierstrassCurve.Affine.addY (shortW A B) x₁ x₂ y₁
          (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂))
        (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy) :=
  WeierstrassCurve.Affine.Point.add_some (W := shortW A B) hxy

/-- Vertical affine addition on the short model. -/
theorem shortW_point_add_vertical
    {A B x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hx : x₁ = x₂)
    (hy : y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂) :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ = 0 :=
  WeierstrassCurve.Affine.Point.add_of_Y_eq (W := shortW A B) hx hy

/-- The rational-to-real base-change map on affine points. -/
noncomputable def rationalPointBaseChange (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Affine.Point.baseChange ℚ ℝ

/-- The rational-to-real base-change map is injective. -/
theorem rationalPointBaseChange_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (rationalPointBaseChange E) := by
  unfold rationalPointBaseChange
  exact WeierstrassCurve.Affine.Point.map_injective (W' := E) (f := Algebra.ofId ℚ ℝ)

end MazurProof.RealTopology
