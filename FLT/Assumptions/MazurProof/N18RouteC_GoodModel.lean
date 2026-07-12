import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The explicit good model at `pi = a - 1`

This records the admissible change of variables from the base-changed
`162.c3` equation to the integral equation used at the prime above `3`.
The scaling parameter is `a^2-a-3 = pi * (2-a^2)`; the second factor is a
local unit.  Point-level transport is developed separately from this finite
coefficient certificate.
-/

namespace MazurProof.N18RouteC.GoodModel

noncomputable section

private theorem a_pow_fifteen :
    a ^ 15 = 1548 * a ^ 2 + 3417 * a + 1000 := by
  calc
    a ^ 15 = a * a ^ 14 := by ring
    _ = 1548 * a ^ 2 + 3417 * a + 1000 := by
      rw [a_pow_fourteen]
      ring_nf
      rw [a_cubic]
      ring

private theorem a_pow_sixteen :
    a ^ 16 = 3417 * a ^ 2 + 5644 * a + 1548 := by
  calc
    a ^ 16 = a * a ^ 15 := by ring
    _ = 3417 * a ^ 2 + 5644 * a + 1548 := by
      rw [a_pow_fifteen]
      ring_nf
      rw [a_cubic]
      ring

private theorem a_pow_seventeen :
    a ^ 17 = 5644 * a ^ 2 + 11799 * a + 3417 := by
  calc
    a ^ 17 = a * a ^ 16 := by ring
    _ = 5644 * a ^ 2 + 11799 * a + 3417 := by
      rw [a_pow_sixteen]
      ring_nf
      rw [a_cubic]
      ring

private theorem a_pow_eighteen :
    a ^ 18 = 11799 * a ^ 2 + 20349 * a + 5644 := by
  calc
    a ^ 18 = a * a ^ 17 := by ring
    _ = 11799 * a ^ 2 + 20349 * a + 5644 := by
      rw [a_pow_seventeen]
      ring_nf
      rw [a_cubic]
      ring

def scale : L := a ^ 2 - a - 3
def changeR : L := 3 + a - a ^ 2
def changeS : L := 2 - a ^ 2
def changeT : L := -8 - 2 * a + 2 * a ^ 2

local macro "n18_ring" : tactic =>
  `(tactic|
    (ring_nf
     simp only [a_pow_eighteen, a_pow_seventeen, a_pow_sixteen, a_pow_fifteen,
       a_pow_fourteen, a_pow_thirteen, a_pow_twelve, a_pow_eleven,
       a_pow_ten, a_pow_nine, a_pow_eight, a_pow_seven, a_pow_six,
       a_pow_five, a_pow_four, a_cubic]
     ring))

theorem scale_mul_mu : scale * mu = 1 := by
  unfold scale mu
  field_simp
  n18_ring

theorem scale_ne_zero : scale ≠ 0 := by
  intro h
  have hmul := scale_mul_mu
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

@[simp] theorem scale_inv : scale⁻¹ = mu := by
  calc
    scale⁻¹ = scale⁻¹ * 1 := (mul_one _).symm
    _ = scale⁻¹ * (scale * mu) := by rw [scale_mul_mu]
    _ = mu := by rw [← mul_assoc, inv_mul_cancel₀ scale_ne_zero, one_mul]

def scaleUnit : Lˣ := Units.mk0 scale scale_ne_zero

/-- The admissible substitution
`(X,Y) ↦ (u²X+r,u³Y+u²sX+t)` carrying the good equation back to
the original equation. -/
def toGoodChange : WeierstrassCurve.VariableChange L where
  u := scaleUnit
  r := changeR
  s := changeS
  t := changeT

/-- The model stored in `N18RouteC_Split` is exactly the transform of `E0`.
This is the missing finite coefficient certificate behind the local model. -/
theorem toGoodChange_smul_E0 : toGoodChange • E0 = E0Good := by
  ext <;>
    simp only [toGoodChange, scaleUnit, changeR, changeS, changeT,
      E0, E0Good, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val,
      Units.val_mk0, scale_inv]
  all_goals unfold mu
  all_goals field_simp [scale_ne_zero]
  all_goals n18_ring

abbrev E0GoodPoint := WeierstrassCurve.Affine.Point E0Good

private noncomputable def curveEqAddEquiv
    {W W' : WeierstrassCurve L} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+
      WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private theorem curveEqAddEquiv_some
    {W W' : WeierstrassCurve L} (h : W = W') {x y : L}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    curveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst W'
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-- Point-level transport from the original quotient to its good model. -/
noncomputable def e0GoodEquiv : Isogeny.E0Point ≃+ E0GoodPoint :=
  (VariableChangePoints.variableChangePointAddEquiv E0 toGoodChange).trans
    (curveEqAddEquiv toGoodChange_smul_E0)

theorem e0GoodEquiv_some
    {x y : L} {h0 : WeierstrassCurve.Affine.Nonsingular E0 x y}
    {hG : WeierstrassCurve.Affine.Nonsingular E0Good
      (VariableChangePoints.variableChangePointX toGoodChange x)
      (VariableChangePoints.variableChangePointY toGoodChange x y)} :
    e0GoodEquiv (WeierstrassCurve.Affine.Point.some x y h0) =
      WeierstrassCurve.Affine.Point.some
        (VariableChangePoints.variableChangePointX toGoodChange x)
        (VariableChangePoints.variableChangePointY toGoodChange x y) hG := by
  change (curveEqAddEquiv toGoodChange_smul_E0)
      (VariableChangePoints.variableChangePointMap E0 toGoodChange
        (WeierstrassCurve.Affine.Point.some x y h0)) = _
  change (curveEqAddEquiv toGoodChange_smul_E0)
      (WeierstrassCurve.Affine.Point.some
        (VariableChangePoints.variableChangePointX toGoodChange x)
        (VariableChangePoints.variableChangePointY toGoodChange x y) _) = _
  exact curveEqAddEquiv_some toGoodChange_smul_E0

/-- The scale is one uniformizer times an element reducing to `1`. -/
theorem scale_eq_pi_mul_unit : scale = pi * changeS := by
  unfold scale changeS a
  ring_nf
  rw [pi_cubed]
  ring

end

end MazurProof.N18RouteC.GoodModel
