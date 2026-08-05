import FLT.Assumptions.MazurProof.TateOrder19Quotient
import FLT.Assumptions.MazurProof.XDelta19Descent
import FLT.Assumptions.MazurProof.XDelta19GoodRationalPoints

/-!
# Rational points on the order-nineteen diamond quotient

The good-model classification is transported first to the scaled
three-isogenous curve, then through the surjective dual isogeny to

`Y² = X³ + (2X+4)²`,

and finally to the minimal diamond quotient

`v² + v = u³ + u² + u`.

The resulting statement supplies the arithmetic input of the explicit
Tate-to-diamond quotient and excludes the order-nineteen Tate residual.
-/

namespace MazurProof.XDelta19RationalPoints

open WeierstrassCurve.Affine
open MazurProof.N19SutherlandModels
open MazurProof.XDelta19Model
open MazurProof.XDelta19Descent
open MazurProof.XDelta19GoodModel

noncomputable section

/-! ## Transport from the good model to the short model -/

/-- Every affine rational point on the original short model has first
coordinate zero.  Surjectivity of the first dual isogeny gives a point on
the scaled quotient; the good-model classification forces that point to
have scaled coordinate `s=228`, whose dual image has `x=0`. -/
theorem short_affine_x_eq_zero {x y : ℚ} (h : OnShort x y) :
    x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular shortCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((shortCurve_equation_iff x y).mpr h)
  obtain ⟨Q, hQ⟩ :=
    dualThreeIsogenyPoint_surjective
      (Point.some x y hns : ShortPoint)
  cases Q with
  | zero =>
      have hzero :
          dualThreeIsogenyPoint (0 : DualPoint) = (0 : ShortPoint) :=
        dualThreeIsogenyPoint_zero
      have hQzero :
          (0 : ShortPoint) = Point.some x y hns := by
        exact hzero.symm.trans hQ
      exact False.elim ((Point.some_ne_zero hns) hQzero.symm)
  | some s t hs =>
      have hdual : OnDual s t := (dualCurve_equation_iff s t).mp hs.1
      have hs0 : s ≠ 0 := dual_x_ne_zero_of_on_curve hdual
      have hgood : OnGood ((s - 228) / 9) (t / 27) :=
        dual_to_good hdual
      have hgoodx : (s - 228) / 9 = 0 :=
        XDelta19GoodRationalPoints.affine_x_eq_zero hgood
      have hs228 : s = 228 := by linarith
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero hs hs0] at hQ
      unfold Point.mk at hQ
      rw [Point.some.injEq] at hQ
      have hxmap := hQ.1
      rw [hs228] at hxmap
      norm_num [dualThreeIsogenyX] at hxmap
      linarith

/-! ## Minimal quotient and Tate residual -/

/-- Every affine rational point on the minimal diamond quotient has
horizontal coordinate zero. -/
theorem minimal_affine_x_eq_zero {u v : ℚ} (h : OnMinimal u v) :
    u = 0 :=
  minimal_x_eq_zero_of_short_x_eq_zero
    (fun _x _y hshort => short_affine_x_eq_zero hshort) h

/-- A zero of the diamond residual has horizontal coordinate zero. -/
theorem diamond_x_eq_zero
    (u v : ℚ) (h : diamondResidual u v = 0) :
    u = 0 := by
  apply minimal_affine_x_eq_zero
  unfold diamondResidual at h
  unfold OnMinimal
  nlinarith [h]

/-- The order-nineteen Tate division factor has no rational zero away from
the excluded boundary `b=0`. -/
theorem no_F19_rational_solution
    (b c : ℚ) (hb : b ≠ 0) :
    TateNFDivision.F19 b c ≠ 0 :=
  TateOrder19Quotient.no_F19_rational_solution_of_diamond_x_eq_zero
    diamond_x_eq_zero b c hb

end

end MazurProof.XDelta19RationalPoints
