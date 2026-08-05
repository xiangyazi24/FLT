import FLT.Assumptions.MazurProof.XDelta19GoodFormalReduction

/-!
# Rational points on the good conductor-nineteen model

The two explicit three-isogeny descents give a three-coset cover of the
rational points on

`y² = x³ + (8x+76)²`.

The three-adic formal filtration then kills six times every rational point.
This curve has no rational two-torsion, so every rational point is already
killed by three.  Finally, the verified dual-forward isogeny composition
shows that an affine three-torsion point must lie in the visible kernel
`x=0`.
-/

namespace MazurProof.XDelta19GoodRationalPoints

open WeierstrassCurve.Affine
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodFormalReduction

noncomputable section

/-! ## Elimination of rational two-torsion -/

/-- The good model has no nonzero rational point killed by two.  An affine
two-torsion point would equal its inverse, forcing its vertical coordinate
to vanish, while the good cubic has no rational root. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : GoodPoint) (hP : 2 • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
      exfalso
      rw [two_nsmul] at hP
      have hself :
          (Point.some x y h : GoodPoint) = -Point.some x y h :=
        eq_neg_of_add_eq_zero_left hP
      rw [Point.neg_some, Point.some.injEq] at hself
      have hy : y = 0 := by
        have := hself.2
        simp only [WeierstrassCurve.Affine.negY, goodCurve] at this
        linarith
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      exact good_y_ne_zero hcurve hy

/-! ## Exponent three and the visible kernel -/

/-- Weak three-descent, formal entry after multiplication by six, and the
absence of rational two-torsion force every rational point to be killed by
three. -/
theorem three_nsmul_eq_zero (P : GoodPoint) :
    3 • P = 0 := by
  apply eq_zero_of_two_nsmul_eq_zero (3 • P)
  calc
    2 • (3 • P) = 6 • P := by
      exact (mul_nsmul' P 2 3).symm
    _ = 0 := six_nsmul_eq_zero six_nsmul_formal P

/-- An affine rational point killed by three belongs to the visible kernel
of the forward three-isogeny, hence has first coordinate zero.  Otherwise
both isogeny maps are affine at the point, contradicting that their
composition is the point at infinity. -/
theorem x_eq_zero_of_three_nsmul
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hthree : 3 • (Point.some x y h : GoodPoint) = 0) :
    x = 0 := by
  by_contra hx
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hforward := threeIsogenyPoint_some_of_x_ne_zero h hx
  have hforwardX := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (Point.some x y h : GoodPoint)
  rw [hthree] at hcomp
  rw [hforward] at hcomp
  change dualThreeIsogenyPoint
      (Point.some (threeIsogenyX x) (threeIsogenyY x y) _) = 0 at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hforwardX] at hcomp
  exact (Point.some_ne_zero _) hcomp

/-- Every affine rational point on the good integral model has first
coordinate zero. -/
theorem affine_x_eq_zero {x y : ℚ} (h : OnGood x y) :
    x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((goodCurve_equation_iff x y).mpr h)
  exact x_eq_zero_of_three_nsmul hns
    (three_nsmul_eq_zero (Point.some x y hns : GoodPoint))

end

end MazurProof.XDelta19GoodRationalPoints
