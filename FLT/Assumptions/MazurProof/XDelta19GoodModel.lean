import FLT.Assumptions.MazurProof.XDelta19Model

/-!
# A good integral model in the conductor-nineteen isogeny class

The scaled quotient used in `XDelta19Model` becomes the smaller integral
model

`Y² = X³ + (8X+76)²`

after the change of variables

`s = 9X + 228`, `t = 27Y`.

This model has good reduction at three.  Its visible rational flexes are
the two points `(0, ±76)`, which is the normalization needed for the
complementary three-isogeny descent.
-/

namespace MazurProof.XDelta19GoodModel

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.XDelta19Model

noncomputable section

/-! ## The good integral equation -/

/-- The integral model in the middle of the conductor-nineteen
three-isogeny chain. -/
def goodCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 64
  a₃ := 0
  a₄ := 1216
  a₆ := 5776

/-- The affine equation of the good integral model. -/
def OnGood (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2

/-- The good model has discriminant `-2^12 * 19^3`, hence in particular
good reduction at three. -/
theorem goodCurve_delta : goodCurve.Δ = (-28094464 : ℚ) := by
  norm_num [goodCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The good integral model is nonsingular. -/
instance goodCurve_isElliptic : goodCurve.IsElliptic where
  isUnit := by
    rw [goodCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed good equation. -/
@[simp] theorem goodCurve_equation_iff (x y : ℚ) :
    Equation goodCurve x y ↔ OnGood x y := by
  rw [equation_iff]
  simp [goodCurve, OnGood]
  ring_nf

/-! ## Change of variables to the scaled quotient -/

/-- The integral change of variables carries the good model to the
scaled quotient from `XDelta19Model`. -/
theorem good_to_dual {x y : ℚ} (h : OnGood x y) :
    OnDual (9 * x + 228) (27 * y) := by
  unfold OnGood at h
  unfold OnDual
  linear_combination 729 * h

/-- The inverse rational change of variables carries the scaled quotient
back to the good model. -/
theorem dual_to_good {s t : ℚ} (h : OnDual s t) :
    OnGood ((s - 228) / 9) (t / 27) := by
  unfold OnDual at h
  unfold OnGood
  linear_combination h / 729

/-- Rational points on the good integral model. -/
abbrev GoodPoint := Point goodCurve

/-- The bundled change of variables from the good model to the scaled
quotient. -/
noncomputable def goodToDualPoint : GoodPoint → DualPoint
  | .zero => .zero
  | .some _x _y h =>
      Point.mk
        (dualCurve_equation_iff _ _ |>.2 <|
          good_to_dual (goodCurve_equation_iff _ _ |>.1 h.1))

/-- The bundled inverse change of variables from the scaled quotient to
the good model. -/
noncomputable def dualToGoodPoint : DualPoint → GoodPoint
  | .zero => .zero
  | .some _s _t h =>
      Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dual_to_good (dualCurve_equation_iff _ _ |>.1 h.1))

/-- The forward change of variables fixes the point at infinity. -/
@[simp] theorem goodToDualPoint_zero :
    goodToDualPoint 0 = 0 := rfl

/-- The inverse change of variables fixes the point at infinity. -/
@[simp] theorem dualToGoodPoint_zero :
    dualToGoodPoint 0 = 0 := rfl

/-- The forward bundled map has the displayed affine coordinates. -/
theorem goodToDualPoint_some {x y : ℚ}
    (h : Nonsingular goodCurve x y) :
    goodToDualPoint (.some x y h) =
      Point.mk
        (dualCurve_equation_iff _ _ |>.2 <|
          good_to_dual (goodCurve_equation_iff _ _ |>.1 h.1)) := rfl

/-- The inverse bundled map has the displayed affine coordinates. -/
theorem dualToGoodPoint_some {s t : ℚ}
    (h : Nonsingular dualCurve s t) :
    dualToGoodPoint (.some s t h) =
      Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dual_to_good (dualCurve_equation_iff _ _ |>.1 h.1)) := rfl

/-- The two bundled coordinate changes are inverse on good-model
rational points. -/
@[simp] theorem dualToGood_goodToDual (P : GoodPoint) :
    dualToGoodPoint (goodToDualPoint P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
      unfold goodToDualPoint dualToGoodPoint Point.mk
      change Point.some ((9 * x + 228 - 228) / 9)
          ((27 * y) / 27) _ = Point.some x y h
      rw [Point.some.injEq]
      constructor <;> ring

/-- The two bundled coordinate changes are inverse on scaled-quotient
rational points. -/
@[simp] theorem goodToDual_dualToGood (P : DualPoint) :
    goodToDualPoint (dualToGoodPoint P) = P := by
  cases P with
  | zero => rfl
  | some s t h =>
      unfold dualToGoodPoint goodToDualPoint Point.mk
      change Point.some (9 * ((s - 228) / 9) + 228)
          (27 * (t / 27)) _ = Point.some s t h
      rw [Point.some.injEq]
      constructor <;> ring

/-! ## Visible rational flexes -/

/-- Nonsingularity of the positive visible flex. -/
theorem goodT_nonsingular : Nonsingular goodCurve (0 : ℚ) 76 :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 76).mpr (by norm_num [OnGood])

/-- Nonsingularity of the negative visible flex. -/
theorem goodTNeg_nonsingular : Nonsingular goodCurve (0 : ℚ) (-76) :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 (-76)).mpr (by norm_num [OnGood])

/-- The positive rational flex on the good model. -/
def goodT : GoodPoint :=
  Point.some 0 76 goodT_nonsingular

/-- The negative rational flex on the good model. -/
def goodTNeg : GoodPoint :=
  Point.some 0 (-76) goodTNeg_nonsingular

/-- The positive flex is carried to the positive distinguished point on
the scaled quotient. -/
theorem goodToDualPoint_goodT :
    goodToDualPoint goodT =
      Point.some 228 2052
        (equation_iff_nonsingular.mp <|
          (dualCurve_equation_iff 228 2052).mpr (by norm_num [OnDual])) := by
  rw [goodT, goodToDualPoint_some]
  change Point.some (9 * 0 + 228) (27 * 76) _ =
    Point.some 228 2052 _
  rw [Point.some.injEq]
  norm_num

/-- The negative flex is carried to the negative distinguished point on
the scaled quotient. -/
theorem goodToDualPoint_goodTNeg :
    goodToDualPoint goodTNeg =
      Point.some 228 (-2052)
        (equation_iff_nonsingular.mp <|
          (dualCurve_equation_iff 228 (-2052)).mpr
            (by norm_num [OnDual])) := by
  rw [goodTNeg, goodToDualPoint_some]
  change Point.some (9 * 0 + 228) (27 * (-76)) _ =
    Point.some 228 (-2052) _
  rw [Point.some.injEq]
  norm_num

end

end MazurProof.XDelta19GoodModel
