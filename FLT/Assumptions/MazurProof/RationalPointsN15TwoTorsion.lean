import FLT.Assumptions.MazurProof.RationalPointsN15ExactSequence
import FLT.Assumptions.MazurProof.RationalPointsN15Isogeny

/-!
# Rational two-torsion on the order-15 descent curve

The full two-descent curve

`y² = x(x+1)(x+16)`

has exactly four rational points killed by two: the point at infinity and
the three affine points with `y = 0`.  This supplies the two-torsion
cardinality input required by `freeRank_eq_zero_of_twoIsogeny`.
-/

namespace MazurProof.RationalPointsN15TwoTorsion

open RationalPointsN15Descent
open RationalPointsN15ExactSequence
open RationalPointsN15Isogeny
open WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

/-- The affine two-torsion point `(-1,0)`. -/
def fullRootNegOne : FullTwoPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((fullTwoCurve_equation_iff (-1) 0).mpr (by norm_num [FullTwoEquation]))

/-- The affine two-torsion point `(-16,0)`. -/
def fullRootNegSixteen : FullTwoPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((fullTwoCurve_equation_iff (-16) 0).mpr (by norm_num [FullTwoEquation]))

/-- On the full two-descent curve, an affine point is killed by two exactly
when its `y` coordinate vanishes. -/
theorem two_nsmul_some_eq_zero_iff_y_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : FullTwoPoint) = 0 ↔
      y = 0 := by
  constructor
  · intro htwo
    rw [two_nsmul] at htwo
    have hself :
        (WeierstrassCurve.Affine.Point.some x y h : FullTwoPoint) =
          -WeierstrassCurve.Affine.Point.some x y h :=
      eq_neg_of_add_eq_zero_left htwo
    rw [WeierstrassCurve.Affine.Point.neg_some] at hself
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hself
    have hy := hself.2
    simp only [WeierstrassCurve.Affine.negY, fullTwoCurve] at hy
    linarith
  · intro hy
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      (by simp [hy, fullTwoCurve, WeierstrassCurve.Affine.negY])

@[simp] theorem two_nsmul_fullRootNegOne : 2 • fullRootNegOne = 0 := by
  apply (two_nsmul_some_eq_zero_iff_y_eq_zero _).mpr
  rfl

@[simp] theorem two_nsmul_fullRootNegSixteen :
    2 • fullRootNegSixteen = 0 := by
  apply (two_nsmul_some_eq_zero_iff_y_eq_zero _).mpr
  rfl

/-- Complete pointwise enumeration of rational two-torsion. -/
theorem two_torsion_classification (P : FullTwoPoint) (hP : 2 • P = 0) :
    P = 0 ∨ P = fullKernel ∨ P = fullRootNegOne ∨
      P = fullRootNegSixteen := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
      have hy : y = 0 := (two_nsmul_some_eq_zero_iff_y_eq_zero h).mp hP
      have heq : FullTwoEquation x y :=
        (fullTwoCurve_equation_iff x y).mp h.1
      simp only [FullTwoEquation] at heq
      rw [hy] at heq
      have hxprod : x * (x + 1) * (x + 16) = 0 := by
        calc
          x * (x + 1) * (x + 16) = (0 : ℚ) ^ 2 := heq.symm
          _ = 0 := by norm_num
      rcases mul_eq_zero.mp hxprod with hx01 | hx16
      · rcases mul_eq_zero.mp hx01 with hx0 | hx1
        · right; left
          subst x
          subst y
          rfl
        · right; right; left
          have hx : x = -1 := by linarith
          subst x
          subst y
          rfl
      · right; right; right
        have hx : x = -16 := by linarith
        subst x
        subst y
        rfl

theorem fullRootNegOne_ne_zero : fullRootNegOne ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem fullRootNegSixteen_ne_zero : fullRootNegSixteen ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem fullKernel_ne_fullRootNegOne : fullKernel ≠ fullRootNegOne := by
  intro h
  have hx := (WeierstrassCurve.Affine.Point.some.inj h).1
  norm_num at hx

theorem fullKernel_ne_fullRootNegSixteen :
    fullKernel ≠ fullRootNegSixteen := by
  intro h
  have hx := (WeierstrassCurve.Affine.Point.some.inj h).1
  norm_num at hx

theorem fullRootNegOne_ne_fullRootNegSixteen :
    fullRootNegOne ≠ fullRootNegSixteen := by
  intro h
  have hx := (WeierstrassCurve.Affine.Point.some.inj h).1
  norm_num at hx

/-- The two-torsion set is exactly the four displayed points. -/
theorem two_torsion_set :
    {P : FullTwoPoint | 2 • P = 0} =
      {0, fullKernel, fullRootNegOne, fullRootNegSixteen} := by
  ext P
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact two_torsion_classification P
  · rintro (rfl | rfl | rfl | rfl) <;> simp

/-- The exact two-torsion cardinality needed by the abstract rank criterion. -/
theorem natCard_twoTorsion_fullTwoPoint :
    Nat.card (TwoTorsion FullTwoPoint) = 4 := by
  change ({P : FullTwoPoint | 2 • P = 0} : Set FullTwoPoint).ncard = 4
  rw [two_torsion_set]
  have hzero :
      (0 : FullTwoPoint) ∉
        ({fullKernel, fullRootNegOne, fullRootNegSixteen} :
          Set FullTwoPoint) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fullKernel_ne_zero.symm, fullRootNegOne_ne_zero.symm,
      fullRootNegSixteen_ne_zero.symm⟩
  have hkernel :
      fullKernel ∉ ({fullRootNegOne, fullRootNegSixteen} :
        Set FullTwoPoint) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fullKernel_ne_fullRootNegOne,
      fullKernel_ne_fullRootNegSixteen⟩
  have hnegOne :
      fullRootNegOne ∉ ({fullRootNegSixteen} : Set FullTwoPoint) := by
    simpa only [Set.mem_singleton_iff] using
      fullRootNegOne_ne_fullRootNegSixteen
  rw [Set.ncard_insert_of_notMem hzero,
    Set.ncard_insert_of_notMem hkernel,
    Set.ncard_insert_of_notMem hnegOne, Set.ncard_singleton]

end MazurProof.RationalPointsN15TwoTorsion
