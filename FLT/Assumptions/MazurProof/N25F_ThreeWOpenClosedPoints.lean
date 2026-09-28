import FLT.Assumptions.MazurProof.N25F_ThreeWOpenPrimeEquiv
import FLT.Assumptions.MazurProof.N25F_ThreeBoundaryPointClassification
import FLT.Assumptions.MazurProof.N25F_ThreeWOpenNonempty
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThreeProjective
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF2
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientThreeBaseChange
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBaseChange
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius
import Mathlib.RingTheory.Jacobson.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeWOpenClosedPoints

open N25F_ThreeWChartDRegular
open N25F_ThreeWOpenPrimeEquiv
open N25F_ThreeBoundaryPointClassification
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientThreeBaseChange
open RationalPointsN25QuotientBaseChange
open NormalizedProjectiveCurveFrobenius

/-! ## The homogeneous form of the affine denominator -/

/-- The degree-two homogeneous form whose restriction to W = 1 is
wChartDenominatorThree = x*z - x + z. -/
def projectiveWChartDenominatorThree
    {K : Type*} [CommRing K] (P : Coordinates4 K) : K :=
  P.x * P.z - P.x * P.w + P.z * P.w

@[simp]
theorem projectiveWChartDenominatorThree_scale
    {K : Type*} [CommRing K] (a : K) (P : Coordinates4 K) :
    projectiveWChartDenominatorThree (scaleCoordinatesThree a P) =
      a ^ 2 * projectiveWChartDenominatorThree P := by
  rcases P with ⟨x, y, z, w⟩
  simp only [projectiveWChartDenominatorThree, scaleCoordinatesThree]
  ring

@[simp]
theorem projectiveWChartDenominatorThree_map
    {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : Coordinates4 K) :
    projectiveWChartDenominatorThree (Coordinates4.map f P) =
      f (projectiveWChartDenominatorThree P) := by
  rcases P with ⟨x, y, z, w⟩
  simp [projectiveWChartDenominatorThree, Coordinates4.map]

/-! ## On a canonical curve point, vanishing of W forces vanishing of D. -/
theorem projectiveWChartDenominatorThree_eq_zero_of_w_eq_zero
    {K : Type} [Field K]
    (P : CurvePoint canonicalThreeModel K)
    (hw : (normalizedCoordinatesThree P.1).w = 0) :
    projectiveWChartDenominatorThree
        (normalizedCoordinatesThree P.1) = 0 := by
  have hcurve : IsCanonicalNormalizedThree P.1 := P.2
  rcases boundary_point_eq_three_cases P.1 hcurve hw with h | h | h
  · rw [h]
    simp [projectiveWChartDenominatorThree, normalizedCoordinatesThree]
  · rw [h]
    simp [projectiveWChartDenominatorThree, normalizedCoordinatesThree]
  · rw [h]
    simp [projectiveWChartDenominatorThree, normalizedCoordinatesThree]

/-- D nonzero implies that the point lies on the projective W-open. -/
theorem w_ne_zero_of_projectiveWChartDenominatorThree_ne_zero
    {K : Type} [Field K]
    (P : CurvePoint canonicalThreeModel K)
    (hD : projectiveWChartDenominatorThree
        (normalizedCoordinatesThree P.1) ≠ 0) :
    (normalizedCoordinatesThree P.1).w ≠ 0 := by
  intro hw
  exact hD (projectiveWChartDenominatorThree_eq_zero_of_w_eq_zero P hw)

end MazurProof.N25F_ThreeWOpenClosedPoints
