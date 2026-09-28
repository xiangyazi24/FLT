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

/-! ## The projective W-open and its W = 1 representatives -/

/-- A canonical curve point whose W-coordinate is nonzero. -/
structure CurvePointOnWOpenThree (K : Type) [Field K] where
  point : CurvePoint canonicalThreeModel K
  w_ne_zero : (normalizedCoordinatesThree point.1).w ≠ 0

@[ext]
theorem CurvePointOnWOpenThree.ext
    {K : Type} [Field K]
    (P Q : CurvePointOnWOpenThree K)
    (h : P.point = Q.point) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Rescale a normalized projective representative by the inverse of W.
The intended uses separately establish that W is nonzero. -/
def normalizeAtWThree
    {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Coordinates4 K :=
  scaleCoordinatesThree ((normalizedCoordinatesThree P).w)⁻¹
    (normalizedCoordinatesThree P)

/-- The W = 1 homogeneous representative of a W-open curve point. -/
def wOpenCoordinatesThree
    {K : Type} [Field K]
    (P : CurvePointOnWOpenThree K) : Coordinates4 K :=
  normalizeAtWThree P.point.1

@[simp]
theorem wOpenCoordinatesThree_w
    {K : Type} [Field K]
    (P : CurvePointOnWOpenThree K) :
    (wOpenCoordinatesThree P).w = 1 := by
  change ((normalizedCoordinatesThree P.point.1).w)⁻¹ *
      (normalizedCoordinatesThree P.point.1).w = 1
  exact inv_mul_cancel₀ P.w_ne_zero

/-- First-nonzero normalization recovers the original projective point. -/
theorem normalizeCoordinatesThree_wOpenCoordinatesThree
    {K : Type} [Field K] [DecidableEq K]
    (P : CurvePointOnWOpenThree K) :
    normalizeCoordinatesThree (wOpenCoordinatesThree P) =
      P.point.1 := by
  exact normalize_scale_normalized P.point.1
    (inv_ne_zero P.w_ne_zero)

/-- Equality of W = 1 representatives determines the W-open curve point. -/
theorem CurvePointOnWOpenThree.eq_of_wOpenCoordinates_eq
    {K : Type} [Field K]
    {P Q : CurvePointOnWOpenThree K}
    (h : wOpenCoordinatesThree P = wOpenCoordinatesThree Q) :
    P = Q := by
  classical
  apply CurvePointOnWOpenThree.ext
  apply Subtype.ext
  have h' := congrArg (normalizeCoordinatesThree (K := K)) h
  simpa only [normalizeCoordinatesThree_wOpenCoordinatesThree] using h'

/-! ## Normalizing an arbitrary affine W-chart representative -/

/-- Homogenize the affine coordinates with W = 1. -/
def wOpenChartPointThree
    {K : Type*} [Field K]
    (v : Fin 3 → K) : Coordinates4 K :=
  ⟨v 0, v 1, v 2, 1⟩

theorem wOpenChartPointThree_ne_zero
    {K : Type*} [Field K]
    (v : Fin 3 → K) :
    wOpenChartPointThree v ≠ zeroCoordinatesThree := by
  intro h
  have hw : (1 : K) = 0 := by
    simpa only [wOpenChartPointThree, zeroCoordinatesThree] using
      congrArg (fun P : Coordinates4 K => P.w) h
  exact one_ne_zero hw

/-- First-nonzero normalization of an affine W-chart representative.
This definition does not assert the canonical curve equations. -/
def normalizedWOpenPointThree
    {K : Type*} [Field K]
    (v : Fin 3 → K) : NormalizedProjective4 K := by
  classical
  exact normalizeCoordinatesThree (wOpenChartPointThree v)

/-- The normalized representative is a nonzero scalar multiple of
its original W = 1 representative. -/
theorem normalizedWOpenPointThree_spec
    {K : Type*} [Field K]
    (v : Fin 3 → K) :
    ∃ a : K, a ≠ 0 ∧
      normalizedCoordinatesThree (normalizedWOpenPointThree v) =
        scaleCoordinatesThree a (wOpenChartPointThree v) := by
  classical
  simpa only [normalizedWOpenPointThree] using
    (normalizeCoordinatesThree_spec (wOpenChartPointThree_ne_zero v))

/-- First-nonzero normalization cannot kill the W-coordinate. -/
theorem normalizedWOpenPointThree_w_ne_zero
    {K : Type*} [Field K]
    (v : Fin 3 → K) :
    (normalizedCoordinatesThree (normalizedWOpenPointThree v)).w ≠ 0 := by
  rcases normalizedWOpenPointThree_spec v with ⟨a, ha, hspec⟩
  rw [hspec]
  simpa only [scaleCoordinatesThree, wOpenChartPointThree, mul_one] using ha

/-- Renormalizing at W recovers the original affine representative. -/
theorem normalizeAtWThree_normalizedWOpenPointThree
    {K : Type*} [Field K]
    (v : Fin 3 → K) :
    normalizeAtWThree (normalizedWOpenPointThree v) =
      wOpenChartPointThree v := by
  rcases normalizedWOpenPointThree_spec v with ⟨a, ha, hspec⟩
  unfold normalizeAtWThree
  rw [hspec]
  simp only [scaleCoordinatesThree, wOpenChartPointThree, mul_one,
    ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end MazurProof.N25F_ThreeWOpenClosedPoints
