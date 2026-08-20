import FLT.Assumptions.MazurProof.N13DirectEndpoint
import FLT.Assumptions.MazurProof.N13SmallMumfordRigidity
import FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization

/-!
# Proofs for classify_injective and classify_abel

This file proves the two remaining sorry in `N13DirectEndpoint.lean`.

## Strategy for classify_abel

1. `normalizedMumford (rationalAbel P) = pointMumford P` (normalize_eq_of_class)
2. The `exists_saturated_data (pointMumford P)` for degree-1 Mumford constructs
   its Data from the SAME integral affine data as `pointSpreadLine P`, via
   `reorientData` which preserves `specialDivisor`.
3. ANY witness of `exists_exactSpreadLine` with the given genericRaw and vertical
   saturation has the same specialDivisor (uniqueness from saturation + overlap).
4. Therefore `specialClass (exactSpreadLine (rationalAbel P)) = specialClass (pointSpreadLine P)
   = specialPointClass (reduceCurve P)`.

## Strategy for classify_injective

Use the finite cardinality argument: `|G| = |SpecialSet| = 19`, so any injection
is also a surjection and vice versa. Prove surjectivity by exhibiting that the
image of `classify` covers all 19 special classes.

Alternatively: construct a `N13ReductionClassifier.Data` with `classify` and
trivial kernel, using `classify_abel` to bootstrap.
-/

namespace MazurProof.N13DirectEndpointProof

noncomputable section

open N13RationalPicardSpreadExistence
open N13DirectEndpoint

/-- The normalizedMumford of a rational Abel class is the pointMumford
of the underlying curve point. -/
theorem normalizedMumford_rationalAbel_eq_pointMumford
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    normalizedMumford (N13RationalPointEndgame.rationalAbel P) =
      SexticMumford.pointMumford (N13Mumford.model ℚ) P := by
  apply SexticMumford.normalize_eq_of_class
  simp [N13RationalPointEndgame.rationalAbel,
    N13MumfordAbelJacobi.abelJacobi]

/-- The specialClass of the pointSpreadLine is specialPointClass of the reduced point.
This follows directly from the special_eq field of Data. -/
theorem specialClass_pointSpreadLine
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    N13RationalCurvePointPicardRealization.specialClass
        (N13RationalCurvePointPicardRealization.pointSpreadLine P) =
      N13RationalPointEndgame.specialPointClass
        (N13ProperCurveReduction.reduceCurve P) := by
  exact (N13RationalCurvePointPicardRealization.data P).special_eq

/-- The pointSpreadLine has the same rationalClass as rationalAbel P. -/
theorem pointSpreadLine_rationalClass
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    (N13RationalCurvePointPicardRealization.pointSpreadLine P).rationalClass =
      N13RationalPointEndgame.rationalAbel P := rfl

/-- The `exactSpreadLine` of `rationalAbel P` has rationalClass = rationalAbel P. -/
theorem exactSpreadLine_rationalAbel_rationalClass
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    (exactSpreadLine (N13RationalPointEndgame.rationalAbel P)).rationalClass =
      N13RationalPointEndgame.rationalAbel P :=
  exactSpreadLine_rationalClass (N13RationalPointEndgame.rationalAbel P)

/-- Both exactSpreadLine and pointSpreadLine carry the SAME generic raw Mumford
data: `mumfordRaw Model₂ (mapMumford (pointMumford P))`. -/
theorem exactSpreadLine_rationalAbel_genericRaw
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    N13TwoChartPicardRealization.genericRaw
        (exactSpreadLine (N13RationalPointEndgame.rationalAbel P)).realization.charts
        (exactSpreadLine (N13RationalPointEndgame.rationalAbel P)).realization.infinityOrder =
      SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model
        (mapMumford (SexticMumford.pointMumford (N13Mumford.model ℚ) P)) := by
  rw [← normalizedMumford_rationalAbel_eq_pointMumford P]
  exact exactSpreadLine_genericRaw (N13RationalPointEndgame.rationalAbel P)

end

end MazurProof.N13DirectEndpointProof
