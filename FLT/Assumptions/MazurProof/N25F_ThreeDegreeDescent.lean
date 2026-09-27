import FLT.Assumptions.MazurProof.N25F_Next
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientFrobeniusOrbits

/-!
# Degreewise descent to the common degree-twelve field

The coherent finite-field realization embeds the actual degree-`d + 1`
coefficient field into the common field of degree twelve. This module exposes
the induced equivalence with the Frobenius fixed-point subtype.
-/

noncomputable section

namespace MazurProof.N25F_ThreeFullClosedPoints

open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientThreeBaseChange

/-- Cardinality of a positive-degree characteristic-three common field. -/
theorem commonFieldThree_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CommonField 3 d) = 3 ^ d := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 3 d hd.ne'

/-- Realize the shifted source field inside the common degree-twelve field. -/
noncomputable def degreeRealizationThree
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    Realization 3 12 (d + 1) (CommonField 3 (d + 1)) :=
  RationalPointsN25QuotientFrobeniusOrbits.fieldRealization
    (CommonField 3 (d + 1)) (d + 1) (Nat.succ_pos d) hd12
    (commonFieldThree_card (d + 1) (Nat.succ_pos d))

/-- The source curve points are equivalent to the common-field points fixed
by the `(d + 1)`-fold arithmetic Frobenius iterate. -/
noncomputable def degreeToCommonFixedEquiv
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    DegreeCurvePointThree d ≃
      NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalThreeModel 3 12 (d + 1) :=
  NormalizedProjectiveCurveFrobenius.curvePointEquivFixedByIterate
    canonicalThreeModel 3 12 (d + 1)
    (CommonField 3 (d + 1)) (degreeRealizationThree d hd12)

/-- The fixed-point equivalence uses the stored field embedding. -/
@[simp]
theorem degreeToCommonFixedEquiv_val
    (d : ℕ) (hd12 : d + 1 ∣ 12)
    (P : DegreeCurvePointThree d) :
    (degreeToCommonFixedEquiv d hd12 P).1 =
      NormalizedProjectiveCurveFrobenius.curvePointEmbedding
        canonicalThreeModel (degreeRealizationThree d hd12).embedding P := by
  apply Subtype.ext
  rfl

/-- The descended point is fixed by the common Frobenius iterate. -/
theorem degreeToCommonFixedEquiv_periodic
    (d : ℕ) (hd12 : d + 1 ∣ 12)
    (P : DegreeCurvePointThree d) :
    (((RationalPointsN25QuotientFrobeniusOrbits.commonPointFrobenius :
        _ → _)^[d + 1]) (degreeToCommonFixedEquiv d hd12 P).1) =
      (degreeToCommonFixedEquiv d hd12 P).1 := by
  exact (degreeToCommonFixedEquiv d hd12 P).2

end MazurProof.N25F_ThreeFullClosedPoints

