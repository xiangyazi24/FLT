import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius

/-!
# Canonical chart of a normalized projective point

The normalized representative records its first nonzero homogeneous
coordinate in its constructor.  This pivot is preserved by coordinatewise
base change and therefore by arithmetic Frobenius.  It supplies a canonical
chart choice for descending finite-field points to closed Frobenius orbits.
-/

namespace MazurProof.RationalPointsN25QuotientTwoClosedPointChart

open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBaseChange
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius

/-- The first nonzero homogeneous coordinate of a normalized projective
representative. -/
def normalizedPivot {K : Type*} : NormalizedProjective4 K → Fin 4
  | .xChart _ _ _ => 0
  | .yChart _ _ => 1
  | .zChart _ => 2
  | .wChart => 3

/-- Coordinatewise base change preserves the normalized chart constructor. -/
@[simp]
theorem normalizedPivot_map
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (P : NormalizedProjective4 K) :
    normalizedPivot (NormalizedProjective4.map f P) =
      normalizedPivot P := by
  cases P <;> rfl

/-- Arithmetic Frobenius preserves the canonical normalized chart. -/
@[simp]
theorem normalizedPivot_pointFrobenius
    (C : CurveModel) (p d : ℕ) [Fact (Nat.Prime p)]
    (P : CurvePoint C (CommonField p d)) :
    normalizedPivot ((pointFrobenius C p d P).1) =
      normalizedPivot P.1 := by
  simpa only [pointFrobenius_apply_val] using
    (normalizedPivot_map
      (commonFrobenius p d).toRingEquiv.toRingHom P.1)

/-- Every Frobenius iterate preserves the canonical normalized chart. -/
theorem normalizedPivot_pointFrobeniusFun_iterate
    (C : CurveModel) (p d n : ℕ) [Fact (Nat.Prime p)]
    (P : CurvePoint C (CommonField p d)) :
    normalizedPivot
        ((((pointFrobeniusFun C p d :
          CurvePoint C (CommonField p d) →
            CurvePoint C (CommonField p d))^[n]) P).1) =
      normalizedPivot P.1 := by
  rw [pointFrobenius_iterate_val]
  exact normalizedPivot_map _ _

end MazurProof.RationalPointsN25QuotientTwoClosedPointChart
