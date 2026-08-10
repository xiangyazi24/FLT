import FLT.Assumptions.MazurProof.CurveZetaMarkedDivisors

/-!
# Extension points as closed-point Frobenius slots

The marked-divisor recurrence uses the intrinsic ghost type
`ExactGhostSlot C k`: a closed point whose degree divides `k`, the uniquely
determined positive quotient, and one of the closed point's Frobenius
positions.  Geometry enters only by classifying actual points over selected
extension fields by these slots.

This module isolates that classification as a family of equivalences.  It
does not assume point-count equations, effective-divisor counts, or an Euler
recurrence; all of those are cardinality consequences.
-/

namespace MazurProof.CurveZetaPointOrbitClassification

open CurveZetaEffectiveDivisors
open CurveZetaMarkedDivisors

/-- A selected family of extension-field point types is classified by
closed points and their Frobenius positions.  Choosing the position numbering
is harmless because downstream arguments use only finite cardinalities. -/
structure PointOrbitClassificationOn
    (C : ClosedPointGrading)
    (Index : Type*)
    (exponent : Index → ℕ)
    (pointType : Index → Type*) where
  /-- A point over the selected degree-`k` extension is uniquely an intrinsic
  closed-point ghost slot of contribution `k`. -/
  classify : ∀ i, pointType i ≃
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot C (exponent i)

namespace PointOrbitClassificationOn

variable {C : ClosedPointGrading}
variable {Index : Type*} {exponent : Index → ℕ}
variable {pointType : Index → Type*}

/-- Orbit classification identifies the cardinality of a semantic extension
point type with the corresponding intrinsic ghost coefficient. -/
theorem pointNatCard_eq_ghostCount
    (B : PointOrbitClassificationOn C Index exponent pointType)
    (i : Index) :
    Nat.card (pointType i) =
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C (exponent i) := by
  exact Nat.card_congr (B.classify i)

end PointOrbitClassificationOn

end MazurProof.CurveZetaPointOrbitClassification
