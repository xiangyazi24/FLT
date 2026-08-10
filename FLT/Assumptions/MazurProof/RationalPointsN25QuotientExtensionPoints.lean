import FLT.Assumptions.MazurProof.CurveZetaPointOrbitClassification
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientZetaThree

/-!
# The first four characteristic-three extension point types

The genus-four middle Riemann--Roch calculation uses the canonical N25 curve
over `𝔽₃`, `𝔽₉`, `𝔽₂₇`, and `𝔽₈₁`.  This file gives those four
semantic point types a common finite index and records their already proved
cardinalities.  It deliberately contains no Frobenius action or Picard data:
the former is constructed from a common algebraic closure model, while the
latter belongs to the geometric Riemann--Roch layer.
-/

namespace MazurProof.RationalPointsN25QuotientMiddleRiemannRoch

open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientWeilThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic
open RationalPointsN25QuotientZetaThree

/-! ## Semantic extension-point counts -/

/-- The semantic N25 point-count sequence through degree four.  Values above
degree four are set to zero because the middle-degree consumer never reads
them; this convention is bookkeeping, not a geometric assertion. -/
noncomputable def extensionPointCount25Three : ℕ → ℕ
  | 1 => Nat.card {P : NormalizedProjective4 Trit // IsCanonicalNormalizedThree P}
  | 2 => Nat.card {P : NormalizedProjective4 F9 // IsCanonicalNormalizedThree P}
  | 3 => Nat.card {P : NormalizedProjective4 F27 // IsCanonicalNormalizedThree P}
  | 4 => Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P}
  | _ => 0

/-- The canonical curve has five points over the prime field. -/
theorem extensionPointCount25Three_one : extensionPointCount25Three 1 = 5 := by
  exact f3_canonical_normalized_three_card

/-- The quadratic extension introduces no new canonical curve point. -/
theorem extensionPointCount25Three_two : extensionPointCount25Three 2 = 5 := by
  exact f9_canonical_normalized_three_card

/-- The canonical curve has twenty points over the cubic extension. -/
theorem extensionPointCount25Three_three : extensionPointCount25Three 3 = 20 := by
  exact f27_canonical_normalized_three_card

/-- The canonical curve has eighty-nine points over the quartic extension. -/
theorem extensionPointCount25Three_four : extensionPointCount25Three 4 = 89 := by
  exact f81_canonical_normalized_three_card

/-! ## A common index for the four extension fields -/

/-- The extension degrees entering the genus-four class-number calculation. -/
inductive ExtensionIndex25Three
  | degreeOne
  | degreeTwo
  | degreeThree
  | degreeFour

namespace ExtensionIndex25Three

/-- The residue-field exponent represented by an extension index. -/
def exponent : ExtensionIndex25Three → ℕ
  | degreeOne => 1
  | degreeTwo => 2
  | degreeThree => 3
  | degreeFour => 4

/-- The normalized projective canonical-curve points over the selected
extension field.  These are semantic field-valued points, not executable
table predicates. -/
def pointType : ExtensionIndex25Three → Type
  | degreeOne =>
      {P : NormalizedProjective4 Trit // IsCanonicalNormalizedThree P}
  | degreeTwo =>
      {P : NormalizedProjective4 F9 // IsCanonicalNormalizedThree P}
  | degreeThree =>
      {P : NormalizedProjective4 F27 // IsCanonicalNormalizedThree P}
  | degreeFour =>
      {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P}

end ExtensionIndex25Three

/-- The geometric bridge needed through extension degree four: each semantic
point is a closed Frobenius orbit together with one position in that orbit.
The structure contains neither point-count equations nor an Euler recurrence. -/
abbrev ClosedPointBridge25ThreeLE4
    (C : CurveZetaEffectiveDivisors.ClosedPointGrading) :=
  PointOrbitClassificationOn C ExtensionIndex25Three
    ExtensionIndex25Three.exponent ExtensionIndex25Three.pointType

end MazurProof.RationalPointsN25QuotientMiddleRiemannRoch
