import FLT.Assumptions.MazurProof.CurveZetaPointOrbitClassification
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

/-!
# The first four characteristic-two extension point types

The binary middle Riemann--Roch calculation uses the canonical N25 curve
over fields of cardinality `2`, `4`, `8`, and `16`.  This file collects the
four semantic field-valued point types and their structurally transferred
point counts.  Frobenius and divisor theory are deliberately kept in later
layers.
-/

namespace MazurProof.RationalPointsN25QuotientMiddleRiemannRoch

open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBinaryFieldSemantics

/-! ## Semantic extension-point counts -/

/-- The binary canonical-curve point-count sequence through degree four.
Values above degree four are unused bookkeeping values, not geometric
claims. -/
noncomputable def extensionPointCount25Two : ℕ → ℕ
  | 1 => Nat.card
      {P : NormalizedProjective4 F2 // IsCanonicalNormalizedTwo P}
  | 2 => Nat.card
      {P : NormalizedProjective4 SemanticF4 // IsCanonicalNormalizedTwo P}
  | 3 => Nat.card
      {P : NormalizedProjective4 SemanticF8 // IsCanonicalNormalizedTwo P}
  | 4 => Nat.card
      {P : NormalizedProjective4 SemanticF16 // IsCanonicalNormalizedTwo P}
  | _ => 0

/-- The canonical curve has five points over the binary prime field. -/
theorem extensionPointCount25Two_one : extensionPointCount25Two 1 = 5 :=
  semanticF2_canonical_card

/-- The quadratic binary extension introduces no new canonical point. -/
theorem extensionPointCount25Two_two : extensionPointCount25Two 2 = 5 :=
  semanticF4_canonical_card

/-- The canonical curve has twenty points over the cubic binary extension. -/
theorem extensionPointCount25Two_three : extensionPointCount25Two 3 = 20 :=
  semanticF8_canonical_card

/-- The canonical curve has twenty-nine points over the quartic binary
extension. -/
theorem extensionPointCount25Two_four : extensionPointCount25Two 4 = 29 :=
  semanticF16_canonical_card

/-! ## A common index for the four extension fields -/

/-- The binary extension degrees entering the genus-four calculation. -/
inductive ExtensionIndex25Two
  | degreeOne
  | degreeTwo
  | degreeThree
  | degreeFour

namespace ExtensionIndex25Two

/-- The residue-field exponent represented by an extension index. -/
def exponent : ExtensionIndex25Two → ℕ
  | degreeOne => 1
  | degreeTwo => 2
  | degreeThree => 3
  | degreeFour => 4

/-- Semantic canonical-curve points over the selected binary extension
field.  Every non-prime carrier uses the certified field wrapper rather
than the executable raw operation table. -/
def pointType : ExtensionIndex25Two → Type
  | degreeOne =>
      {P : NormalizedProjective4 F2 // IsCanonicalNormalizedTwo P}
  | degreeTwo =>
      {P : NormalizedProjective4 SemanticF4 // IsCanonicalNormalizedTwo P}
  | degreeThree =>
      {P : NormalizedProjective4 SemanticF8 // IsCanonicalNormalizedTwo P}
  | degreeFour =>
      {P : NormalizedProjective4 SemanticF16 // IsCanonicalNormalizedTwo P}

end ExtensionIndex25Two

/-- The binary geometric bridge required through degree four: each semantic
extension point is classified as a Frobenius closed-point slot. -/
abbrev ClosedPointBridge25TwoLE4
    (C : CurveZetaEffectiveDivisors.ClosedPointGrading) :=
  PointOrbitClassificationOn C ExtensionIndex25Two
    ExtensionIndex25Two.exponent ExtensionIndex25Two.pointType

end MazurProof.RationalPointsN25QuotientMiddleRiemannRoch
