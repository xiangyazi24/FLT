import FLT.Assumptions.MazurProof.CurveZetaFrobeniusOrbitGrading
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoBaseChange
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoExtensionPoints

/-!
# Frobenius orbits for the characteristic-two N25 curve

The semantic fields of cardinality `2`, `4`, `8`, and `16` all embed in the
common field `𝔽_(2^12)`.  Generic normalized-projective descent identifies
their canonical curve points with the fixed points of the first four
arithmetic-Frobenius iterates.  The permutation-orbit construction then
supplies the honest closed-point grading required by the Euler recurrence.

Only coefficient-field cardinalities enter the realization constructor.
The curve-point equivalences themselves descend coordinates and reflect the
quadric-cubic equations; they are not manufactured from point-count
equalities.
-/

namespace MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits

open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientMiddleRiemannRoch
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius

/-- The common degree-twelve binary field contains the selected extensions
because each degree from one through four divides twelve. -/
abbrev CommonTwoField := CommonField 2 12

/-- Semantic points on the characteristic-two canonical model. -/
abbrev CurvePointTwo (K : Type) [Field K] :=
  CurvePoint canonicalTwoModel K

/-- The common-field curve-point type is finite as a subtype of normalized
projective four-space over a finite field. -/
noncomputable instance commonCurvePointTwoFintype :
    Fintype (CurvePointTwo CommonTwoField) :=
  have : Finite (CurvePointTwo CommonTwoField) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite (CurvePointTwo CommonTwoField)

/-- Arithmetic Frobenius acts coordinatewise on common binary curve points. -/
noncomputable def commonPointFrobeniusTwo :
    Equiv.Perm (CurvePointTwo CommonTwoField) :=
  pointFrobenius canonicalTwoModel 2 12

/-- One coherent realization of a selected binary extension inside the
common field.  The embedded coordinates and the fixed-subfield inverse are
coupled by the `Realization` coherence law. -/
noncomputable def fieldRealizationTwo
    (K : Type*) [Field K] [Fintype K] [CharP K 2]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 2 ^ d) :
    Realization 2 12 d K :=
  realization 2 12 K d hdpos (by norm_num) hd hcard

/-- Compatibility wrapper identifying the generic fixed-function subtype
with fixed points of the public Frobenius permutation. -/
noncomputable def curvePointEquivFixedByIterateTwo
    (K : Type) [Field K] [Fintype K] [CharP K 2]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 2 ^ d) :
    CurvePointTwo K ≃
      CurveZetaFrobeniusOrbitGrading.FixedByIterate
        commonPointFrobeniusTwo d :=
  curvePointEquivFixedByIterate canonicalTwoModel 2 12 d K
    (fieldRealizationTwo K d hdpos hd hcard)

/-- The four semantic binary extension-point types are precisely the fixed
points of the corresponding arithmetic-Frobenius iterates. -/
noncomputable def extensionFixedPointRealization25Two :
    FixedPointRealizationOn commonPointFrobeniusTwo ExtensionIndex25Two
      ExtensionIndex25Two.exponent ExtensionIndex25Two.pointType where
  realize i := by
    cases i with
    | degreeOne =>
        simpa [ExtensionIndex25Two.pointType, ExtensionIndex25Two.exponent,
          CurvePointTwo, canonicalTwoModel] using
          curvePointEquivFixedByIterateTwo F2 1
            (by norm_num) (by norm_num) (by decide)
    | degreeTwo =>
        simpa [ExtensionIndex25Two.pointType, ExtensionIndex25Two.exponent,
          CurvePointTwo, canonicalTwoModel] using
          curvePointEquivFixedByIterateTwo SemanticF4 2
            (by norm_num) (by norm_num) (by decide)
    | degreeThree =>
        simpa [ExtensionIndex25Two.pointType, ExtensionIndex25Two.exponent,
          CurvePointTwo, canonicalTwoModel] using
          curvePointEquivFixedByIterateTwo SemanticF8 3
            (by norm_num) (by norm_num) (by decide)
    | degreeFour =>
        simpa [ExtensionIndex25Two.pointType, ExtensionIndex25Two.exponent,
          CurvePointTwo, canonicalTwoModel] using
          curvePointEquivFixedByIterateTwo SemanticF16 4
            (by norm_num) (by norm_num) (by decide)
  exponent_pos i := by
    cases i <;> norm_num [ExtensionIndex25Two.exponent]

/-- Exact arithmetic-Frobenius orbits in `𝔽_(2^12)`, retained as a
closed-point grading.  Completeness is asserted only through the four
selected degrees. -/
noncomputable def frobeniusOrbitGrading25TwoLE4 :=
  orbitClosedPointGrading commonPointFrobeniusTwo

/-- Structural classification of the first four semantic extension-point
types by exact Frobenius orbits and positions within those orbits. -/
noncomputable def frobeniusClosedPointBridge25TwoLE4 :
    ClosedPointBridge25TwoLE4 frobeniusOrbitGrading25TwoLE4 :=
  extensionFixedPointRealization25Two.pointOrbitClassification

end MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits
