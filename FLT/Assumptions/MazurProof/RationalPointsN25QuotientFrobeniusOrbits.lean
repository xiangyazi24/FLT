import FLT.Assumptions.MazurProof.CurveZetaFrobeniusOrbitGrading
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientExtensionPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientThreeBaseChange

/-!
# Frobenius orbits for the characteristic-three N25 curve

The characteristic-three extension fields of degrees one through four embed
in `𝔽_(3^12)`.  This file preserves the original characteristic-specific
API while delegating finite-field and normalized-projective descent to the
prime-generic implementation.  The only characteristic-three input is the
canonical quadric-cubic predicate and its coefficient-base-change law.

Arithmetic Frobenius is used throughout.  Its inverse has the same finite
orbits, but retaining one convention avoids an orientation mismatch between
the fixed-point realization and the closed-point grading.
-/

namespace MazurProof.RationalPointsN25QuotientFrobeniusOrbits

open Polynomial
open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientWeilThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic
open RationalPointsN25QuotientThreeBaseChange
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientMiddleRiemannRoch
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius

/-! ## Compatibility wrappers for the generic finite-field layer -/

/-- The common field containing the selected characteristic-three
extensions. -/
abbrev CommonThreeField := CommonField 3 12

/-- A named finite presentation of the common field, retained for API
compatibility.  Instance search uses the prime-generic instance. -/
@[reducible] noncomputable def commonThreeFieldFintype :
    Fintype CommonThreeField :=
  inferInstance

/-- Embed the canonical degree-`d` Galois field in the common field. -/
noncomputable def galoisFieldToCommon
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12) :
    GaloisField 3 d →ₐ[ZMod 3] CommonThreeField :=
  FiniteFieldFrobeniusDescent.galoisFieldToCommon
    3 12 d hdpos (by norm_num) hd

/-- Embed a finite characteristic-three field of cardinality `3^d` in the
common field. -/
noncomputable def finiteFieldToCommon
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K →+* CommonThreeField :=
  FiniteFieldFrobeniusDescent.finiteFieldToCommon
    3 12 K d hdpos (by norm_num) hd hcard

/-- The `3^d`-power fixed subtype of the common field. -/
abbrev PowerFixed (d : ℕ) :=
  FiniteFieldFrobeniusDescent.PowerFixed 3 12 d

/-- A named finite presentation of the fixed subtype, retained for API
compatibility. -/
@[reducible] noncomputable def powerFixedFintype (d : ℕ) :
    Fintype (PowerFixed d) :=
  inferInstance

/-- The common-field embedding with its fixed-power proof attached. -/
noncomputable def finiteFieldToPowerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K → PowerFixed d :=
  FiniteFieldFrobeniusDescent.finiteFieldToPowerFixed
    3 12 K d hdpos (by norm_num) hd hcard

/-- The fixed-power embedding is injective. -/
theorem finiteFieldToPowerFixed_injective
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    Function.Injective (finiteFieldToPowerFixed K d hdpos hd hcard) :=
  FiniteFieldFrobeniusDescent.finiteFieldToPowerFixed_injective
    3 12 K d hdpos (by norm_num) hd hcard

/-- A positive power of three is not one. -/
theorem three_pow_ne_one (d : ℕ) (hd : 0 < d) : 3 ^ d ≠ 1 := by
  exact ne_of_gt (one_lt_pow₀ (by omega) hd.ne')

/-- Degree of the characteristic-three fixed-subfield polynomial. -/
theorem commonPolynomial_natDegree (d : ℕ) (hd : 0 < d) :
    (X ^ (3 ^ d) - X : CommonThreeField[X]).natDegree = 3 ^ d :=
  FiniteFieldFrobeniusDescent.commonPolynomial_natDegree 3 12 d hd

/-- The fixed-subfield polynomial is nonzero in positive degree. -/
theorem commonPolynomial_ne_zero (d : ℕ) (hd : 0 < d) :
    (X ^ (3 ^ d) - X : CommonThreeField[X]) ≠ 0 :=
  FiniteFieldFrobeniusDescent.commonPolynomial_ne_zero 3 12 d hd

/-- View a power-fixed element as a root of the fixed-subfield polynomial. -/
noncomputable def powerFixedToRootSet (d : ℕ) (hd : 0 < d) :
    PowerFixed d ↪
      (X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet CommonThreeField :=
  FiniteFieldFrobeniusDescent.powerFixedToRootSet 3 12 d hd

/-- Polynomial root bounds control the size of the fixed subtype. -/
theorem powerFixed_card_le (d : ℕ) (hd : 0 < d) :
    Fintype.card (PowerFixed d) ≤ 3 ^ d :=
  FiniteFieldFrobeniusDescent.powerFixed_card_le 3 12 d hd

/-- The source field is explicitly equivalent to the fixed subtype via its
actual embedding. -/
noncomputable def finiteFieldEquivPowerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K ≃ PowerFixed d :=
  FiniteFieldFrobeniusDescent.finiteFieldEquivPowerFixed
    3 12 K d hdpos (by norm_num) hd hcard

/-- The fixed-subfield equivalence uses the same coefficient embedding. -/
@[simp]
theorem finiteFieldEquivPowerFixed_apply_val
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K) :
    (finiteFieldEquivPowerFixed K d hdpos hd hcard a).1 =
      finiteFieldToCommon K d hdpos hd hcard a := rfl

/-- One coherent characteristic-three realization, coupling the common-field
embedding with its fixed-subfield inverse. -/
noncomputable def fieldRealization
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : Realization 3 12 d K :=
  realization 3 12 K d hdpos (by norm_num) hd hcard

/-! ## Compatibility wrappers for generic Frobenius descent -/

/-- Arithmetic Frobenius on the common characteristic-three field. -/
noncomputable def commonFrobenius :
    CommonThreeField ≃ₐ[ZMod 3] CommonThreeField :=
  FiniteFieldFrobeniusDescent.commonFrobenius 3 12

/-- The `d`-th arithmetic-Frobenius iterate is the `3^d`-power map. -/
theorem commonFrobenius_pow_apply (d : ℕ) (x : CommonThreeField) :
    (commonFrobenius ^ d) x = x ^ (3 ^ d) :=
  FiniteFieldFrobeniusDescent.commonFrobenius_pow_apply 3 12 d x

/-- Semantic canonical curve points over a characteristic-three field. -/
abbrev CurvePoint (K : Type) [Field K] :=
  NormalizedProjectiveCurveFrobenius.CurvePoint canonicalThreeModel K

/-- The common curve-point type is finite. -/
noncomputable instance commonCurvePointFintype :
    Fintype (CurvePoint CommonThreeField) :=
  have : Finite (CurvePoint CommonThreeField) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite (CurvePoint CommonThreeField)

/-- Arithmetic Frobenius acting coordinatewise on common curve points. -/
noncomputable def commonPointFrobenius :
    Equiv.Perm (CurvePoint CommonThreeField) :=
  pointFrobenius canonicalThreeModel 3 12

/-- Compatibility name for the generic iterate-commutation lemma. -/
theorem self_iterate_commute_apply {A : Type*}
    (f : A → A) (d : ℕ) (x : A) :
    f (f^[d] x) = f^[d] (f x) :=
  NormalizedProjectiveCurveFrobenius.self_iterate_commute_apply f d x

/-- Iterated point Frobenius is coordinatewise iterated field Frobenius. -/
theorem commonPointFrobenius_iterate_val
    (d : ℕ) (P : CurvePoint CommonThreeField) :
    (commonPointFrobenius^[d] P).1 =
      NormalizedProjective4.map
        (commonFrobenius ^ d).toRingEquiv.toRingHom P.1 :=
  NormalizedProjectiveCurveFrobenius.pointFrobenius_iterate_val
    canonicalThreeModel 3 12 d P

/-- Normalized-projective points fixed by the selected Frobenius iterate. -/
abbrev ProjectiveFrobeniusFixed (d : ℕ) :=
  FiniteFieldFrobeniusDescent.ProjectiveFrobeniusFixed 3 12 d

/-- Embedded source coordinates are fixed by the corresponding Frobenius
iterate. -/
theorem finiteFieldToCommon_frobenius_fixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K) :
    (commonFrobenius ^ d) (finiteFieldToCommon K d hdpos hd hcard a) =
      finiteFieldToCommon K d hdpos hd hcard a :=
  FiniteFieldFrobeniusDescent.finiteFieldToCommon_frobenius_fixed
    3 12 K d hdpos (by norm_num) hd hcard a

/-- A Frobenius-fixed coordinate satisfies the fixed-power equation. -/
theorem frobenius_fixed_to_power_fixed
    (d : ℕ) (x : CommonThreeField) (hx : (commonFrobenius ^ d) x = x) :
    x ^ (3 ^ d) = x :=
  FiniteFieldFrobeniusDescent.frobenius_fixed_to_power_fixed 3 12 d x hx

/-- Descending an embedded coordinate returns the source coordinate. -/
theorem finiteFieldEquivPowerFixed_symm_embedding
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K)
    (ha : finiteFieldToCommon K d hdpos hd hcard a ^ (3 ^ d) =
      finiteFieldToCommon K d hdpos hd hcard a) :
    (finiteFieldEquivPowerFixed K d hdpos hd hcard).symm
      ⟨finiteFieldToCommon K d hdpos hd hcard a, ha⟩ = a :=
  FiniteFieldFrobeniusDescent.finiteFieldEquivPowerFixed_symm_embedding
    3 12 K d hdpos (by norm_num) hd hcard a ha

/-- Re-embedding a descended fixed coordinate recovers that coordinate. -/
theorem finiteFieldToCommon_symm_powerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (x : CommonThreeField)
    (hx : x ^ (3 ^ d) = x) :
    finiteFieldToCommon K d hdpos hd hcard
      ((finiteFieldEquivPowerFixed K d hdpos hd hcard).symm ⟨x, hx⟩) = x :=
  FiniteFieldFrobeniusDescent.finiteFieldToCommon_symm_powerFixed
    3 12 K d hdpos (by norm_num) hd hcard x hx

/-- Characteristic-three projective descent, now a thin wrapper around one
coherent generic realization. -/
noncomputable def projectiveEquivFrobeniusFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    NormalizedProjective4 K ≃ ProjectiveFrobeniusFixed d :=
  FiniteFieldFrobeniusDescent.projectiveEquivFrobeniusFixed
    3 12 K d (fieldRealization K d hdpos hd hcard)

/-- Characteristic-three curve descent, restricted structurally from the
generic projective equivalence. -/
noncomputable def curvePointEquivFixedByIterate
    (K : Type) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    CurvePoint K ≃ FixedByIterate commonPointFrobenius d :=
  NormalizedProjectiveCurveFrobenius.curvePointEquivFixedByIterate
    canonicalThreeModel 3 12 d K (fieldRealization K d hdpos hd hcard)

/-- The forward curve equivalence applies the common-field coefficient
embedding to normalized coordinates. -/
@[simp]
theorem curvePointEquivFixedByIterate_apply_val
    (K : Type) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (P : CurvePoint K) :
    ((curvePointEquivFixedByIterate K d hdpos hd hcard P).1).1 =
      NormalizedProjective4.map
        (finiteFieldToCommon K d hdpos hd hcard) P.1 := rfl

/-! ## The four extension fields and the resulting closed-point bridge -/

/-- The four semantic extension-point types are the fixed points of the
first four selected Frobenius iterates.  Only coefficient-field cardinalities
enter these realizations. -/
noncomputable def extensionFixedPointRealization25Three :
    FixedPointRealizationOn commonPointFrobenius ExtensionIndex25Three
      ExtensionIndex25Three.exponent ExtensionIndex25Three.pointType where
  realize i := by
    cases i with
    | degreeOne =>
        simpa [ExtensionIndex25Three.pointType,
          ExtensionIndex25Three.exponent, CurvePoint, canonicalThreeModel]
          using curvePointEquivFixedByIterate Trit 1
            (by norm_num) (by norm_num)
            (by norm_num [ternary_extension_cardinalities])
    | degreeTwo =>
        simpa [ExtensionIndex25Three.pointType,
          ExtensionIndex25Three.exponent, CurvePoint, canonicalThreeModel]
          using curvePointEquivFixedByIterate F9 2
            (by norm_num) (by norm_num)
            (by norm_num [ternary_extension_cardinalities])
    | degreeThree =>
        simpa [ExtensionIndex25Three.pointType,
          ExtensionIndex25Three.exponent, CurvePoint, canonicalThreeModel]
          using curvePointEquivFixedByIterate F27 3
            (by norm_num) (by norm_num)
            (by norm_num [ternary_extension_cardinalities])
    | degreeFour =>
        simpa [ExtensionIndex25Three.pointType,
          ExtensionIndex25Three.exponent, CurvePoint, canonicalThreeModel]
          using curvePointEquivFixedByIterate F81 4
            (by norm_num) (by norm_num)
            (by norm_num [ternary_extension_cardinalities])
  exponent_pos i := by
    cases i <;> norm_num [ExtensionIndex25Three.exponent]

/-- Exact arithmetic-Frobenius orbits in the common field, used as a
closed-point grading through degree four. -/
noncomputable def frobeniusOrbitGrading25ThreeLE4 :=
  orbitClosedPointGrading commonPointFrobenius

/-- Structural classification of the four semantic extension-point types
as exact Frobenius orbits with a position in each orbit. -/
noncomputable def frobeniusClosedPointBridge25ThreeLE4 :
    ClosedPointBridge25ThreeLE4 frobeniusOrbitGrading25ThreeLE4 :=
  extensionFixedPointRealization25Three.pointOrbitClassification

end MazurProof.RationalPointsN25QuotientFrobeniusOrbits
