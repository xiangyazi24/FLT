import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneQuarticFunctionField
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# The finite-place normalization of the binary plane function field

The integral closure of `F₂[z]` in the concrete plane function field is a
Dedekind domain with that function field as its fraction field.  Maximal
ideals contract to maximal base primes, and their relative ideal norms are
powers of those contractions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.SeparableRelativeNorm

open scoped nonZeroDivisors

set_option linter.overlappingInstances false

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]

local instance fractionAlgebra :
    Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra _ _

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" =>
  IntermediateField.normalClosure K L (AlgebraicClosure L)
local notation3 "T" => Ring.NormalClosure R S

local instance sAlgebraE : Algebra S E :=
  ((algebraMap L E).comp (algebraMap S L)).toAlgebra

local instance sLE : IsScalarTower S L E :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance tAlgebraE : Algebra T E :=
  inferInstanceAs (Algebra (integralClosure S E) E)

local instance tIntegralClosure : IsIntegralClosure T S E :=
  integralClosure.isIntegralClosure S E

local instance sTE : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance eFiniteDimensional : FiniteDimensional L E :=
  Module.Finite.right K L E

local instance tFractionRing : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E

local instance rLE : IsScalarTower R L E :=
  IsScalarTower.to₁₃₄ R K L E

local instance rSE : IsScalarTower R S E :=
  IsScalarTower.to₁₂₄ R S L E

local instance rTE : IsScalarTower R T E :=
  IsScalarTower.to₁₃₄ R S T E

omit [Module.Finite R S] in
/-- The normal closure over the fraction field remains separable over the
intermediate fraction field when the original finite extension is separable.
This is the replacement for the perfectness argument used by Mathlib's
normal-closure instance. -/
theorem normalClosure_isSeparable_top
    [Algebra.IsSeparable K L] : Algebra.IsSeparable L E := by
  letI : ∀ f : L →ₐ[K] AlgebraicClosure L,
      Algebra.IsSeparable K f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  letI : Algebra.IsSeparable K E := by
    rw [normalClosure_def]
    infer_instance
  exact Algebra.isSeparable_tower_top_of_isSeparable K L E

/-- A finite separable fraction-field extension has a Galois normal closure,
without requiring the base fraction field to be perfect. -/
theorem normalClosure_isGalois_of_isSeparable
    [Algebra.IsSeparable K L] : IsGalois K (FractionRing T) := by
  letI : Algebra.IsAlgebraic K (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.trans K L (AlgebraicClosure L)
  letI : Normal K (AlgebraicClosure L) := by
    rw [normal_iff]
    intro x
    exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  letI : Algebra.IsSeparable L E := normalClosure_isSeparable_top R S
  letI : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K L E
  letI : Normal K E := inferInstance
  letI : IsGalois K E := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

/-- For a maximal prime in a finite separable extension of Dedekind domains,
the exponent in its relative ideal norm is exactly its inertia degree.  This
is Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal` with separability replacing
the stronger, inapplicable perfect-base assumption. -/
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg P := by
  letI : Algebra.IsSeparable L E := normalClosure_isSeparable_top R S
  letI : Module.Finite S T := IsIntegralClosure.finite S L E T
  letI : Module.Finite R T := Module.Finite.trans S T
  letI : IsDedekindDomain T := integralClosure.isDedekindDomain S L E
  letI : IsGalois K (FractionRing T) :=
    normalClosure_isGalois_of_isSeparable R S
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois L (FractionRing T) :=
    IsGalois.tower_top_of_isGalois K L (FractionRing T)
  rwa [← Ideal.relNorm_relNorm R S,
    Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| Ideal.inertiaDeg_pos P Q

end MazurProof.SeparableRelativeNorm

namespace MazurProof.RationalPointsN25QuotientTwoPlaneNormalization

open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneQuarticFunctionField

local notation "k₂" => ZMod 2
local notation "Rz" => Polynomial k₂
local notation "Fz" => RatFunc k₂

/-- The normalization of the affine `z`-line in the plane function field. -/
abbrev PlaneNormalization :=
  FunctionField.ringOfIntegers k₂ PlaneFunctionField

/-- The normalization is finite over `F₂[z]`. -/
instance planeNormalization_finite : Module.Finite Rz PlaneNormalization :=
  IsIntegralClosure.finite Rz Fz PlaneFunctionField PlaneNormalization

/-- Contract a finite-place prime to the polynomial base. -/
def planeNormalizationBasePrime
    (P : Ideal PlaneNormalization) : Ideal Rz :=
  P.comap (algebraMap Rz PlaneNormalization)

/-- Maximal finite places contract to maximal primes of `F₂[z]`. -/
instance planeNormalizationBasePrime_isMaximal
    (P : Ideal PlaneNormalization) [P.IsMaximal] :
    (planeNormalizationBasePrime P).IsMaximal := by
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P

/-- A finite-place prime lies over its explicit contraction. -/
instance planeNormalizationBasePrime_liesOver
    (P : Ideal PlaneNormalization) :
    P.LiesOver (planeNormalizationBasePrime P) := by
  rw [Ideal.liesOver_iff]
  rfl

/-- Without yet identifying the exponent, the relative ideal norm of a
finite-place prime is a power of its contracted base prime. -/
theorem planeNormalization_relNorm_eq_basePrime_pow_some
    (P : Ideal PlaneNormalization) [P.IsMaximal] :
    ∃ s : ℕ, Ideal.relNorm Rz P =
      planeNormalizationBasePrime P ^ s := by
  letI : (planeNormalizationBasePrime P).IsPrime :=
    (planeNormalizationBasePrime_isMaximal P).isPrime
  exact Ideal.exists_relNorm_eq_pow_of_isPrime P
    (planeNormalizationBasePrime P)

local instance planeNormalization_fractionAlgebra :
    Algebra (FractionRing Rz) (FractionRing PlaneNormalization) :=
  FractionRing.liftAlgebra _ _

/-- Separability transported to the canonical fraction-ring types used by
the ideal-theoretic norm API. -/
instance planeNormalization_fractionRing_isSeparable :
    Algebra.IsSeparable (FractionRing Rz)
      (FractionRing PlaneNormalization) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv Rz Fz).symm.toRingEquiv
    (FractionRing.algEquiv PlaneNormalization PlaneFunctionField).symm.toRingEquiv ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv Rz Fz).symm
    (FractionRing.algEquiv PlaneNormalization PlaneFunctionField).symm _

/-- The exact exponent in the finite-place norm formula is the residue-field
degree over the corresponding polynomial prime. -/
theorem planeNormalization_relNorm_eq_basePrime_pow
    (P : Ideal PlaneNormalization) [P.IsMaximal] :
    Ideal.relNorm Rz P = planeNormalizationBasePrime P ^
      (planeNormalizationBasePrime P).inertiaDeg P := by
  exact SeparableRelativeNorm.relNorm_eq_pow_of_isMaximal_of_isSeparable
    Rz PlaneNormalization P (planeNormalizationBasePrime P)

end MazurProof.RationalPointsN25QuotientTwoPlaneNormalization
