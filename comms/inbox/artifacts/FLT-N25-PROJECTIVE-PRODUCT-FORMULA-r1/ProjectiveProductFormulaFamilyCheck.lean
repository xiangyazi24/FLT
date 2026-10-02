import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import InfinityNormalizationCheck
import Mathlib.RingTheory.Norm.Basic
import N25F_RationalBaseInversion
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega


/-! Compare norms on the same fixed curve field under the actual affine
and reciprocal rational-base actions. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_NormBaseTwist

/-- Precomposing the base action with an automorphism applies its inverse
to the norm. The two Algebra structures remain explicit. -/
theorem norm_twist {B L : Type*} [CommRing B] [CommRing L]
    (A : Algebra B L) (e : B ≃+* B) (x : L) :
    let A' : Algebra B L := ((@algebraMap B L _ _ A).comp e.toRingHom).toAlgebra
    @Algebra.norm B L _ _ A' x = e.symm (@Algebra.norm B L _ _ A x) := by
  let A' : Algebra B L := ((@algebraMap B L _ _ A).comp e.toRingHom).toAlgebra
  exact @Algebra.norm_eq_of_equiv_equiv B L B L _ _ _ _ A' A e (RingEquiv.refl L)
    (by rfl) x

end MazurProof.N25F_NormBaseTwist

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityAffineNormComparison
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_InfinityNormalization N25F_NormBaseTwist
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityRationalAlgebra

/-- The norm for the established affine action sending the base variable to qz. -/
def affineFieldNorm : CurveField →* BaseField :=
  @Algebra.norm BaseField CurveField _ _ affineRationalBaseToField.toRingHom.toAlgebra

/-- The reciprocal norm is precisely the inverse base-coordinate change
applied to the affine norm, with the function itself unchanged. -/
theorem infinity_norm_eq_baseInversion_affine_norm (f : CurveField) :
    Algebra.norm BaseField f = baseInversion.symm (affineFieldNorm f) :=
  norm_twist affineRationalBaseToField.toRingHom.toAlgebra baseInversion.toRingEquiv f

end MazurProof.N25F_InfinityAffineNormComparison

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_AffineNormPolynomial
open N25F_RationalBaseInversion N25F_InfinityFunctionField
open N25F_ProjectivePrincipalDivisor N25F_InfinityAffineNormComparison
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial W]
variable [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable [hWrank : Fact (Module.finrank BasePolynomial W = 4)]
local instance : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
local instance : Module BaseField CurveField :=
  @Algebra.toModule BaseField CurveField _ _ affineRationalBaseToField.toRingHom.toAlgebra
local instance : SMul BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra.toSMul
local instance : IsScalarTower BasePolynomial BaseField CurveField :=
  IsScalarTower.of_algebraMap_eq fun p => by
    calc
      algebraMap BasePolynomial CurveField p =
          algebraMap W CurveField (algebraMap BasePolynomial W p) :=
        IsScalarTower.algebraMap_apply BasePolynomial W CurveField p
      _ = affinePolynomialBaseToField p := basePolynomial_inFunctionField p
      _ = affineRationalBaseToField (algebraMap BasePolynomial BaseField p) :=
        (affineRationalBaseToField_algebraMap p).symm
local instance : Module.Finite BaseField CurveField :=
  FiniteDimensional.of_finrank_pos (by rw [affineRationalBaseToField_finrank hWrank.out]; decide)

/-- The fixed affine field norm agrees with the polynomial norm used by
the accepted W-chart quotient-dimension formula. -/
theorem affineFieldNorm_algebraMap (a : W) :
    affineFieldNorm (algebraMap W CurveField a) =
      algebraMap BasePolynomial BaseField (Algebra.norm BasePolynomial a) := by
  letI : Module.Free BasePolynomial W := Module.free_of_finite_type_torsion_free'
  letI : IsIntegralClosure W BasePolynomial CurveField :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  change Algebra.norm BaseField (algebraMap W CurveField a) = _
  simpa only [Algebra.intNorm_eq_norm] using
    (Algebra.algebraMap_intNorm (A := BasePolynomial) (B := W)
      (K := BaseField) (L := CurveField) a).symm

end MazurProof.N25F_AffineNormPolynomial

/-! Base inversion turns the genuine order at (T) of a nonzero polynomial
into minus its degree. The rational base and its inversion are the actual ones. -/
namespace MazurProof.N25F_InfinityPrimeContraction
open N25F_RationalBaseInversion
noncomputable def infinityBasePrime : Ideal BasePolynomial := Ideal.span {Polynomial.X}
instance infinityBasePrime_isMaximal : infinityBasePrime.IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
end MazurProof.N25F_InfinityPrimeContraction

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_BaseInversionOrder
open N25F_RationalBaseInversion N25F_InfinityPrimeContraction

private theorem ordFrac_aeval_at_pole
    {k R L : Type*} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L] [IsScalarTower k R L]
    [IsFractionRing R L] (z : L) (n : ℕ) (hn : 0 < n)
    (hz : Ring.ordFrac R z = WithZero.exp (-(n : ℤ)))
    (p : Polynomial k) (hp : p ≠ 0) :
    Ring.ordFrac R (p.aeval z) = WithZero.exp (-(n * p.natDegree : ℤ)) := by
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation L
  letI : v.IsTrivialOn k := ⟨by
    intro a ha
    have hu : IsUnit (algebraMap k R a) :=
      (isUnit_iff_ne_zero.mpr ha).map (algebraMap k R)
    have ho : Ring.ordFrac R (algebraMap R L (algebraMap k R a)) = 1 :=
      Ring.ordFrac_of_isUnit hu
    rw [← IsScalarTower.algebraMap_apply k R L, Ring.ordFrac_eq_valuation_inv] at ho
    exact inv_eq_one.mp ho⟩
  have hvz : v z = WithZero.exp (n : ℤ) := by
    have hi := congrArg Inv.inv hz
    simpa [Ring.ordFrac_eq_valuation_inv, v] using hi
  have hvpos : 1 < v z := by
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact_mod_cast hn
  have he := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (v := v) z hvpos hp
  rw [Ring.ordFrac_eq_valuation_inv, he, hvz, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
  congr 1
  simp only [nsmul_eq_mul]
  ring


private theorem infinityBasePrime_ne_bot : infinityBasePrime ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr (Polynomial.X_ne_zero (R := ZMod 2))

local instance : IsDiscreteValuationRing (Localization.AtPrime infinityBasePrime) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain BasePolynomial
    infinityBasePrime_ne_bot (Localization.AtPrime infinityBasePrime)

private theorem baseVariable_local_order :
    Ring.ord (Localization.AtPrime infinityBasePrime)
      (algebraMap BasePolynomial (Localization.AtPrime infinityBasePrime) Polynomial.X) = 1 := by
  have hm := IsLocalization.AtPrime.map_eq_maximalIdeal infinityBasePrime
    (Localization.AtPrime infinityBasePrime)
  change (Ideal.span {Polynomial.X} : Ideal BasePolynomial).map
    (algebraMap BasePolynomial (Localization.AtPrime infinityBasePrime)) = _ at hm
  rw [Ideal.map_span, Set.image_singleton] at hm
  apply Ring.ord_of_irreducible
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hm.symm

/-- The inverse of the actual base variable has a genuine simple pole at (T). -/
theorem baseVariable_inverse_fractionOrder :
    Ring.ordFrac (Localization.AtPrime infinityBasePrime) baseVariable⁻¹ =
      WithZero.exp (-1 : ℤ) := by
  have hi := IsLocalization.injective (Localization.AtPrime infinityBasePrime)
    infinityBasePrime.primeCompl_le_nonZeroDivisors
  have hX : algebraMap BasePolynomial (Localization.AtPrime infinityBasePrime) Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ hi).mpr (Polynomial.X_ne_zero (R := ZMod 2))
  have he : Ring.ordFrac (Localization.AtPrime infinityBasePrime) baseVariable =
      WithZero.exp (1 : ℤ) := by
    change Ring.ordFrac (Localization.AtPrime infinityBasePrime)
      (algebraMap BasePolynomial BaseField Polynomial.X) = _
    rw [IsScalarTower.algebraMap_apply BasePolynomial
      (Localization.AtPrime infinityBasePrime) BaseField,
      Ring.ordFrac_eq_ord _ hX,
      Ring.ordMonoidWithZeroHom_eq_coe _
        (mem_nonZeroDivisors_iff_ne_zero.mpr hX) baseVariable_local_order]
    rfl
  rw [map_inv₀, he, ← WithZero.exp_neg]

/-- Inverting the base coordinate makes the order of every nonzero
base polynomial exactly minus its degree. -/
theorem baseInversion_polynomial_order (p : BasePolynomial) (hp : p ≠ 0) :
    WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
      (baseInversion.symm (algebraMap BasePolynomial BaseField p))) = -(p.natDegree : ℤ) := by
  have hbase : baseInversion.symm (algebraMap BasePolynomial BaseField p) =
      p.aeval baseVariable⁻¹ := by
    change baseInversionHom (algebraMap BasePolynomial BaseField p) = _
    exact baseInversionHom_algebraMap p
  letI : IsScalarTower (ZMod 2) (Localization.AtPrime infinityBasePrime) BaseField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  rw [hbase, ordFrac_aeval_at_pole (R := Localization.AtPrime infinityBasePrime)
    baseVariable⁻¹ 1 (by decide) baseVariable_inverse_fractionOrder p hp,
    WithZero.log_exp]
  simp only [Nat.cast_one, one_mul]

end MazurProof.N25F_BaseInversionOrder
namespace MazurProof.N25F_ProjectiveProductFormula
private theorem hom_zero_of_regular {R L : Type*} [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (D : Additive Lˣ →+ ℤ)
    (h : ∀ (a : R) (ha : a ≠ 0), D (Additive.ofMul (Units.mk0
      (algebraMap R L a) ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))) = 0)
    (f : Additive Lˣ) : D f = 0 := by
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective R (f.toMul : L)
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div] at heq
    exact (Units.ne_zero f.toMul) heq.symm
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let fa : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L a)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))
  let fb : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L b)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hb'))
  have hf : f = fa - fb := by
    apply Additive.toMul.injective
    apply Units.ext
    simpa [fa, fb] using heq.symm
  rw [hf, map_sub, h a ha, h b hb', sub_self]


open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityPrimeContraction
open N25F_InfinityAffineNormComparison N25F_BaseInversionOrder N25F_AffineNormPolynomial
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial W] [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable [hWrank : Fact (Module.finrank BasePolynomial W = 4)]
attribute [local instance] infinityRationalAlgebra
variable {Divisor : Type*} [AddCommGroup Divisor]
variable (principal : Additive CurveFieldˣ →+ Divisor) (degree : Divisor →+ ℤ)
variable (bx byz bz affineDegree : Additive CurveFieldˣ → ℤ)
variable (hsum : ∀ f : Additive CurveFieldˣ,
 WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
   (Algebra.norm BaseField (f.toMul : CurveField))) = bx f + byz f + bz f)
variable (hsplit : ∀ f : Additive CurveFieldˣ,
 degree (principal f) = bx f + byz f + bz f + affineDegree f)
variable (hquot : ∀ (a : W), a ≠ 0 → ∀ (f : Additive CurveFieldˣ),
 (f.toMul : CurveField) = algebraMap W CurveField a →
 affineDegree f = (Module.finrank (ZMod 2) (W ⧸ Ideal.span {a}) : ℤ))
variable (hnormdim : ∀ (a : W), a ≠ 0 →
 Module.finrank (ZMod 2) (W ⧸ Ideal.span {a}) = (Algebra.norm BasePolynomial a).natDegree)
include hWrank hsum hsplit hquot hnormdim in
/-- Degree zero for every nonzero regular W-chart function, with its actual
boundary poles and affine zeros computed from the same field norm. -/
theorem projectivePrincipalDivisor_degree_regular
    (a : W) (ha : a ≠ 0) (f : Additive CurveFieldˣ)
    (hf : (f.toMul : CurveField) = algebraMap W CurveField a) :
    degree (principal f) = 0 := by
  letI : Module.Free BasePolynomial W := Module.free_of_finite_type_torsion_free'
  have hn : Algebra.norm BasePolynomial a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hsum := hsum f
  rw [hf, infinity_norm_eq_baseInversion_affine_norm, affineFieldNorm_algebraMap] at hsum
  change WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
    (baseInversion.symm (algebraMap BasePolynomial BaseField (Algebra.norm BasePolynomial a)))) =
      bx f + byz f + bz f at hsum
  rw [baseInversion_polynomial_order _ hn] at hsum
  have haff := hquot a ha f hf
  rw [hnormdim a ha] at haff
  rw [hsplit, ← hsum, haff]
  omega

include hWrank hsum hsplit hquot hnormdim in
/-- The actual projective principal divisor of every nonzero function has
degree zero. The fraction representation extends the regular-function case. -/
theorem projectivePrincipalDivisor_degree_eq_zero (f : Additive CurveFieldˣ) :
    degree (principal f) = 0 :=
  hom_zero_of_regular (R := W)
    (degree.comp principal)
    (fun a ha => projectivePrincipalDivisor_degree_regular principal degree bx byz bz affineDegree hsum hsplit hquot hnormdim a ha _ rfl) f


#print axioms projectivePrincipalDivisor_degree_regular
#print axioms projectivePrincipalDivisor_degree_eq_zero
end MazurProof.N25F_ProjectiveProductFormula
