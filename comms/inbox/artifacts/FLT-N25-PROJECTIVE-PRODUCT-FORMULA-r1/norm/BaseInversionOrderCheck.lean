import N25F_RationalBaseInversion
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.NormNum

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

#print axioms baseVariable_inverse_fractionOrder
#print axioms baseInversion_polynomial_order
end MazurProof.N25F_BaseInversionOrder
