import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! Normalized ideal-factor counts are the genuine length orders at the
corresponding Dedekind localizations. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_LocalFactorOrder
open UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Local quotient length reads exactly the chosen prime-factor multiplicity. -/
theorem local_length_eq_factor_count (I : Ideal R) (hI : I ≠ ⊥)
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) =
      (normalizedFactors I).count p := by
  classical
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp
      (Localization.AtPrime p)
  obtain ⟨J, hcop, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI p
  have hnot : ¬ J ≤ p := by
    intro hle
    rw [sup_of_le_left hle] at hcop
    exact (inferInstance : p.IsPrime).ne_top hcop
  have hm : I.map (algebraMap R (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ (normalizedFactors I).count p := by
    conv_lhs => rw [hfac]
    rw [Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime p) hnot,
      Ideal.mul_top, Localization.AtPrime.map_eq_maximalIdeal]
  rw [hm, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- The actual order of a nonzero regular function is its principal ideal's
normalized-factor count, with no assumed valuation compatibility. -/
theorem ord_algebraMap_eq_factor_count (a : R) (ha : a ≠ 0)
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
      (normalizedFactors (Ideal.span {a})).count p := by
  have h := local_length_eq_factor_count (Ideal.span {a})
    (Ideal.span_singleton_eq_bot.not.mpr ha) p hp
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h

end MazurProof.N25F_LocalFactorOrder

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FractionOrderDifference

/-- Compute the genuine signed fraction-field order using quotient lengths. -/
theorem log_ordFrac_div {R L : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R L a / algebraMap R L b)) =
      ((Ring.ord R a).toNat : ℤ) - ((Ring.ord R b).toNat : ℤ) := by
  have he (c : R) (hc : c ≠ 0) :
      Ring.ordFrac R (algebraMap R L c) =
        WithZero.exp ((Ring.ord R c).toNat : ℤ) := by
    have hc' : c ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hc
    rw [Ring.ordFrac_eq_ord R hc,
      Ring.ordMonoidWithZeroHom_eq_coe R hc'
        (ENat.coe_toNat (Ring.ord_ne_top hc')).symm]
    rfl
  rw [map_div₀, he a ha, he b hb, ← WithZero.exp_sub, WithZero.log_exp]

end MazurProof.N25F_FractionOrderDifference

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_LocalFractionFactorOrder
open UniqueFactorizationMonoid N25F_LocalFactorOrder N25F_FractionOrderDifference

theorem log_ordFrac_atPrime_div {A : Type*} [CommRing A] [IsDedekindDomain A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac (Localization.AtPrime p)
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) =
      ((normalizedFactors (Ideal.span {a})).count p : ℤ) -
      ((normalizedFactors (Ideal.span {b})).count p : ℤ) := by
  have hi := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have ha' : algebraMap A (Localization.AtPrime p) a ≠ 0 := (map_ne_zero_iff _ hi).mpr ha
  have hb' : algebraMap A (Localization.AtPrime p) b ≠ 0 := (map_ne_zero_iff _ hi).mpr hb
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A),
    log_ordFrac_div _ _ ha' hb', ord_algebraMap_eq_factor_count a ha p hp,
    ord_algebraMap_eq_factor_count b hb p hp]
  simp only [ENat.toNat_coe]

end MazurProof.N25F_LocalFractionFactorOrder

#print axioms MazurProof.N25F_LocalFractionFactorOrder.log_ordFrac_atPrime_div
