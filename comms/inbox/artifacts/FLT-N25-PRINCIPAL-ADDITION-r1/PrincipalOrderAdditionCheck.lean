import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.DedekindDomain.Factorization
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


set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors

namespace MazurProof.DedekindQuotientDegree

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
variable (K : Type*) [Field K] [Algebra S K] [IsFractionRing S K]

/-- The fractional-ideal valuation of a nonzero regular function is exactly
its principal ideal's normalized-factor multiplicity. -/
theorem count_spanSingleton_eq_normalizedFactors
    (a : S) (ha : a ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum S) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton S⁰ (algebraMap S K a)) =
      ((UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({a} : Set S))).count v.asIdeal : ℤ) := by
  have hI : Ideal.span ({a} : Set S) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]

end MazurProof.DedekindQuotientDegree

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_PrincipalOrderAddition
open N25F_LocalFractionFactorOrder

/-- Signed DVR orders satisfy the minimum inequality when all three functions
are nonzero. This is the additive closure input for bounded-pole spaces. -/
theorem log_ordFrac_add_ge_min {R L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (hs : x + y ≠ 0) :
    min (WithZero.log (Ring.ordFrac R x)) (WithZero.log (Ring.ordFrac R y)) ≤
      WithZero.log (Ring.ordFrac R (x + y)) := by
  have hxv : Ring.ordFrac R x ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hx).map (Ring.ordFrac R)).ne_zero
  have hyv : Ring.ordFrac R y ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hy).map (Ring.ordFrac R)).ne_zero
  have hsv : Ring.ordFrac R (x + y) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hs).map (Ring.ordFrac R)).ne_zero
  have h := Ring.ordFrac_add (R := R) x y hs
  by_cases hxy : Ring.ordFrac R x ≤ Ring.ordFrac R y
  · rw [min_eq_left hxy] at h
    exact (min_le_left _ _).trans ((WithZero.log_le_log hxv hsv).mpr h)
  · rw [min_eq_right (le_of_not_ge hxy)] at h
    exact (min_le_right _ _).trans ((WithZero.log_le_log hyv hsv).mpr h)

/-- The actual fractional-ideal count agrees with the genuine signed length
order on the canonical fraction field, at every height-one prime. -/
theorem count_spanSingleton_eq_log_ordFrac {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) (z : FractionRing R) (hz : z ≠ 0) :
    FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ z) =
      WithZero.log (Ring.ordFrac (Localization.AtPrime v.asIdeal) z) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div, ne_eq, not_true_eq_false] at hz
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hna : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr ha
  have hnb : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb'
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul (FractionRing R) v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hna)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hnb)),
    FractionalIdeal.count_inv,
    DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors (FractionRing R) a ha v,
    DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors (FractionRing R) b hb' v]
  simpa only [div_eq_mul_inv, sub_eq_add_neg] using
    (log_ordFrac_atPrime_div v.asIdeal v.ne_bot a b ha hb').symm

/-- Addition has the same minimum inequality for the exact fractional-ideal
coefficients used by the existing affine principal-divisor definition. -/
theorem count_spanSingleton_add_ge_min {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) (x y : FractionRing R)
    (hx : x ≠ 0) (hy : y ≠ 0) (hs : x + y ≠ 0) :
    min (FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ x))
        (FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ y)) ≤
      FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ (x + y)) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
      (Localization.AtPrime v.asIdeal)
  rw [count_spanSingleton_eq_log_ordFrac v x hx,
    count_spanSingleton_eq_log_ordFrac v y hy,
    count_spanSingleton_eq_log_ordFrac v (x + y) hs]
  exact log_ordFrac_add_ge_min x y hx hy hs

end MazurProof.N25F_PrincipalOrderAddition

#print axioms MazurProof.N25F_PrincipalOrderAddition.log_ordFrac_add_ge_min
#print axioms MazurProof.N25F_PrincipalOrderAddition.count_spanSingleton_eq_log_ordFrac
#print axioms MazurProof.N25F_PrincipalOrderAddition.count_spanSingleton_add_ge_min
