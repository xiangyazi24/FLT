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

#print axioms MazurProof.N25F_LocalFactorOrder.local_length_eq_factor_count
#print axioms MazurProof.N25F_LocalFactorOrder.ord_algebraMap_eq_factor_count
