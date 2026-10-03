import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors BigOperators

namespace MazurProof.N25F_ExactCountWeightedSum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Reindex any integer-weighted exact valuation vector by the actual normalized
prime factors of its nonzero integral ideal. No quotient dimension is assumed. -/
theorem weighted_sum_eq_of_exact_counts
    (I : Ideal R) (hI : I ≠ ⊥)
    (d : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)
    (hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = d v)
    (w : Ideal R → ℤ) :
    d.sum (fun v m => m * w v.asIdeal) =
      ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
        ((UniqueFactorizationMonoid.normalizedFactors I).count P : ℤ) * w P := by
  classical
  have hcoeff (v : IsDedekindDomain.HeightOneSpectrum R) :
      d v = ((UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal : ℤ) := by
    rw [← hcount v, FractionalIdeal.count_coe K v hI,
      Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
  unfold Finsupp.sum
  apply Finset.sum_bij (fun v _ => v.asIdeal)
  · intro v hv
    have hne := Finsupp.mem_support_iff.mp hv
    rw [hcoeff] at hne
    simp only [Multiset.mem_toFinset, ← Multiset.count_pos, Nat.pos_iff_ne_zero]
    exact_mod_cast hne
  · intro v hv u hu h
    exact IsDedekindDomain.HeightOneSpectrum.ext h
  · intro P hP
    have hmem := Multiset.mem_toFinset.mp hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hmem
    let v : IsDedekindDomain.HeightOneSpectrum R :=
      ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    refine ⟨v, ?_, rfl⟩
    rw [Finsupp.mem_support_iff, hcoeff]
    exact_mod_cast (ne_of_gt (Multiset.count_pos.mpr hmem))
  · intro v hv
    rw [hcoeff]

end MazurProof.N25F_ExactCountWeightedSum
