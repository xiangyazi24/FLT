import FLT.Assumptions.MazurProof.CurveDedekindDivisor
import FLT.Assumptions.MazurProof.N25F_DedekindFactorDegree
import FLT.Assumptions.MazurProof.N25F_PrincipalDivisorCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors BigOperators

namespace MazurProof.CurveDedekindDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The existing principal-divisor coefficient of a nonzero regular function
is its actual principal ideal's normalized-factor multiplicity. -/
theorem principalDivisor_regular_apply (a : R) (ha : a ≠ 0)
    (f : Additive Kˣ) (hf : (f.toMul : K) = algebraMap R K a)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    principalDivisor f v =
      ((UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({a} : Set R))).count v.asIdeal : ℤ) := by
  change FractionalIdeal.count K v
    (FractionalIdeal.spanSingleton R⁰ (f.toMul : K)) = _
  rw [hf]
  exact MazurProof.DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors K a ha v

/-- The weighted degree of the existing affine principal divisor of a regular
function is the dimension of its quotient algebra over the finite base field. -/
theorem principalDivisor_degree_eq_quotient_finrank
    (k : Type*) [Field k] [Finite k] [Algebra k R]
    (a : R) (ha : a ≠ 0) [Module.Finite k (R ⧸ Ideal.span ({a} : Set R))]
    (f : Additive Kˣ) (hf : (f.toMul : K) = algebraMap R K a) :
    (principalDivisor f).sum
        (fun v n => n * (Module.finrank k (R ⧸ v.asIdeal) : ℤ)) =
      (Module.finrank k (R ⧸ Ideal.span ({a} : Set R)) : ℤ) := by
  classical
  let I : Ideal R := Ideal.span ({a} : Set R)
  have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  have hcoeff (v : IsDedekindDomain.HeightOneSpectrum R) :
      principalDivisor f v =
        ((UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal : ℤ) :=
    principalDivisor_regular_apply a ha f hf v
  calc
    (principalDivisor f).sum
        (fun v n => n * (Module.finrank k (R ⧸ v.asIdeal) : ℤ)) =
      ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
        ((UniqueFactorizationMonoid.normalizedFactors I).count P : ℤ) *
          (Module.finrank k (R ⧸ P) : ℤ) := by
      unfold Finsupp.sum
      apply Finset.sum_bij (fun v _ => v.asIdeal)
      · intro v hv
        have hne := Finsupp.mem_support_iff.mp hv
        rw [hcoeff] at hne
        simp only [Multiset.mem_toFinset, ← Multiset.count_pos, Nat.pos_iff_ne_zero]
        exact_mod_cast hne
      · intro v hv w hw h
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
    _ = (Module.finrank k (R ⧸ I) : ℤ) := by
      exact_mod_cast
        (MazurProof.DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors
          k I hI).symm

end MazurProof.CurveDedekindDivisor
