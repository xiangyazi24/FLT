import Mathlib.RingTheory.DedekindDomain.Factorization

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
