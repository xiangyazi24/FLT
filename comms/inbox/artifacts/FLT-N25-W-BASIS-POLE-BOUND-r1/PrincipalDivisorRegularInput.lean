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

end MazurProof.CurveDedekindDivisor
