import FLT.Assumptions.MazurProof.N25F_ExactCountWeightedSum
import FLT.Assumptions.MazurProof.N25F_DedekindFactorDegree
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors BigOperators

namespace MazurProof.N25F_ExactCountWeightedSum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Exact valuation counts identify a divisor's residue-weighted degree with
an ideal quotient dimension, using the existing Dedekind factor-degree theorem. -/
theorem weighted_sum_eq_quotient_finrank_of_exact_counts
    (k : Type*) [Field k] [Finite k] [Algebra k R]
    (I : Ideal R) (hI : I ≠ ⊥) [Module.Finite k (R ⧸ I)]
    (d : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)
    (hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = d v) :
    d.sum (fun v m => m * (Module.finrank k (R ⧸ v.asIdeal) : ℤ)) =
      (Module.finrank k (R ⧸ I) : ℤ) := by
  classical
  rw [weighted_sum_eq_of_exact_counts I hI d hcount
    (fun P => (Module.finrank k (R ⧸ P) : ℤ))]
  exact_mod_cast
    (DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors k I hI).symm

/-- Binary residue-degree specialization, ready for the actual W-chart ideal.
Finiteness is explicit here; its actual-W producer is already available. -/
theorem binary_weighted_sum_eq_quotient_finrank_of_exact_counts
    [Algebra (ZMod 2) R]
    (I : Ideal R) (hI : I ≠ ⊥) [Module.Finite (ZMod 2) (R ⧸ I)]
    (d : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)
    (hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = d v) :
    d.sum (fun v m => m * (Module.finrank (ZMod 2) (R ⧸ v.asIdeal) : ℤ)) =
      (Module.finrank (ZMod 2) (R ⧸ I) : ℤ) :=
  weighted_sum_eq_quotient_finrank_of_exact_counts (ZMod 2) I hI d hcount

end MazurProof.N25F_ExactCountWeightedSum
