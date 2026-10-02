import FLT.Assumptions.MazurProof.N25F_InfinityNormMultiplicity
import FLT.Assumptions.MazurProof.N25F_LocalFactorOrder

/-! The integral norm of a nonzero actual normalization element has order
at (T) equal to the sum of its three genuine localization orders. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityPrincipalNormOrder
open UniqueFactorizationMonoid
open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityNormMultiplicity N25F_LocalFactorOrder N25F_InfinityBoundaryAlgebras
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

/-- A principal ideal's norm multiplicity is the sum of the actual three
local orders of its generator. No function-norm identity is assumed. -/
theorem infinity_intNorm_local_order (a : InfinityNormalization) (ha : a ≠ 0) :
    Ring.ord (Localization.AtPrime infinityBasePrime)
      (algebraMap BasePolynomial (Localization.AtPrime infinityBasePrime)
        (Algebra.intNorm BasePolynomial InfinityNormalization a)) =
      Ring.ord (Localization.AtPrime xInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime xInfinityPrime) a) +
      Ring.ord (Localization.AtPrime yzInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime yzInfinityPrime) a) +
      Ring.ord (Localization.AtPrime zInfinityPrime)
        (algebraMap InfinityNormalization (Localization.AtPrime zInfinityPrime) a) := by
  have hI : (Ideal.span {a} : Ideal InfinityNormalization) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  have hN : Ideal.relNorm BasePolynomial (Ideal.span {a}) ≠ ⊥ :=
    Ideal.relNorm_eq_bot_iff.not.mpr hI
  rw [Ideal.relNorm_singleton] at hN
  have hNa : Algebra.intNorm BasePolynomial InfinityNormalization a ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mp hN
  have hp : infinityBasePrime ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Polynomial.X_ne_zero (R := ZMod 2))
  rw [ord_algebraMap_eq_factor_count _ hNa _ hp,
    ord_algebraMap_eq_factor_count a ha _ xInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count a ha _ yzInfinityPrime_ne_bot,
    ord_algebraMap_eq_factor_count a ha _ zInfinityPrime_ne_bot]
  have h := infinity_relNorm_multiplicity (Ideal.span {a}) hI
  rw [Ideal.relNorm_singleton] at h
  simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℕ∞)) h

end MazurProof.N25F_InfinityPrincipalNormOrder
