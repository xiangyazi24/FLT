import FLT.Assumptions.MazurProof.N25F_InfinityCanonicalSeparable
import FLT.Assumptions.MazurProof.N25F_SeparableRelativeNorm
import FLT.Assumptions.MazurProof.N25F_InfinityResidueFields
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras

/-! The three actual center ideals have relative norm equal to the
reciprocal-coordinate prime. No perfectness assumption is used. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityPrimeNorms
open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityResidueFields N25F_InfinityCanonicalSeparable
open N25F_InfinityBoundaryAlgebras N25F_SeparableRelativeNorm
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra
local instance : Algebra BaseField (FractionRing InfinityNormalization) := FractionRing.liftAlgebra _ _
local instance : Algebra.IsSeparable BaseField (FractionRing InfinityNormalization) :=
  infinityCanonicalFraction_isSeparable

/-- The actual X center has relative norm (T), its residue degree being one. -/
theorem xInfinityPrime_relNorm :
    Ideal.relNorm BasePolynomial xInfinityPrime = infinityBasePrime := by
  rw [relNorm_prime_of_separable BasePolynomial InfinityNormalization
      xInfinityPrime infinityBasePrime,
    Ideal.inertiaDeg_eq_inertiaDeg', xInfinityPrime_inertiaDeg_eq_one, pow_one]

/-- The actual YZ center has relative norm (T), its residue degree being one. -/
theorem yzInfinityPrime_relNorm :
    Ideal.relNorm BasePolynomial yzInfinityPrime = infinityBasePrime := by
  rw [relNorm_prime_of_separable BasePolynomial InfinityNormalization
      yzInfinityPrime infinityBasePrime,
    Ideal.inertiaDeg_eq_inertiaDeg', yzInfinityPrime_inertiaDeg_eq_one, pow_one]

/-- The actual Z center has relative norm (T), its residue degree being one. -/
theorem zInfinityPrime_relNorm :
    Ideal.relNorm BasePolynomial zInfinityPrime = infinityBasePrime := by
  rw [relNorm_prime_of_separable BasePolynomial InfinityNormalization
      zInfinityPrime infinityBasePrime,
    Ideal.inertiaDeg_eq_inertiaDeg', zInfinityPrime_inertiaDeg_eq_one, pow_one]

end MazurProof.N25F_InfinityPrimeNorms
