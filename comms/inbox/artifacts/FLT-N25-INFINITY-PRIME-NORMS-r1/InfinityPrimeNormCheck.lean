import InfinityNormalizationCheck
import N25F_SeparableRelativeNorm
import Mathlib.RingTheory.RamificationInertia.Inertia

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityPrimeNormsCheck
open N25F_RationalBaseInversion N25F_InfinityNormalization N25F_SeparableRelativeNorm
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain InfinityNormalization]
variable [Module.Finite BasePolynomial InfinityNormalization]
variable [Module.IsTorsionFree BasePolynomial InfinityNormalization]
attribute [local instance] infinityPolynomialAlgebra
local instance : Algebra BaseField (FractionRing InfinityNormalization) := FractionRing.liftAlgebra _ _
variable [Algebra.IsSeparable BaseField (FractionRing InfinityNormalization)]

theorem prime_relNorm (q : Ideal InfinityNormalization) (p : Ideal BasePolynomial)
    [q.IsMaximal] [p.IsMaximal] [q.LiesOver p]
    (hf : q.inertiaDeg' BasePolynomial = 1) : Ideal.relNorm BasePolynomial q = p := by
  rw [relNorm_prime_of_separable BasePolynomial InfinityNormalization q p,
    Ideal.inertiaDeg_eq_inertiaDeg', hf, pow_one]

#check @prime_relNorm
#print axioms prime_relNorm
end MazurProof.N25F_InfinityPrimeNormsCheck
