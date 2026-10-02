import ZChartFractionEquivCheck
import Mathlib.RingTheory.Algebraic.Basic
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectivePrincipalDivisor
open RationalPointsN25QuotientTwoWOpenPrimeSurjective N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
theorem basePolynomial_inFunctionField (p : Polynomial (ZMod 2)) :
    algebraMap N25F_NonBoundaryPrincipalDivisor.W K (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W p) =
      p.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz) := by
  have h : (algebraMap N25F_NonBoundaryPrincipalDivisor.W K).comp (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W) =
      (Polynomial.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_zmod _ _
    · change algebraMap N25F_NonBoundaryPrincipalDivisor.W K
        (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W Polynomial.X) =
        (Polynomial.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz)) Polynomial.X
      rw [Polynomial.aeval_X, algebraMap_Rz_X]
  exact congrArg (fun h : Polynomial (ZMod 2) →+* K => h p) h

end MazurProof.N25F_ProjectivePrincipalDivisor
namespace MazurProof.N25F_InfinityBaseMaps
private theorem inverse_aeval_injective
    {k L : Type*} [Field k] [Field L] [Algebra k L] (z : L)
    (hz : Function.Injective (Polynomial.aeval z : Polynomial k →ₐ[k] L)) :
    Function.Injective (Polynomial.aeval (1 / z) : Polynomial k →ₐ[k] L) := by
  apply transcendental_iff_injective.mp
  have ht : Transcendental k z := transcendental_iff_injective.mpr hz
  simpa only [one_div, Transcendental, IsAlgebraic.inv_iff] using ht

open RationalPointsN25QuotientTwoWOpenPrimeSurjective N25F_ZChartFractionMap
open N25F_ProjectivePrincipalDivisor
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
def infinityBaseToField : Polynomial (ZMod 2) →ₐ[ZMod 2] K :=
  Polynomial.aeval (1 / algebraMap W K qz)

/-- This is a genuine polynomial base, with no kernel. -/
theorem infinityBaseToField_injective : Function.Injective infinityBaseToField := by
  change Function.Injective (Polynomial.aeval (1 / algebraMap W K qz))
  apply inverse_aeval_injective
  intro p q h
  apply FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) W
  apply IsFractionRing.injective W K
  rw [basePolynomial_inFunctionField, basePolynomial_inFunctionField]
  exact h

#check @infinityBaseToField_injective
#print axioms infinityBaseToField
#print axioms infinityBaseToField_injective
end MazurProof.N25F_InfinityBaseMaps
