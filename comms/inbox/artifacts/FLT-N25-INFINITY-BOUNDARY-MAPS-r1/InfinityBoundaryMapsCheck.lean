import InfinityNormalizationCheck
import N25F_IntegralBoundaryFactor

/-! Actual reciprocal normalization carrier; a boundary-ring family exposing
only the established common-field and reciprocal-base compatibility facts. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryMapsCheck
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization N25F_IntegralBoundaryFactor
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityPolynomialAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul

variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R] [IsIntegrallyClosed R]

/-- The actual normalization carrier factors through any one of the
three established compatible boundary-ring embeddings. -/
theorem infinityNormalization_boundary_factor
    (baseToR : BasePolynomial →ₐ[ZMod 2] R)
    (localToField : R →ₐ[ZMod 2] CurveField)
    (hComp : localToField.comp baseToR = infinityBaseToField)
    (hFrac : letI : Algebra R CurveField := localToField.toRingHom.toAlgebra
      IsFractionRing R CurveField) :
    letI : Algebra BasePolynomial R := baseToR.toRingHom.toAlgebra
    ∃ f : InfinityNormalization →ₐ[BasePolynomial] R,
      (∀ a, localToField (f a) = (a : CurveField)) ∧ Function.Injective f := by
  letI : Algebra BasePolynomial R := baseToR.toRingHom.toAlgebra
  letI : Algebra R CurveField := localToField.toRingHom.toAlgebra
  letI : IsFractionRing R CurveField := hFrac
  letI : IsScalarTower BasePolynomial R CurveField :=
    IsScalarTower.of_algebraMap_eq fun p =>
      (AlgHom.congr_fun hComp p).symm
  exact ⟨integralClosureToRing, algebraMap_integralClosureToRing,
    integralClosureToRing_injective⟩

#check @infinityNormalization_boundary_factor
#print axioms infinityNormalization_boundary_factor
end MazurProof.N25F_InfinityBoundaryMapsCheck
