import FLT.Assumptions.MazurProof.N25F_InfinityNormalization
import FLT.Assumptions.MazurProof.N25F_IntegralBoundaryFactor

/-! The actual reciprocal integral normalization maps into each of the
three established boundary local rings inside the same curve field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryMaps
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization N25F_IntegralBoundaryFactor
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityPolynomialAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul

section X
local instance : Algebra BasePolynomial XLocalRing :=
  infinityBaseToX.toRingHom.toAlgebra
local instance : Algebra XLocalRing CurveField :=
  xLocalToFraction.toRingHom.toAlgebra
local instance : IsFractionRing XLocalRing CurveField :=
  xLocalToFraction_isFractionRing
local instance : IsScalarTower BasePolynomial XLocalRing CurveField :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (AlgHom.congr_fun xLocalToFraction_comp_infinityBase p).symm

/-- The actual normalization inclusion factored through the X boundary. -/
def infinityNormalizationToX : InfinityNormalization →ₐ[BasePolynomial] XLocalRing :=
  integralClosureToRing

@[simp]
theorem xLocalToFraction_infinityNormalizationToX (a : InfinityNormalization) :
    xLocalToFraction (infinityNormalizationToX a) = (a : CurveField) :=
  algebraMap_integralClosureToRing a

theorem infinityNormalizationToX_injective :
    Function.Injective infinityNormalizationToX :=
  integralClosureToRing_injective

end X

section YZ
local instance : Algebra BasePolynomial YZLocalRing :=
  infinityBaseToYZ.toRingHom.toAlgebra
local instance : Algebra YZLocalRing CurveField :=
  yzLocalToFraction.toRingHom.toAlgebra
local instance : IsFractionRing YZLocalRing CurveField :=
  yzLocalToFraction_isFractionRing
local instance : IsScalarTower BasePolynomial YZLocalRing CurveField :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (AlgHom.congr_fun yzLocalToFraction_comp_infinityBase p).symm

/-- The actual normalization inclusion factored through the YZ boundary. -/
def infinityNormalizationToYZ : InfinityNormalization →ₐ[BasePolynomial] YZLocalRing :=
  integralClosureToRing

@[simp]
theorem yzLocalToFraction_infinityNormalizationToYZ (a : InfinityNormalization) :
    yzLocalToFraction (infinityNormalizationToYZ a) = (a : CurveField) :=
  algebraMap_integralClosureToRing a

theorem infinityNormalizationToYZ_injective :
    Function.Injective infinityNormalizationToYZ :=
  integralClosureToRing_injective

end YZ

section Z
local instance : Algebra BasePolynomial ZLocalRing :=
  infinityBaseToZ.toRingHom.toAlgebra
local instance : Algebra ZLocalRing CurveField :=
  zLocalToFraction.toRingHom.toAlgebra
local instance : IsFractionRing ZLocalRing CurveField :=
  zLocalToFraction_isFractionRing
local instance : IsScalarTower BasePolynomial ZLocalRing CurveField :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (AlgHom.congr_fun zLocalToFraction_comp_infinityBase p).symm

/-- The actual normalization inclusion factored through the Z boundary. -/
def infinityNormalizationToZ : InfinityNormalization →ₐ[BasePolynomial] ZLocalRing :=
  integralClosureToRing

@[simp]
theorem zLocalToFraction_infinityNormalizationToZ (a : InfinityNormalization) :
    zLocalToFraction (infinityNormalizationToZ a) = (a : CurveField) :=
  algebraMap_integralClosureToRing a

theorem infinityNormalizationToZ_injective :
    Function.Injective infinityNormalizationToZ :=
  integralClosureToRing_injective

end Z

end MazurProof.N25F_InfinityBoundaryMaps
