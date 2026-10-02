import InfinitySeparableCheck
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! The actual integral normalization of the reciprocal polynomial base
inside the fixed curve function field. Its finite degree-four, Dedekind
and fraction-field structures are proved, with no normalization premise. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityNormalization

open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityFunctionField N25F_InfinitySeparable
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [hWrank : Fact (Module.finrank BasePolynomial N25F_NonBoundaryPrincipalDivisor.W = 4)]
variable [hInfinitySeparable :
  letI : Algebra BaseField CurveField := infinityRationalBaseToField.toRingHom.toAlgebra
  Algebra.IsSeparable BaseField CurveField]

/-- The precise reciprocal polynomial action used in the integral closure. -/
abbrev infinityPolynomialAlgebra : Algebra BasePolynomial CurveField :=
  infinityBaseToField.toRingHom.toAlgebra

/-- The compatible reciprocal rational action, on the same field. -/
abbrev infinityRationalAlgebra : Algebra BaseField CurveField :=
  infinityRationalBaseToField.toRingHom.toAlgebra

attribute [local instance] infinityPolynomialAlgebra infinityRationalAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul
local instance : Module BaseField CurveField :=
  @Algebra.toModule BaseField CurveField _ _ infinityRationalAlgebra
local instance : SMul BaseField CurveField := infinityRationalAlgebra.toSMul

local instance : IsScalarTower BasePolynomial BaseField CurveField :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (infinityRationalBaseToField_algebraMap p).symm

local instance : IsScalarTower (ZMod 2) BasePolynomial CurveField :=
  IsScalarTower.of_algebraMap_eq fun a => (infinityBaseToField.commutes a).symm

local instance : Module.Finite BaseField CurveField :=
  (infinityRationalBaseToField_finite_finrank hWrank.out).1


local instance : Module.IsTorsionFree BasePolynomial CurveField :=
  Module.IsTorsionFree.trans_faithfulSMul BasePolynomial BaseField CurveField

/-- The actual integral closure, using the reciprocal action fixed above. -/
abbrev InfinityNormalization := ↥(integralClosure BasePolynomial CurveField)

/-- The integral normalization is finite over the reciprocal polynomial base. -/
instance infinityNormalization_finite : Module.Finite BasePolynomial InfinityNormalization :=
  IsIntegralClosure.finite BasePolynomial BaseField CurveField InfinityNormalization

/-- The same curve field is the fraction field of this actual normalization. -/
instance infinityNormalization_isFractionRing : IsFractionRing InfinityNormalization CurveField :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    BasePolynomial BaseField CurveField InfinityNormalization

/-- The actual normalization is Dedekind. -/
instance infinityNormalization_isDedekindDomain : IsDedekindDomain InfinityNormalization :=
  IsIntegralClosure.isDedekindDomain BasePolynomial BaseField CurveField InfinityNormalization

/-- The reciprocal normalization has polynomial-base rank four. -/
theorem infinityNormalization_finrank_eq_four :
    Module.finrank BasePolynomial InfinityNormalization = 4 := by
  rw [IsIntegralClosure.rank BasePolynomial BaseField CurveField InfinityNormalization]
  exact (infinityRationalBaseToField_finite_finrank hWrank.out).2

#check @InfinityNormalization
#check @infinityNormalization_finite
#check @infinityNormalization_isFractionRing
#check @infinityNormalization_isDedekindDomain
#check @infinityNormalization_finrank_eq_four
#print axioms infinityPolynomialAlgebra
#print axioms infinityRationalAlgebra
#print axioms InfinityNormalization
#print axioms infinityNormalization_finite
#print axioms infinityNormalization_isFractionRing
#print axioms infinityNormalization_isDedekindDomain
#print axioms infinityNormalization_finrank_eq_four
end MazurProof.N25F_InfinityNormalization
