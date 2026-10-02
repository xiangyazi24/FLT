import InfinityNormalizationCheck
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! The three actual boundary rings determine nonzero prime centers on the
reciprocal normalization. The reciprocal parameter belongs to every center. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryCenters
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityPolynomialAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul

/-- The reciprocal base coordinate as an actual element of the normalization. -/
def infinityParameter : InfinityNormalization :=
  algebraMap BasePolynomial InfinityNormalization Polynomial.X

theorem infinityParameter_ne_zero : infinityParameter ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R := ZMod 2)
  apply infinityBaseToField_injective
  have hh := congrArg (fun a : InfinityNormalization => (a : CurveField)) h
  change infinityBaseToField Polynomial.X = 0 at hh
  exact hh.trans infinityBaseToField.map_zero.symm


variable {R : Type*} [CommRing R] [IsLocalRing R]

def boundaryCenter (f : InfinityNormalization →+* R) : Ideal InfinityNormalization :=
  (IsLocalRing.maximalIdeal R).comap f

instance boundaryCenter_isPrime (f : InfinityNormalization →+* R) :
    (boundaryCenter f).IsPrime :=
  inferInstanceAs ((IsLocalRing.maximalIdeal R).comap f).IsPrime

omit [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W] in
theorem infinityParameter_mem_boundaryCenter (f : InfinityNormalization →+* R)
    (ho : Ring.ord R (f infinityParameter) ≠ 0) : infinityParameter ∈ boundaryCenter f := by
  change f infinityParameter ∈ IsLocalRing.maximalIdeal R
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact ho (Ring.ord_of_isUnit hu)

theorem boundaryCenter_ne_bot (f : InfinityNormalization →+* R)
    (ho : Ring.ord R (f infinityParameter) ≠ 0) : boundaryCenter f ≠ ⊥ := by
  intro h
  have hm := infinityParameter_mem_boundaryCenter f ho
  rw [h, Ideal.mem_bot] at hm
  exact infinityParameter_ne_zero hm

theorem boundaryCenter_isMaximal (f : InfinityNormalization →+* R)
    (ho : Ring.ord R (f infinityParameter) ≠ 0) : (boundaryCenter f).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (boundaryCenter_ne_bot f ho)

#print axioms infinityParameter
#print axioms infinityParameter_ne_zero
#print axioms boundaryCenter
#print axioms boundaryCenter_isPrime
#print axioms infinityParameter_mem_boundaryCenter
#print axioms boundaryCenter_ne_bot
#print axioms boundaryCenter_isMaximal
end MazurProof.N25F_InfinityBoundaryCenters
