import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryMaps

/-! The three actual boundary rings determine nonzero prime centers on the
reciprocal normalization. The reciprocal parameter belongs to every center. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBoundaryCenters
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XInfinityGerm
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
attribute [local instance] infinityPolynomialAlgebra
local instance : Module BasePolynomial CurveField :=
  @Algebra.toModule BasePolynomial CurveField _ _ infinityPolynomialAlgebra
local instance : SMul BasePolynomial CurveField := infinityPolynomialAlgebra.toSMul
local instance : Algebra BasePolynomial XLocalRing :=
  infinityBaseToX.toRingHom.toAlgebra
local instance : Algebra BasePolynomial YZLocalRing :=
  infinityBaseToYZ.toRingHom.toAlgebra
local instance : Algebra BasePolynomial ZLocalRing :=
  infinityBaseToZ.toRingHom.toAlgebra

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

/-- The actual center of the X boundary on the reciprocal normalization. -/
def xInfinityPrime : Ideal InfinityNormalization :=
  (IsLocalRing.maximalIdeal XLocalRing).comap infinityNormalizationToX.toRingHom

instance xInfinityPrime_isPrime : xInfinityPrime.IsPrime :=
  inferInstanceAs ((IsLocalRing.maximalIdeal XLocalRing).comap
    infinityNormalizationToX.toRingHom).IsPrime

theorem infinityParameter_mem_xInfinityPrime : infinityParameter ∈ xInfinityPrime := by
  change infinityNormalizationToX infinityParameter ∈ IsLocalRing.maximalIdeal XLocalRing
  have hmap : infinityNormalizationToX infinityParameter = xInverseZGerm := by
    change infinityNormalizationToX
      (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = xInverseZGerm
    rw [infinityNormalizationToX.commutes]
    exact Polynomial.aeval_X _
  rw [hmap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have ho := Ring.ord_of_isUnit hu
  rw [xInverseZGerm_ord_eq_one] at ho
  norm_num at ho

theorem xInfinityPrime_ne_bot : xInfinityPrime ≠ ⊥ := by
  intro h
  have hm := infinityParameter_mem_xInfinityPrime
  rw [h, Ideal.mem_bot] at hm
  exact infinityParameter_ne_zero hm

instance xInfinityPrime_isMaximal : xInfinityPrime.IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance xInfinityPrime_ne_bot

/-- The actual center of the YZ boundary on the reciprocal normalization. -/
def yzInfinityPrime : Ideal InfinityNormalization :=
  (IsLocalRing.maximalIdeal YZLocalRing).comap infinityNormalizationToYZ.toRingHom

instance yzInfinityPrime_isPrime : yzInfinityPrime.IsPrime :=
  inferInstanceAs ((IsLocalRing.maximalIdeal YZLocalRing).comap
    infinityNormalizationToYZ.toRingHom).IsPrime

theorem infinityParameter_mem_yzInfinityPrime : infinityParameter ∈ yzInfinityPrime := by
  change infinityNormalizationToYZ infinityParameter ∈ IsLocalRing.maximalIdeal YZLocalRing
  have hmap : infinityNormalizationToYZ infinityParameter = yzInverseZGerm := by
    change infinityNormalizationToYZ
      (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = yzInverseZGerm
    rw [infinityNormalizationToYZ.commutes]
    exact Polynomial.aeval_X _
  rw [hmap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have ho := Ring.ord_of_isUnit hu
  rw [yzInverseZGerm_ord_eq_one] at ho
  norm_num at ho

theorem yzInfinityPrime_ne_bot : yzInfinityPrime ≠ ⊥ := by
  intro h
  have hm := infinityParameter_mem_yzInfinityPrime
  rw [h, Ideal.mem_bot] at hm
  exact infinityParameter_ne_zero hm

instance yzInfinityPrime_isMaximal : yzInfinityPrime.IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance yzInfinityPrime_ne_bot

/-- The actual center of the Z boundary on the reciprocal normalization. -/
def zInfinityPrime : Ideal InfinityNormalization :=
  (IsLocalRing.maximalIdeal ZLocalRing).comap infinityNormalizationToZ.toRingHom

instance zInfinityPrime_isPrime : zInfinityPrime.IsPrime :=
  inferInstanceAs ((IsLocalRing.maximalIdeal ZLocalRing).comap
    infinityNormalizationToZ.toRingHom).IsPrime

theorem infinityParameter_mem_zInfinityPrime : infinityParameter ∈ zInfinityPrime := by
  change infinityNormalizationToZ infinityParameter ∈ IsLocalRing.maximalIdeal ZLocalRing
  have hmap : infinityNormalizationToZ infinityParameter = zWGerm := by
    change infinityNormalizationToZ
      (algebraMap BasePolynomial InfinityNormalization Polynomial.X) = zWGerm
    rw [infinityNormalizationToZ.commutes]
    exact Polynomial.aeval_X _
  rw [hmap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have ho := Ring.ord_of_isUnit hu
  rw [zWGerm_ord_eq_two] at ho
  norm_num at ho

theorem zInfinityPrime_ne_bot : zInfinityPrime ≠ ⊥ := by
  intro h
  have hm := infinityParameter_mem_zInfinityPrime
  rw [h, Ideal.mem_bot] at hm
  exact infinityParameter_ne_zero hm

instance zInfinityPrime_isMaximal : zInfinityPrime.IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance zInfinityPrime_ne_bot

end MazurProof.N25F_InfinityBoundaryCenters
