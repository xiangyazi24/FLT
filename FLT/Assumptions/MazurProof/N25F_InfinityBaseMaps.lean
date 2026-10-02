import FLT.Assumptions.MazurProof.N25F_XInfinityGerm
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalDivisor
import Mathlib.RingTheory.Algebraic.Basic

/-! The reciprocal polynomial base F₂[1/qz] maps into all three actual
boundary local rings, compatibly with the fixed common function field.
These are explicit maps, not competing global algebra instances. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityBaseMaps

private theorem inverse_aeval_injective
    {k L : Type*} [Field k] [Field L] [Algebra k L] (z : L)
    (hz : Function.Injective (Polynomial.aeval z : Polynomial k →ₐ[k] L)) :
    Function.Injective (Polynomial.aeval (1 / z) : Polynomial k →ₐ[k] L) := by
  apply transcendental_iff_injective.mp
  have ht : Transcendental k z := transcendental_iff_injective.mpr hz
  simpa only [one_div, Transcendental, IsAlgebraic.inv_iff] using ht

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XInfinityGerm N25F_XLocalFractionEmbedding
open N25F_YZLocalZUnit N25F_YZOverlapMap N25F_YZLocalDVR
open N25F_YZLocalFractionEmbedding N25F_ZBoundaryOrder
open N25F_ZChartFractionMap N25F_ProjectivePrincipalDivisor
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

/-- At YZ, W/Z is W/Y multiplied by the inverse of the existing unit Z/Y. -/
def yzInverseZGerm : YZLocalRing := yzWGerm * (↑yzZUnit⁻¹ : YZLocalRing)

@[simp]
theorem yzLocalToFraction_yzInverseZGerm :
    yzLocalToFraction yzInverseZGerm = 1 / algebraMap W K qz := by
  rw [yzInverseZGerm, map_mul, map_units_inv, yzZUnit_val,
    yzLocalToFraction_yzWGerm, yzLocalToFraction_yzZGerm,
    inv_div, one_div, ← mul_div_assoc, inv_mul_cancel₀ fraction_qy_ne_zero]

theorem yzInverseZGerm_ne_zero : yzInverseZGerm ≠ 0 :=
  mul_ne_zero yzWGerm_ne_zero (Units.isUnit (yzZUnit⁻¹)).ne_zero

theorem yzInverseZGerm_ord_eq_one : Ring.ord YZLocalRing yzInverseZGerm = 1 := by
  rw [yzInverseZGerm, Ring.ord_mul_of_isUnit_right (Units.isUnit (yzZUnit⁻¹)),
    yzWGerm_ord_eq_one]

/-- The actual infinity-base coordinate sends its variable to 1/qz. -/
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

/-- The actual reciprocal base maps to the X-boundary local ring. -/
def infinityBaseToX : Polynomial (ZMod 2) →ₐ[ZMod 2] XLocalRing :=
  Polynomial.aeval xInverseZGerm

/-- The actual reciprocal base maps to the YZ-boundary local ring. -/
def infinityBaseToYZ : Polynomial (ZMod 2) →ₐ[ZMod 2] YZLocalRing :=
  Polynomial.aeval yzInverseZGerm

/-- The actual reciprocal base maps to the Z-boundary local ring. -/
def infinityBaseToZ : Polynomial (ZMod 2) →ₐ[ZMod 2] ZLocalRing :=
  Polynomial.aeval zWGerm

@[simp]
theorem xLocalToFraction_comp_infinityBase :
    xLocalToFraction.comp infinityBaseToX = infinityBaseToField := by
  rw [infinityBaseToX, infinityBaseToField, ← Polynomial.aeval_algHom,
    xLocalToFraction_xInverseZGerm]

@[simp]
theorem yzLocalToFraction_comp_infinityBase :
    yzLocalToFraction.comp infinityBaseToYZ = infinityBaseToField := by
  rw [infinityBaseToYZ, infinityBaseToField, ← Polynomial.aeval_algHom,
    yzLocalToFraction_yzInverseZGerm]

@[simp]
theorem zLocalToFraction_comp_infinityBase :
    zLocalToFraction.comp infinityBaseToZ = infinityBaseToField := by
  rw [infinityBaseToZ, infinityBaseToField, ← Polynomial.aeval_algHom,
    zLocalToFraction_zWGerm]

theorem infinityBaseToX_injective : Function.Injective infinityBaseToX := by
  intro p q h
  apply infinityBaseToField_injective
  have hh := congrArg xLocalToFraction h
  change (xLocalToFraction.comp infinityBaseToX) p =
    (xLocalToFraction.comp infinityBaseToX) q at hh
  simpa only [xLocalToFraction_comp_infinityBase] using hh

theorem infinityBaseToYZ_injective : Function.Injective infinityBaseToYZ := by
  intro p q h
  apply infinityBaseToField_injective
  have hh := congrArg yzLocalToFraction h
  change (yzLocalToFraction.comp infinityBaseToYZ) p =
    (yzLocalToFraction.comp infinityBaseToYZ) q at hh
  simpa only [yzLocalToFraction_comp_infinityBase] using hh

theorem infinityBaseToZ_injective : Function.Injective infinityBaseToZ := by
  intro p q h
  apply infinityBaseToField_injective
  have hh := congrArg zLocalToFraction h
  change (zLocalToFraction.comp infinityBaseToZ) p =
    (zLocalToFraction.comp infinityBaseToZ) q at hh
  simpa only [zLocalToFraction_comp_infinityBase] using hh

end MazurProof.N25F_InfinityBaseMaps
