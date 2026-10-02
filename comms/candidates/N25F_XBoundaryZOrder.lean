import FLT.Assumptions.MazurProof.N25F_XCoordinateOrders
import FLT.Assumptions.MazurProof.N25F_ZChartFractionMap

/-! The affine function Z/W has pole order one at the actual X-boundary point. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XBoundaryZOrder

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XLocalDVR N25F_XLocalFractionEmbedding N25F_XChartFractionMap
open N25F_XCoordinateOrders N25F_XBoundaryOrder N25F_ZChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

@[simp]
theorem xLocalToFraction_xZGerm :
    xLocalToFraction xZGerm = algebraMap W K qz / algebraMap W K qx := by
  rw [xZGerm, xLocalToFraction_algebraMap, xChartToFraction_xZ]

theorem xZGerm_ne_zero : xZGerm ≠ 0 := by
  intro hzero
  have h := congrArg xLocalToFraction hzero
  rw [xLocalToFraction_xZGerm, map_zero] at h
  exact (div_ne_zero fraction_qz_ne_zero fraction_qx_ne_zero) h

private theorem ordFrac_image_eq_exp
    {R L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field L] [Algebra R L] [IsFractionRing R L]
    (a : R) (ha : a ≠ 0) (n : ℕ) (hord : Ring.ord R a = n) :
    Ring.ordFrac R (algebraMap R L a) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

theorem xLocalFractionOrder_xZGerm :
    xLocalFractionOrder (xLocalToFraction xZGerm) = WithZero.exp (2 : ℤ) := by
  letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
  exact ordFrac_image_eq_exp (L := K) xZGerm xZGerm_ne_zero 2 xZGerm_ord_eq_two

/-- Z/W = (Z/X)/(W/X) has signed order 2 - 3 = -1 at [1:0:0:0]. -/
theorem xBoundaryOrder_qz :
    xBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W K qz) fraction_qz_ne_zero)) = -1 := by
  change WithZero.log (xLocalFractionOrder (algebraMap W K qz)) = -1
  have h : algebraMap W K qz = xLocalToFraction xZGerm / xLocalToFraction xWGerm := by
    rw [xLocalToFraction_xZGerm, xLocalToFraction_xWGerm, one_div, div_inv_eq_mul]
    exact (div_mul_cancel₀ _ fraction_qx_ne_zero).symm
  rw [h, map_div₀, xLocalFractionOrder_xZGerm, xLocalFractionOrder_xWGerm,
    WithZero.log_div (by simp) (by simp), WithZero.log_exp, WithZero.log_exp]
  norm_num

end MazurProof.N25F_XBoundaryZOrder
