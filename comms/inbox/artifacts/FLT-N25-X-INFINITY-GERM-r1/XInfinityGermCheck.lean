import XBoundaryZOrderCheck

/-! The actual X-local representative of the reciprocal base parameter W/Z.
It is constructed by DVR divisibility, not by dividing in the local ring
or postulating a rational-function germ. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XInfinityGerm

open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XCoordinateOrders N25F_XLocalFractionEmbedding
open N25F_XBoundaryZOrder N25F_XChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [IsDedekindDomain W]
variable (hord : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)


include hord in
/-- In the actual X-boundary DVR, Z/X divides W/X because 2 ≤ 3. -/
theorem xZGerm_dvd_xWGerm : xZGerm ∣ xWGerm := by
  apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
  rw [← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal,
    xZGerm_ord_eq_two hord, hord]
  norm_num

/-- The actual local element W/Z, selected from the proved divisibility. -/
def xInverseZGerm : XLocalRing := Classical.choose (xZGerm_dvd_xWGerm hord)

@[simp]
theorem xZGerm_mul_xInverseZGerm : xZGerm * (xInverseZGerm hord) = xWGerm :=
  (Classical.choose_spec (xZGerm_dvd_xWGerm hord)).symm

include fraction_qz_ne_zero in
/-- The constructed germ has the required coordinate-rigid common-field image. -/
@[simp]
theorem xLocalToFraction_xInverseZGerm :
    xLocalToFraction (xInverseZGerm hord) = 1 / algebraMap W K qz := by
  have hzne : xLocalToFraction xZGerm ≠ 0 :=
    (map_ne_zero_iff _ xLocalToFraction_injective).mpr (xZGerm_ne_zero fraction_qz_ne_zero)
  have hratio : xLocalToFraction (xInverseZGerm hord) =
      xLocalToFraction xWGerm / xLocalToFraction xZGerm := by
    apply (eq_div_iff hzne).mpr
    rw [mul_comm, ← map_mul, (xZGerm_mul_xInverseZGerm hord)]
  rw [hratio, xLocalToFraction_xWGerm, xLocalToFraction_xZGerm,
    div_div_eq_mul_div, one_div, inv_mul_cancel₀ fraction_qx_ne_zero]

include fraction_qz_ne_zero in
/-- The reciprocal base-parameter germ is nonzero. -/
theorem xInverseZGerm_ne_zero : (xInverseZGerm hord) ≠ 0 := by
  intro hzero
  have h := congrArg xLocalToFraction hzero
  rw [xLocalToFraction_xInverseZGerm hord fraction_qz_ne_zero, map_zero] at h
  exact (one_div_ne_zero fraction_qz_ne_zero) h

include fraction_qz_ne_zero in
/-- The actual reciprocal base parameter has simple zero at the X boundary. -/
theorem xInverseZGerm_ord_eq_one : Ring.ord XLocalRing (xInverseZGerm hord) = 1 := by
  have h := congrArg (Ring.ord XLocalRing) (xZGerm_mul_xInverseZGerm hord)
  rw [Ring.ord_mul XLocalRing (mem_nonZeroDivisors_iff_ne_zero.mpr (xInverseZGerm_ne_zero hord fraction_qz_ne_zero)),
    xZGerm_ord_eq_two hord, hord] at h
  apply ENat.add_right_injective_of_ne_top (n := 2) (by simp)
  exact h

#check @xInverseZGerm_ord_eq_one
#print axioms xZGerm_dvd_xWGerm
#print axioms xInverseZGerm
#print axioms xZGerm_mul_xInverseZGerm
#print axioms xLocalToFraction_xInverseZGerm
#print axioms xInverseZGerm_ne_zero
#print axioms xInverseZGerm_ord_eq_one
end MazurProof.N25F_XInfinityGerm
