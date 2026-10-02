import FLT.Assumptions.MazurProof.N25F_XBoundaryZOrder

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
open N25F_XBoundaryZOrder N25F_XChartFractionMap N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

/-- In the actual X-boundary DVR, Z/X divides W/X because 2 ≤ 3. -/
theorem xZGerm_dvd_xWGerm : xZGerm ∣ xWGerm := by
  apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
  rw [← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal,
    xZGerm_ord_eq_two, xWGerm_ord_eq_three]
  norm_num

/-- The actual local element W/Z, selected from the proved divisibility. -/
def xInverseZGerm : XLocalRing := Classical.choose xZGerm_dvd_xWGerm

@[simp]
theorem xZGerm_mul_xInverseZGerm : xZGerm * xInverseZGerm = xWGerm :=
  (Classical.choose_spec xZGerm_dvd_xWGerm).symm

/-- The constructed germ has the required coordinate-rigid common-field image. -/
@[simp]
theorem xLocalToFraction_xInverseZGerm :
    xLocalToFraction xInverseZGerm = 1 / algebraMap W K qz := by
  have hzne : xLocalToFraction xZGerm ≠ 0 :=
    (map_ne_zero_iff _ xLocalToFraction_injective).mpr xZGerm_ne_zero
  have hratio : xLocalToFraction xInverseZGerm =
      xLocalToFraction xWGerm / xLocalToFraction xZGerm := by
    apply (eq_div_iff hzne).mpr
    rw [mul_comm, ← map_mul, xZGerm_mul_xInverseZGerm]
  rw [hratio, xLocalToFraction_xWGerm, xLocalToFraction_xZGerm,
    div_div_eq_mul_div, one_div, inv_mul_cancel₀ fraction_qx_ne_zero]

/-- The reciprocal base-parameter germ is nonzero. -/
theorem xInverseZGerm_ne_zero : xInverseZGerm ≠ 0 := by
  intro hzero
  have h := congrArg xLocalToFraction hzero
  rw [xLocalToFraction_xInverseZGerm, map_zero] at h
  exact (one_div_ne_zero fraction_qz_ne_zero) h

/-- The actual reciprocal base parameter has simple zero at the X boundary. -/
theorem xInverseZGerm_ord_eq_one : Ring.ord XLocalRing xInverseZGerm = 1 := by
  have h := congrArg (Ring.ord XLocalRing) xZGerm_mul_xInverseZGerm
  rw [Ring.ord_mul XLocalRing (mem_nonZeroDivisors_iff_ne_zero.mpr xInverseZGerm_ne_zero),
    xZGerm_ord_eq_two, xWGerm_ord_eq_three] at h
  apply ENat.add_right_injective_of_ne_top (n := 2) (by simp)
  exact h

end MazurProof.N25F_XInfinityGerm
