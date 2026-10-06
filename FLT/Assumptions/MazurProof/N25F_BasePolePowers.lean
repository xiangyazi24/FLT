import FLT.Assumptions.MazurProof.N25F_WBasisPoleSections
import FLT.Assumptions.MazurProof.N25F_SectionMultiplication
import FLT.Assumptions.MazurProof.N25F_ZeroDegreeConstants

/-! Actual powers of Z/W belong to the expected full bounded-pole spaces. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_BasePolePowers
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_RiemannRochSpace N25F_WBasisPoleSections N25F_SectionMultiplication
open N25F_XBoundaryOrder N25F_XBoundaryZOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap N25F_ZeroDegreeConstants
local notation "K" => FractionRing W

theorem basePoleDivisor25Two_nonneg : 0 ≤ basePoleDivisor25Two := by
  exact add_nonneg
    (add_nonneg (Finsupp.single_nonneg.mpr (by decide))
      (Finsupp.single_nonneg.mpr (by decide)))
    (Finsupp.single_nonneg.mpr (by decide))

theorem qz_mem_basePole_section_space :
    algebraMap W K qz ∈ fullRiemannRochSpace25Two basePoleDivisor25Two := by
  have hq : qz ≠ 0 := by
    intro h
    exact fraction_qz_ne_zero (by rw [h, map_zero])
  have h := regular_function_mem_basePole_space 1 qz hq
      (Additive.ofMul (Units.mk0 (algebraMap W K qz) fraction_qz_ne_zero)) rfl
      (le_of_eq xBoundaryOrder_qz.symm) (le_of_eq yzBoundaryOrder_qz.symm)
      (le_of_eq zBoundaryOrder_qz.symm)
  change algebraMap W K qz ∈ fullRiemannRochSpace25Two ((1 : ℤ) • basePoleDivisor25Two) at h
  simpa only [one_smul] using h

/-- Powers of the actual base coordinate have poles bounded by nH. -/
theorem qz_pow_mem_basePole_section_space (n : ℕ) :
    (algebraMap W K qz) ^ n ∈
      fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_smul] using one_mem_fullRiemannRochSpace25Two_zero
  | succ n ih =>
      have h := mul_mem_fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)
        basePoleDivisor25Two ((algebraMap W K qz) ^ n) (algebraMap W K qz)
        ih qz_mem_basePole_section_space
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_smul, one_smul] using h

end MazurProof.N25F_BasePolePowers
