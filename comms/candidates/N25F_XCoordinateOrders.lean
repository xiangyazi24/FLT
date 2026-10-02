import FLT.Assumptions.MazurProof.N25F_XBoundaryOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.NormNum

/-! Orders of the actual Y/X and Z/X germs at the X-boundary point,
derived from the defining quadric and cubic and the known W/X order. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XCoordinateOrders

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoConormal
open N25F_XLocalDVR

private theorem coordinate_orders
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (y z w u v : R) (hwne : w ≠ 0)
    (hy : ¬ IsUnit y) (hz : ¬ IsUnit z) (hu : IsUnit u) (hv : IsUnit v)
    (hw : Ring.ord R w = 3)
    (hc : y * z = -(w * u)) (hq : z * v = -(w + y ^ 2)) :
    Ring.ord R y = 1 ∧ Ring.ord R z = 2 := by
  have hp : y * z ≠ 0 := by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero hwne hu.ne_zero)
  have hyne : y ≠ 0 := left_ne_zero_of_mul hp
  have hzne : z ≠ 0 := right_ne_zero_of_mul hp
  have hs : Ring.ord R y + Ring.ord R z = 3 := by
    rw [← Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hzne), hc,
      Ring.ord_neg, Ring.ord_mul_of_isUnit_right hu, hw]
  have hqord : Ring.ord R (w + y ^ 2) = Ring.ord R z := by
    rw [← Ring.ord_neg (w + y ^ 2), ← hq, Ring.ord_mul_of_isUnit_right hv]
  have hi := Ring.ord_add w (y ^ 2)
  rw [hqord, hw, Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hyne)] at hi
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := R) (mem_nonZeroDivisors_iff_ne_zero.mpr hyne))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := R) (mem_nonZeroDivisors_iff_ne_zero.mpr hzne))
  have hnpos : n ≠ 0 := by
    intro hnzero
    apply hy
    apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
    rw [← Ring.ord_eq_addVal, ← hn, hnzero]
    rfl
  have hmpos : m ≠ 0 := by
    intro hmzero
    apply hz
    apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
    rw [← Ring.ord_eq_addVal, ← hm, hmzero]
    rfl
  rw [← hn, ← hm] at hs hi ⊢
  have hsum : n + m = 3 := by exact_mod_cast hs
  have hmin : min 3 (2 * n) ≤ m := by
    simp only [nsmul_eq_mul, ← Nat.cast_mul] at hi
    rcases min_le_iff.mp hi with h | h
    · exact (min_le_left _ _).trans (by exact_mod_cast h)
    · exact (min_le_right _ _).trans (by exact_mod_cast h)
  have hn1 : n = 1 := by omega
  have hm2 : m = 2 := by omega
  simp [hn1, hm2]

/-- The actual germ Y/X at the X-boundary point. -/
def xYGerm : XLocalRing := algebraMap XChartRing XLocalRing xY

/-- The actual germ Z/X at the X-boundary point. -/
def xZGerm : XLocalRing := algebraMap XChartRing XLocalRing xZ

private def cubicFactor : XChartRing :=
  1 + xY + xZ + xY * xZ + xZ ^ 2 + xZ * xW

private def quadricFactor : XChartRing := 1 + xY + xW

private theorem x_quadric_relation : xZ + xW + xY ^ 2 + xY * xZ + xZ * xW = 0 := by
  have h := chartQuotientPoint_quadric (0 : Fin 4)
  simpa [canonicalQuadric25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

private theorem x_cubic_relation :
    xW + xY * xZ + xY * xW + xZ * xW + xY * xZ * xW +
      xZ ^ 2 * xW + xZ * xW ^ 2 = 0 := by
  have h := chartQuotientPoint_cubic (0 : Fin 4)
  simpa [canonicalCubic25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

private theorem germ_isUnit_of_eval_one (a : XChartRing) (ha : xChartEval a = 1) :
    IsUnit (algebraMap XChartRing XLocalRing a) := by
  apply IsLocalization.map_units XLocalRing (⟨a, ?_⟩ : xPrime.primeCompl)
  apply Ideal.mem_primeCompl_iff.mpr
  intro hp
  have hzero : xChartEval a = 0 := RingHom.mem_ker.mp hp
  rw [ha] at hzero
  exact one_ne_zero hzero

private theorem xYGerm_not_isUnit : ¬ IsUnit xYGerm := by
  intro hu
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff XLocalRing xPrime xY).mp hu
  exact (Ideal.mem_primeCompl_iff.mp h) (RingHom.mem_ker.mpr xChartEval_xY)

private theorem xZGerm_not_isUnit : ¬ IsUnit xZGerm := by
  intro hu
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff XLocalRing xPrime xZ).mp hu
  exact (Ideal.mem_primeCompl_iff.mp h) (RingHom.mem_ker.mpr xChartEval_xZ)

private theorem xCoordinateGermOrders :
    Ring.ord XLocalRing xYGerm = 1 ∧ Ring.ord XLocalRing xZGerm = 2 := by
  apply coordinate_orders xYGerm xZGerm xWGerm
    (algebraMap XChartRing XLocalRing cubicFactor)
    (algebraMap XChartRing XLocalRing quadricFactor)
    xWGerm_ne_zero xYGerm_not_isUnit xZGerm_not_isUnit
  · exact germ_isUnit_of_eval_one cubicFactor (by simp [cubicFactor])
  · exact germ_isUnit_of_eval_one quadricFactor (by simp [quadricFactor])
  · exact xWGerm_ord_eq_three
  · have hc : xY * xZ = -(xW * cubicFactor) := by
      apply eq_neg_of_add_eq_zero_left
      dsimp [cubicFactor]
      linear_combination x_cubic_relation
    simpa only [xYGerm, xZGerm, xWGerm, map_mul, map_neg] using congrArg (algebraMap XChartRing XLocalRing) hc
  · have hq : xZ * quadricFactor = -(xW + xY ^ 2) := by
      apply eq_neg_of_add_eq_zero_left
      dsimp [quadricFactor]
      linear_combination x_quadric_relation
    simpa only [xYGerm, xZGerm, xWGerm, map_mul, map_neg, map_add, map_pow] using
      congrArg (algebraMap XChartRing XLocalRing) hq

/-- The actual Y/X germ is a uniformizing function at [1:0:0:0]. -/
theorem xYGerm_ord_eq_one : Ring.ord XLocalRing xYGerm = 1 :=
  xCoordinateGermOrders.1

/-- The actual Z/X germ vanishes to order two at [1:0:0:0]. -/
theorem xZGerm_ord_eq_two : Ring.ord XLocalRing xZGerm = 2 :=
  xCoordinateGermOrders.2

end MazurProof.N25F_XCoordinateOrders
