import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.NormNum
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25XCoordinateOrdersCheck

theorem coordinate_orders
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

#print axioms coordinate_orders
end N25XCoordinateOrdersCheck
