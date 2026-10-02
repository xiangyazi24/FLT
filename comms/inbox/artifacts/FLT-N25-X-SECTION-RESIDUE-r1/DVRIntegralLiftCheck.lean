import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Recovering genuine local elements and residue vanishing from the signed
order of fractions. Zero is handled explicitly because WithZero.log 0 = 0. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_DVRIntegralLift

/-- Every zero or nonnegative-order fraction has a unique actual DVR germ. -/
theorem existsUnique_algebraMap_eq_of_log_nonneg {R L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (f : L) (hf : f = 0 ∨ 0 ≤ WithZero.log (Ring.ordFrac R f)) :
    ∃! a : R, algebraMap R L a = f := by
  have hex : ∃ a : R, algebraMap R L a = f := by
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [map_zero, hf0]⟩
    have hv : Ring.ordFrac R f ≠ 0 :=
      ((isUnit_iff_ne_zero.mpr hf0).map (Ring.ordFrac R)).ne_zero
    have hlog : 0 ≤ WithZero.log (Ring.ordFrac R f) := hf.resolve_left hf0
    have horder : 1 ≤ Ring.ordFrac R f :=
      (WithZero.log_le_log one_ne_zero hv).mp (by simpa only [WithZero.log_one] using hlog)
    apply IsDiscreteValuationRing.exists_lift_of_le_one
    have he : (IsDiscreteValuationRing.maximalIdeal R).valuation L f =
        (Ring.ordFrac R f)⁻¹ := by rw [Ring.ordFrac_eq_valuation_inv, inv_inv]
    rw [he]
    exact inv_le_one_of_one_le₀ horder
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, fun b hb => IsFractionRing.injective R L (hb.trans ha.symm)⟩

/-- Residue vanishes exactly at the zero germ or at strictly positive order. -/
theorem residue_eq_zero_iff_eq_zero_or_log_pos {R L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra R L] [IsFractionRing R L] (a : R) :
    IsLocalRing.residue R a = 0 ↔
      a = 0 ∨ 0 < WithZero.log (Ring.ordFrac R (algebraMap R L a)) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  by_cases ha : a = 0
  · simp [ha]
  constructor
  · intro hnot
    right
    have hmap : algebraMap R L a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha
    have hv0 : Ring.ordFrac R (algebraMap R L a) ≠ 0 :=
      ((isUnit_iff_ne_zero.mpr hmap).map (Ring.ordFrac R)).ne_zero
    have hv1 : Ring.ordFrac R (algebraMap R L a) ≠ 1 :=
      fun h => hnot (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h)
    have hp : 1 < Ring.ordFrac R (algebraMap R L a) :=
      lt_of_le_of_ne (Ring.ordFrac_ge_one_of_ne_zero ha) (Ne.symm hv1)
    simpa only [WithZero.log_one] using (WithZero.log_lt_log one_ne_zero hv0).mpr hp
  · intro hp hu
    have hpos := hp.resolve_left ha
    rw [Ring.ordFrac_of_isUnit hu, WithZero.log_one] at hpos
    exact (lt_irrefl (0 : ℤ)) hpos

end MazurProof.N25F_DVRIntegralLift

#print axioms MazurProof.N25F_DVRIntegralLift.existsUnique_algebraMap_eq_of_log_nonneg
#print axioms MazurProof.N25F_DVRIntegralLift.residue_eq_zero_iff_eq_zero_or_log_pos
