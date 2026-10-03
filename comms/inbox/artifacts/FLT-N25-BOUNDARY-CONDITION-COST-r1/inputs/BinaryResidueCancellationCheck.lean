import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-! A nonconstant unit in a DVR with binary residue field becomes strictly
positive in order after subtracting one, on its actual fraction field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_BinaryResidueOrder

private theorem binary_ne_zero_eq_one (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  have hv := ZMod.val_lt a
  have hz : a.val ≠ 0 := by
    intro h
    apply ha
    apply ZMod.val_injective 2
    simpa using h
  have h : a.val = 1 := by omega
  apply ZMod.val_injective 2
  simpa only [ZMod.val_one_eq_one_mod] using h

/-- A fraction of order zero has a unit representative. Over a binary
residue field its difference from one has positive order unless it is zero. -/
theorem log_ordFrac_sub_one_pos {R L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (e : IsLocalRing.ResidueField R ≃+* ZMod 2) (f : L)
    (hf : f ≠ 1) (hord : Ring.ordFrac R f = 1) :
    0 < WithZero.log (Ring.ordFrac R (f - 1)) := by
  have hm : f ∈ (IsUnit.submonoid R).map (algebraMap R L) := by
    rw [← Ring.mker_ordFrac_eq_isUnitSubmonoid (R := R) (K := L)]
    exact hord
  obtain ⟨a, ha, rfl⟩ := hm
  change IsUnit a at ha
  have hv : e (IsLocalRing.residue R a) ≠ 0 :=
    ((ha.map (IsLocalRing.residue R)).map e.toMonoidHom).ne_zero
  have hr : IsLocalRing.residue R a = 1 := by
    apply e.injective
    simpa only [map_one] using binary_ne_zero_eq_one _ hv
  have hres : IsLocalRing.residue R (a - 1) = 0 := by
    rw [map_sub, map_one, hr, sub_self]
  have hnot : ¬ IsUnit (a - 1) :=
    (IsLocalRing.mem_maximalIdeal (a - 1)).mp ((IsLocalRing.residue_eq_zero_iff _).mp hres)
  have ha1 : a ≠ 1 := by
    intro h
    subst a
    exact hf (map_one _)
  have has : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hs : algebraMap R L (a - 1) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr has
  have hv0 : Ring.ordFrac R (algebraMap R L (a - 1)) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hs).map (Ring.ordFrac R)).ne_zero
  have hv1 : Ring.ordFrac R (algebraMap R L (a - 1)) ≠ 1 := by
    intro h
    exact hnot (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h)
  have hpos : 1 < Ring.ordFrac R (algebraMap R L (a - 1)) :=
    lt_of_le_of_ne (Ring.ordFrac_ge_one_of_ne_zero has) (Ne.symm hv1)
  have hlog : 0 < WithZero.log (Ring.ordFrac R (algebraMap R L (a - 1))) := by
    simpa only [WithZero.log_one] using
      (WithZero.log_lt_log (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 from one_ne_zero) hv0).mpr hpos
  simpa only [map_sub, map_one] using hlog

end MazurProof.N25F_BinaryResidueOrder

/-! Equal-order leading terms cancel strictly over the actual binary residue field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_BinaryResidueCancellation
open N25F_BinaryResidueOrder

/-- Two distinct nonzero fractions of equal order have a difference of
strictly higher order when the genuine residue field is F2. -/
theorem log_ordFrac_sub_gt_of_log_eq {R L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (e : IsLocalRing.ResidueField R ≃+* ZMod 2) (f g : L)
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f ≠ g)
    (hord : WithZero.log (Ring.ordFrac R f) = WithZero.log (Ring.ordFrac R g)) :
    WithZero.log (Ring.ordFrac R g) < WithZero.log (Ring.ordFrac R (f - g)) := by
  have hvf : Ring.ordFrac R f ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hf).map (Ring.ordFrac R)).ne_zero
  have hvg : Ring.ordFrac R g ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hg).map (Ring.ordFrac R)).ne_zero
  have hsame : Ring.ordFrac R f = Ring.ordFrac R g := by
    rw [← WithZero.exp_log hvf, ← WithZero.exp_log hvg, hord]
  have hquot : Ring.ordFrac R (f / g) = 1 := by
    rw [map_div₀, hsame, div_self hvg]
  have hq1 : f / g ≠ 1 := by
    intro h
    exact hfg ((div_eq_one_iff_eq hg).mp h)
  have hpos := log_ordFrac_sub_one_pos e (f / g) hq1 hquot
  have hq0 : Ring.ordFrac R (f / g - 1) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hq1)).map (Ring.ordFrac R)).ne_zero
  have heq : (f / g - 1) * g = f - g := by
    rw [sub_mul, div_mul_cancel₀ _ hg, one_mul]
  have he := congrArg (fun a : L => WithZero.log (Ring.ordFrac R a)) heq
  rw [map_mul, WithZero.log_mul hq0 hvg] at he
  omega

end MazurProof.N25F_BinaryResidueCancellation

#print axioms MazurProof.N25F_BinaryResidueCancellation.log_ordFrac_sub_gt_of_log_eq
