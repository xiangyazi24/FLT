import FLT.Assumptions.MazurProof.N25F_BinaryResidueOrder

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
