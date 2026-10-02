import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors
structure ClosedPointGrading where
  Closed : ℕ → Type*
  finite_closed : ∀ d, Finite (Closed d)
  empty_degree_zero : IsEmpty (Closed 0)

namespace ClosedPointGrading
variable (C : ClosedPointGrading)
abbrev Atom := Σ d : ℕ, C.Closed d

/-- The residue degree of a graded closed point. -/
def atomDegree (x : C.Atom) : ℕ := x.1

abbrev Divisor := C.Atom →₀ ℤ

/-- The integer degree of a signed divisor is the sum of each multiplicity
times the residue degree of its closed point. -/
def divisorDegree : C.Divisor →+ ℤ where
  toFun D := D.sum fun x m => m * (C.atomDegree x : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    exact Finsupp.sum_add_index' (by simp) (by
      intro x a b
      simp only [add_mul])

end ClosedPointGrading
end MazurProof.CurveZetaEffectiveDivisors

namespace MazurProof.N25F_RiemannRochSpace
open CurveZetaEffectiveDivisors
private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h


variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
/-- The actual F2-vector space of zero and rational functions whose poles
are bounded by D, using every full closed-point coefficient. -/
def fullRiemannRochSpace25Two (D : C.Divisor) : Submodule (ZMod 2) L where
  carrier := {f | f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
    0 ≤ D A + principal (Additive.ofMul (Units.mk0 f hf)) A}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with hf | ⟨hf0, hf⟩
    · subst f
      simpa only [zero_add] using hg
    rcases hg with hg | ⟨hg0, hg⟩
    · subst g
      simp only [add_zero]
      exact Or.inr ⟨hf0, hf⟩
    by_cases hs : f + g = 0
    · exact Or.inl hs
    refine Or.inr ⟨hs, ?_⟩
    intro A
    have hm := hmin
      (Additive.ofMul (Units.mk0 f hf0)) (Additive.ofMul (Units.mk0 g hg0))
      (Additive.ofMul (Units.mk0 (f + g) hs)) rfl A
    have hfa := hf A
    have hga := hg A
    have hl : -D A ≤ min
        (principal (Additive.ofMul (Units.mk0 f hf0)) A)
        (principal (Additive.ofMul (Units.mk0 g hg0)) A) :=
      le_min (by omega) (by omega)
    have hfinal := hl.trans hm
    omega
  smul_mem' := by
    intro a f hf
    rcases zmod_two_cases a with rfl | rfl
    · simp only [zero_smul]
      exact Or.inl rfl
    · simpa only [one_smul] using hf

@[simp]
theorem mem_fullRiemannRochSpace25Two (D : C.Divisor) (f : L) :
    f ∈ fullRiemannRochSpace25Two C principal hmin D ↔ f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
      0 ≤ D A + principal (Additive.ofMul (Units.mk0 f hf)) A := Iff.rfl

include hzero in
/-- A nonzero bounded-pole function forces the bounding divisor's degree
to be nonnegative, by the genuine projective product formula. -/
theorem degree_nonneg_of_nonzero_mem (D : C.Divisor) (f : L)
    (hf : f ∈ fullRiemannRochSpace25Two C principal hmin D) (hne : f ≠ 0) :
    0 ≤ C.divisorDegree D := by
  rcases hf with hf | ⟨hf0, hb⟩
  · exact (hne hf).elim
  have hp := hzero (Additive.ofMul (Units.mk0 f hf0))
  have hd : 0 ≤ C.divisorDegree
      (D + principal (Additive.ofMul (Units.mk0 f hf0))) := by
    change 0 ≤ (D + principal (Additive.ofMul (Units.mk0 f hf0))).sum
      (fun A m => m * (C.atomDegree A : ℤ))
    apply Finsupp.sum_nonneg'
    intro A
    exact mul_nonneg (by simpa only [Finsupp.add_apply] using hb A) (Nat.cast_nonneg _)
  rw [map_add, hp, add_zero] at hd
  exact hd

include hzero in
/-- The actual Riemann--Roch space of a negative-degree full divisor is zero. -/
theorem fullRiemannRochSpace25Two_eq_bot_of_degree_neg (D : C.Divisor)
    (hD : C.divisorDegree D < 0) :
    fullRiemannRochSpace25Two C principal hmin D = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hne
  have hp := degree_nonneg_of_nonzero_mem C principal hmin hzero D f hf hne
  exact (not_le.mpr hD) hp


end MazurProof.N25F_RiemannRochSpace

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


namespace MazurProof.N25F_XSectionFiltration
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_BinaryResidueCancellation
variable {L : Type*} [Field L]
private theorem unit_mk0_eq (f : Additive Lˣ) (hf : (f.toMul : L) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : L) hf) = f := by
  apply Additive.toMul.injective
  exact Units.ext rfl


variable (C : ClosedPointGrading) [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
def boundaryOrder (f : Additive Lˣ) : ℤ := WithZero.log (Ring.ordFrac R (f.toMul : L))
variable (XPoint : C.Atom)
variable (hcoeff : ∀ f : Additive Lˣ, principal f XPoint = boundaryOrder R f)
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
/-- Removing the genuine X point gives a subspace of the original section space. -/
theorem fullRiemannRochSpace25Two_sub_X_le (D : C.Divisor) :
    fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ≤
      fullRiemannRochSpace25Two C principal hmin D := by
  classical
  intro a ha
  rcases ha with rfl | ⟨ha, hb⟩
  · exact (fullRiemannRochSpace25Two C principal hmin D).zero_mem
  refine Or.inr ⟨ha, ?_⟩
  intro A
  have h := hb A
  by_cases hA : A = XPoint
  · subst A
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same] at h
    omega
  · simpa [hA, Ne.symm hA] using h

include hcoeff in
/-- Membership in the next X filtration step is exactly strict improvement
of the allowed X order, once the other pole bounds already hold. -/
theorem mem_fullRiemannRochSpace25Two_sub_X_iff (D : C.Divisor)
    (f : Additive Lˣ) (hf : (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin D) :
    (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ↔
      -D XPoint < boundaryOrder R f := by
  classical
  have hb : ∀ A, 0 ≤ D A + principal f A := by
    rcases hf with h | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero h).elim
    simpa only [unit_mk0_eq f hf0] using hb
  constructor
  · intro hs
    rcases hs with h | ⟨hf0, hs⟩
    · exact (f.toMul.ne_zero h).elim
    have hx := hs XPoint
    rw [unit_mk0_eq f hf0, Finsupp.sub_apply, Finsupp.single_eq_same,
      hcoeff] at hx
    omega
  · intro hx
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = XPoint
    · subst A
      rw [Finsupp.sub_apply, Finsupp.single_eq_same, hcoeff]
      omega
    · simpa [hA, Ne.symm hA] using hb A

include hcoeff in
/-- A section outside the next step has exactly the extremal allowed X order. -/
theorem xBoundaryOrder_eq_neg_of_not_mem_sub_X (D : C.Divisor)
    (f : Additive Lˣ) (hf : (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hnot : (f.toMul : L) ∉
      fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)) :
    boundaryOrder R f = -D XPoint := by
  have hn := mt (mem_fullRiemannRochSpace25Two_sub_X_iff C principal hmin R XPoint hcoeff D f hf).mpr hnot
  rcases hf with h | ⟨hf0, hb⟩
  · exact (f.toMul.ne_zero h).elim
  have hx := hb XPoint
  rw [unit_mk0_eq f hf0, hcoeff] at hx
  omega

include hcoeff e in
/-- All sections outside L(D-X) have the same nonzero leading coefficient:
their difference lies in L(D-X), by the actual binary residue calculation. -/
theorem sub_mem_fullRiemannRochSpace25Two_sub_X (D : C.Divisor)
    (a b : L) (ha : a ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hb : b ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hanot : a ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1))
    (hbnot : b ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)) :
    a - b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) := by
  by_cases hab : a = b
  · rw [hab, sub_self]
    exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have ha0 : a ≠ 0 := by
    intro h
    apply hanot
    rw [h]
    exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have hb0 : b ≠ 0 := by
    intro h
    apply hbnot
    rw [h]
    exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have hxa := xBoundaryOrder_eq_neg_of_not_mem_sub_X C principal hmin R XPoint hcoeff D (Additive.ofMul (Units.mk0 a ha0)) ha hanot
  have hxb := xBoundaryOrder_eq_neg_of_not_mem_sub_X C principal hmin R XPoint hcoeff D (Additive.ofMul (Units.mk0 b hb0)) hb hbnot
  have hp := log_ordFrac_sub_gt_of_log_eq e a b ha0 hb0 hab
    (hxa.trans hxb.symm)
  have hs : a - b ≠ 0 := sub_ne_zero.mpr hab
  apply (mem_fullRiemannRochSpace25Two_sub_X_iff C principal hmin R XPoint hcoeff D
    (Additive.ofMul (Units.mk0 (a - b) hs)) ((fullRiemannRochSpace25Two C principal hmin D).sub_mem ha hb)).mpr
  change -D XPoint < WithZero.log (Ring.ordFrac R (a - b))
  change WithZero.log (Ring.ordFrac R b) = -D XPoint at hxb
  omega

end MazurProof.N25F_XSectionFiltration

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

namespace MazurProof.N25F_XSectionResidue
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_XSectionFiltration N25F_DVRIntegralLift
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (XPoint : C.Atom)
variable (hcoeff : ∀ f : Additive Lˣ, principal f XPoint = boundaryOrder R f)
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
variable (tau : R) (htaune : tau ≠ 0) (htauorder : Ring.ord R tau = 1)
private def xSectionScale (D : C.Divisor) : L :=
  ((algebraMap R L) tau) ^ (D XPoint)

include htaune in
omit [Algebra (ZMod 2) L] [IsDomain R] [IsDiscreteValuationRing R] in
private theorem xSectionScale_ne_zero (D : C.Divisor) : xSectionScale C (L := L) R XPoint tau D ≠ 0 :=
  zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr htaune)

include htaune htauorder in
omit [Algebra (ZMod 2) L] in
private theorem xSectionScale_order (D : C.Divisor) :
    WithZero.log ((Ring.ordFrac R) (xSectionScale C (L := L) R XPoint tau D)) = D XPoint := by
  have ht : (Ring.ordFrac R) ((algebraMap R L) tau) = WithZero.exp (1 : ℤ) := by
    change Ring.ordFrac R (algebraMap R L tau) = _
    rw [Ring.ordFrac_eq_ord R htaune,
      Ring.ordMonoidWithZeroHom_eq_coe R
        (mem_nonZeroDivisors_iff_ne_zero.mpr htaune) htauorder]
    rfl
  change WithZero.log ((Ring.ordFrac R)
    (((algebraMap R L) tau) ^ (D XPoint))) = D XPoint
  rw [map_zpow₀, WithZero.log_zpow, ht, WithZero.log_exp]
  simp

include hcoeff htaune htauorder in
private theorem scaled_section_nonneg (D : C.Divisor)
    (f : fullRiemannRochSpace25Two C principal hmin D) :
    xSectionScale C (L := L) R XPoint tau D * (f : L) = 0 ∨
      0 ≤ WithZero.log ((Ring.ordFrac R) (xSectionScale C (L := L) R XPoint tau D * (f : L))) := by
  rcases f.property with hzero | ⟨hf, hb⟩
  · exact Or.inl (by rw [hzero, mul_zero])
  right
  have hs : (Ring.ordFrac R) (xSectionScale C (L := L) R XPoint tau D) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr (xSectionScale_ne_zero C (L := L) R XPoint tau htaune D)).map (Ring.ordFrac R)).ne_zero
  have hv : (Ring.ordFrac R) (f : L) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hf).map (Ring.ordFrac R)).ne_zero
  rw [map_mul, WithZero.log_mul hs hv, xSectionScale_order C (L := L) R XPoint tau htaune htauorder]
  have hx := hb XPoint
  rw [hcoeff] at hx
  exact hx

include hcoeff htaune htauorder in
private theorem xScaledSection_has_germ (D : C.Divisor)
    (f : fullRiemannRochSpace25Two C principal hmin D) :
    ∃! a : R, (algebraMap R L) a = xSectionScale C (L := L) R XPoint tau D * (f : L) := by
  exact existsUnique_algebraMap_eq_of_log_nonneg _ (scaled_section_nonneg C principal hmin R XPoint hcoeff tau htaune htauorder D f)

/-- The unique actual X-local germ of (W/Z)^D(X) times a section. -/
def xScaledSectionGerm25Two (D : C.Divisor)
    (f : fullRiemannRochSpace25Two C principal hmin D) : R :=
  Classical.choose (xScaledSection_has_germ C principal hmin R XPoint hcoeff tau htaune htauorder D f)

@[simp]
theorem xLocalToFraction_xScaledSectionGerm25Two (D : C.Divisor)
    (f : fullRiemannRochSpace25Two C principal hmin D) :
    (algebraMap R L) (xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f) =
      ((algebraMap R L) tau) ^ (D XPoint) * (f : L) :=
  (Classical.choose_spec (xScaledSection_has_germ C principal hmin R XPoint hcoeff tau htaune htauorder D f)).1

private theorem xScaledSectionGerm_zero (D : C.Divisor) :
    xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D 0 = 0 := by
  apply (IsFractionRing.injective R L)
  rw [xLocalToFraction_xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder, map_zero]
  exact mul_zero _

theorem xScaledSectionGerm25Two_add (D : C.Divisor)
    (f g : fullRiemannRochSpace25Two C principal hmin D) :
    xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D (f + g) =
      xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f + xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D g := by
  apply (IsFractionRing.injective R L)
  simp only [map_add, xLocalToFraction_xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder, Submodule.coe_add, mul_add]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have hc : a.val = 0 ∨ a.val = 1 := by omega
  rcases hc with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- The genuine uniformizer-scaled residue, as an F2-linear functional on L(D). -/
def xLeadingResidue25Two (D : C.Divisor) :
    fullRiemannRochSpace25Two C principal hmin D →ₗ[ZMod 2] ZMod 2 where
  toFun f := e (IsLocalRing.residue R (xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f))
  map_add' f g := by rw [xScaledSectionGerm25Two_add C principal hmin R XPoint hcoeff tau htaune htauorder, map_add, map_add]
  map_smul' r f := by
    rcases zmod_two_cases r with rfl | rfl
    · simp only [zero_smul, xScaledSectionGerm_zero C principal hmin R XPoint hcoeff tau htaune htauorder, map_zero]
    · simp only [map_one, one_smul]

/-- Vanishing of the actual leading residue means exactly one extra zero at X. -/
theorem xLeadingResidue25Two_eq_zero_iff (D : C.Divisor)
    (f : fullRiemannRochSpace25Two C principal hmin D) :
    xLeadingResidue25Two C principal hmin R XPoint hcoeff e tau htaune htauorder D f = 0 ↔
      (f : L) ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) := by
  by_cases hf : (f : L) = 0
  · have hf0 : f = 0 := Subtype.ext hf
    rw [hf0, map_zero]
    simp only [Submodule.coe_zero, zero_mem, iff_self]
  have hg : xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f ≠ 0 := by
    intro h
    have hm := xLocalToFraction_xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f
    rw [h, map_zero] at hm
    exact (mul_ne_zero (xSectionScale_ne_zero C (L := L) R XPoint tau htaune D) hf) hm.symm
  change e
    (IsLocalRing.residue R (xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f)) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective,
    residue_eq_zero_iff_eq_zero_or_log_pos (L := L), or_iff_right hg]
  have hs : (Ring.ordFrac R) (xSectionScale C (L := L) R XPoint tau D) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr (xSectionScale_ne_zero C (L := L) R XPoint tau htaune D)).map (Ring.ordFrac R)).ne_zero
  have hv : (Ring.ordFrac R) (f : L) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hf).map (Ring.ordFrac R)).ne_zero
  change 0 < WithZero.log ((Ring.ordFrac R)
    ((algebraMap R L) (xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder D f))) ↔ _
  rw [xLocalToFraction_xScaledSectionGerm25Two C principal hmin R XPoint hcoeff tau htaune htauorder]
  change 0 < WithZero.log ((Ring.ordFrac R) (xSectionScale C (L := L) R XPoint tau D * (f : L))) ↔ _
  rw [map_mul, WithZero.log_mul hs hv, xSectionScale_order C (L := L) R XPoint tau htaune htauorder]
  have hm := mem_fullRiemannRochSpace25Two_sub_X_iff C principal hmin R XPoint hcoeff D
    (Additive.ofMul (Units.mk0 (f : L) hf)) f.property
  change ((f : L) ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ↔
    -D XPoint < WithZero.log ((Ring.ordFrac R) (f : L))) at hm
  rw [hm]
  omega

/-- The exact kernel of the genuine leading-residue functional is L(D-X). -/
theorem ker_xLeadingResidue25Two (D : C.Divisor) :
    LinearMap.ker (xLeadingResidue25Two C principal hmin R XPoint hcoeff e tau htaune htauorder D) =
      (fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)).submoduleOf
        (fullRiemannRochSpace25Two C principal hmin D) := by
  ext f
  exact xLeadingResidue25Two_eq_zero_iff C principal hmin R XPoint hcoeff e tau htaune htauorder D f

#print axioms xScaledSectionGerm25Two
#print axioms xLocalToFraction_xScaledSectionGerm25Two
#print axioms xScaledSectionGerm25Two_add
#print axioms xLeadingResidue25Two
#print axioms xLeadingResidue25Two_eq_zero_iff
#print axioms ker_xLeadingResidue25Two
end MazurProof.N25F_XSectionResidue
