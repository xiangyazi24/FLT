import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
namespace MazurProof.N25F_ZeroDegreeConstants
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_BinaryResidueOrder
variable {L : Type*} [Field L]
private theorem unit_mk0_eq (f : Additive Lˣ) (hf : (f.toMul : L) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : L) hf) = f := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl


variable (C : ClosedPointGrading) [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (x : C.Atom) (hdeg : C.atomDegree x = 1)
variable (hpoint : ∀ f : Additive Lˣ, principal f x = WithZero.log (Ring.ordFrac R (f.toMul : L)))
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
theorem one_mem_fullRiemannRochSpace25Two_zero :
    (1 : L) ∈ (fullRiemannRochSpace25Two C principal hmin) 0 := by
  refine Or.inr ⟨one_ne_zero, ?_⟩
  intro A
  have h1 : Additive.ofMul (Units.mk0 (1 : L) one_ne_zero) = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  rw [h1, map_zero]
  simp

include hzero hdeg hpoint in
/-- A nonzero globally regular function cannot vanish at the actual X point:
that would place it in the already vanishing degree-minus-one space. -/
theorem xBoundaryOrder_eq_zero_of_mem_zero (f : Additive Lˣ)
    (hf : (f.toMul : L) ∈ (fullRiemannRochSpace25Two C principal hmin) 0) :
    WithZero.log (Ring.ordFrac R (f.toMul : L)) = 0 := by
  classical
  have hb : ∀ A, 0 ≤ principal f A := by
    rcases hf with hf | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero hf).elim
    intro A
    simpa only [unit_mk0_eq f hf0, Finsupp.zero_apply, zero_add] using hb A
  have hx := hb (x)
  rw [hpoint] at hx
  by_contra hne
  have hpos : 0 < WithZero.log (Ring.ordFrac R (f.toMul : L)) := by omega
  have hD : C.divisorDegree
      (-(Finsupp.single (x) (1 : ℤ))) < 0 := by
    rw [map_neg]
    simp [ClosedPointGrading.divisorDegree, hdeg]
  have hmem : (f.toMul : L) ∈ (fullRiemannRochSpace25Two C principal hmin)
      (-(Finsupp.single (x) (1 : ℤ))) := by
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = x
    · subst A
      simp only [Finsupp.neg_apply, Finsupp.single_eq_same, hpoint]
      omega
    · simpa [hA, Ne.symm hA] using hb A
  rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg C principal hmin hzero _ hD, Submodule.mem_bot] at hmem
  exact f.toMul.ne_zero hmem

include hzero hdeg hpoint e in
/-- Every globally regular function on the actual full curve is zero or one. -/
theorem mem_fullRiemannRochSpace25Two_zero_iff (a : L) :
    a ∈ (fullRiemannRochSpace25Two C principal hmin) 0 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    right
    by_contra ha1
    have hx := (xBoundaryOrder_eq_zero_of_mem_zero (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint)) (Additive.ofMul (Units.mk0 a ha0)) ha
    change WithZero.log (Ring.ordFrac R a) = 0 at hx
    have hv : Ring.ordFrac R a ≠ 0 :=
      ((isUnit_iff_ne_zero.mpr ha0).map (Ring.ordFrac R)).ne_zero
    have he := WithZero.exp_log hv
    rw [hx, WithZero.exp_zero] at he
    have hp := log_ordFrac_sub_one_pos e a ha1 he.symm
    have hs : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hmem : a - 1 ∈ (fullRiemannRochSpace25Two C principal hmin) 0 :=
      ((fullRiemannRochSpace25Two C principal hmin) 0).sub_mem ha (one_mem_fullRiemannRochSpace25Two_zero (C := C) (principal := principal) (hmin := hmin))
    have hz := (xBoundaryOrder_eq_zero_of_mem_zero (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint)) (Additive.ofMul (Units.mk0 (a - 1) hs)) hmem
    change WithZero.log (Ring.ordFrac R (a - 1)) = 0 at hz
    omega
  · rintro (rfl | rfl)
    · exact ((fullRiemannRochSpace25Two C principal hmin) 0).zero_mem
    · exact (one_mem_fullRiemannRochSpace25Two_zero (C := C) (principal := principal) (hmin := hmin))

include hzero hdeg hpoint e in
/-- The degree-zero section space is the actual one-dimensional constant line. -/
theorem fullRiemannRochSpace25Two_zero_eq_span_one :
    (fullRiemannRochSpace25Two C principal hmin) 0 = Submodule.span (ZMod 2) ({1} : Set L) := by
  apply le_antisymm
  · intro a ha
    rcases ((mem_fullRiemannRochSpace25Two_zero_iff (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint) (e := e)) a).mp ha with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact (one_mem_fullRiemannRochSpace25Two_zero (C := C) (principal := principal) (hmin := hmin))

include hzero hdeg hpoint e in
theorem fullRiemannRochSpace25Two_zero_finite :
    Module.Finite (ZMod 2) ((fullRiemannRochSpace25Two C principal hmin) 0) := by
  rw [(fullRiemannRochSpace25Two_zero_eq_span_one (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint) (e := e))]
  infer_instance

include hzero hdeg hpoint e in
theorem finrank_fullRiemannRochSpace25Two_zero :
    Module.finrank (ZMod 2) ((fullRiemannRochSpace25Two C principal hmin) 0) = 1 := by
  rw [(fullRiemannRochSpace25Two_zero_eq_span_one (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint) (e := e))]
  exact finrank_span_singleton one_ne_zero

include hmin hzero hdeg hpoint e in
/-- The full principal map has precisely the actual constant-function kernel;
over F2 the sole nonzero constant is the identity unit. -/
theorem fullPrincipalDivisor_eq_zero_iff (f : Additive Lˣ) :
    principal f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hm : (f.toMul : L) ∈ (fullRiemannRochSpace25Two C principal hmin) 0 := by
      refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
      intro A
      rw [unit_mk0_eq f f.toMul.ne_zero, hf]
      simp
    rcases ((mem_fullRiemannRochSpace25Two_zero_iff (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint) (e := e)) _).mp hm with h0 | h1
    · exact (f.toMul.ne_zero h0).elim
    · apply Additive.toMul.injective
      apply Units.ext
      exact h1
  · rintro rfl
    exact map_zero _

include hmin hzero hdeg hpoint e in
/-- The full principal divisor determines an actual nonzero function uniquely
because the binary field has only one nonzero constant. -/
theorem fullPrincipalDivisor_injective : Function.Injective principal := by
  intro f g h
  have hz : principal (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (((fullPrincipalDivisor_eq_zero_iff (C := C) (principal := principal) (hmin := hmin) (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint) (e := e)) _).mp hz)


#print axioms one_mem_fullRiemannRochSpace25Two_zero
#print axioms xBoundaryOrder_eq_zero_of_mem_zero
#print axioms mem_fullRiemannRochSpace25Two_zero_iff
#print axioms fullRiemannRochSpace25Two_zero_eq_span_one
#print axioms fullRiemannRochSpace25Two_zero_finite
#print axioms finrank_fullRiemannRochSpace25Two_zero
#print axioms fullPrincipalDivisor_eq_zero_iff
#print axioms fullPrincipalDivisor_injective
end MazurProof.N25F_ZeroDegreeConstants
