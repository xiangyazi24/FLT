import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Option
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors

open scoped BigOperators

/-- A locally finite positive grading of closed points by residue degree.
Degree zero is empty because every closed point has a nonzero residue-field
degree. -/
structure ClosedPointGrading where
  Closed : ℕ → Type*
  finite_closed : ∀ d, Finite (Closed d)
  empty_degree_zero : IsEmpty (Closed 0)

namespace ClosedPointGrading

variable (C : ClosedPointGrading)

instance (d : ℕ) : Finite (C.Closed d) := C.finite_closed d

instance : IsEmpty (C.Closed 0) := C.empty_degree_zero

/-- A closed point together with its residue degree. -/
abbrev Atom := Σ d : ℕ, C.Closed d

/-- The residue degree of a graded closed point. -/
def atomDegree (x : C.Atom) : ℕ := x.1

/-- Every closed point has positive degree. -/
theorem atomDegree_pos (x : C.Atom) : 0 < C.atomDegree x := by
  rcases x with ⟨d, x⟩
  cases d with
  | zero => exact isEmptyElim x
  | succ d => simp [atomDegree]

/-- Effective divisors are finite nonnegative multiplicity functions on
closed points. -/
abbrev EffDiv := C.Atom →₀ ℕ

/-- The degree of an effective divisor is the multiplicity-weighted sum of
its closed-point degrees. -/
def divDegree (D : C.EffDiv) : ℕ :=
  D.sum fun x m => m * C.atomDegree x

@[simp]
theorem divDegree_zero : C.divDegree 0 = 0 := by
  simp [divDegree]

/-- Divisor degree is additive. -/
theorem divDegree_add (D E : C.EffDiv) :
    C.divDegree (D + E) = C.divDegree D + C.divDegree E := by
  classical
  exact Finsupp.sum_add_index' (by simp) (by
    intro x m₁ m₂
    simp only [add_mul])

/-- A single closed point with multiplicity `m` has degree `m * deg(x)`. -/
theorem divDegree_single (x : C.Atom) (m : ℕ) :
    C.divDegree (Finsupp.single x m) = m * C.atomDegree x := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  · simp [divDegree]

/-- Removing at most the available multiplicity and then restoring it
recovers the original divisor. -/
theorem sub_single_add_single (D : C.EffDiv) (x : C.Atom) (r : ℕ)
    (hr : r ≤ D x) :
    D - Finsupp.single x r + Finsupp.single x r = D := by
  classical
  ext y
  by_cases hy : y = x
  · subst y
    simp [Nat.sub_add_cancel hr]
  · simp [hy]

/-- Adding copies of one closed point and then removing the same copies
recovers the original divisor. -/
theorem add_single_sub_single (D : C.EffDiv) (x : C.Atom) (r : ℕ) :
    D + Finsupp.single x r - Finsupp.single x r = D := by
  classical
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp

/-- Exact subtraction of `r` copies of a closed point subtracts
`r * deg(x)` from the total degree. -/
theorem divDegree_sub_single (D : C.EffDiv) (x : C.Atom) (r : ℕ)
    (hr : r ≤ D x) :
    C.divDegree (D - Finsupp.single x r) =
      C.divDegree D - r * C.atomDegree x := by
  have hdecomp := congrArg C.divDegree (C.sub_single_add_single D x r hr)
  rw [C.divDegree_add, C.divDegree_single] at hdecomp
  omega

/-- The contribution of one closed point is bounded by the total divisor
degree. -/
theorem term_le_divDegree (D : C.EffDiv) (x : C.Atom) :
    D x * C.atomDegree x ≤ C.divDegree D := by
  classical
  by_cases hx : D x = 0
  · simp [hx]
  · rw [divDegree, Finsupp.sum]
    exact Finset.single_le_sum
      (s := D.support) (f := fun y => D y * C.atomDegree y)
      (fun y _hy => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)

/-- A divisor whose total degree is at most `n` has multiplicity at most `n`
at every closed point. -/
theorem coeff_le_of_divDegree_le (D : C.EffDiv) (n : ℕ)
    (hdegree : C.divDegree D ≤ n) (x : C.Atom) :
    D x ≤ n := by
  calc
    D x = D x * 1 := by omega
    _ ≤ D x * C.atomDegree x :=
      Nat.mul_le_mul_left (D x) (C.atomDegree_pos x)
    _ ≤ C.divDegree D := C.term_le_divDegree D x
    _ ≤ n := hdegree

/-- A closed point occurring in a divisor of degree at most `n` itself has
degree at most `n`. -/
theorem atomDegree_le_of_mem_support (D : C.EffDiv) (n : ℕ)
    (hdegree : C.divDegree D ≤ n) {x : C.Atom} (hx : x ∈ D.support) :
    C.atomDegree x ≤ n := by
  have hcoeff : 1 ≤ D x := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)
  calc
    C.atomDegree x = 1 * C.atomDegree x := by omega
    _ ≤ D x * C.atomDegree x := Nat.mul_le_mul_right _ hcoeff
    _ ≤ C.divDegree D := C.term_le_divDegree D x
    _ ≤ n := hdegree

/-- The finite type of closed points whose degree is at most `n`. -/
def AtomLE (n : ℕ) := {x : C.Atom // C.atomDegree x ≤ n}

/-- Bounded-degree closed points are equivalent to a finite sigma type over
the possible degrees `0,...,n`. -/
def atomLEEquivSigma (n : ℕ) :
    C.AtomLE n ≃ Σ d : Fin (n + 1), C.Closed d.1 where
  toFun x := ⟨⟨x.1.1, by
    simpa [atomDegree] using Nat.lt_succ_of_le x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, by
    simpa [atomDegree] using Nat.le_of_lt_succ x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance atomLEFinite (n : ℕ) : Finite (C.AtomLE n) :=
  Finite.of_equiv (Σ d : Fin (n + 1), C.Closed d.1) (C.atomLEEquivSigma n).symm

/-- Effective divisors of one prescribed total degree. -/
def EffDivOfDegree (n : ℕ) := {D : C.EffDiv // C.divDegree D = n}

/-- The bounded multiplicity table of a degree-`n` divisor. -/
noncomputable def boundedTable (n : ℕ) :
    C.EffDivOfDegree n → C.AtomLE n → Fin (n + 1) :=
  fun D x => ⟨D.1 x.1, by
    apply Nat.lt_succ_of_le
    exact C.coeff_le_of_divDegree_le D.1 n (Nat.le_of_eq D.2) x.1⟩

/-- The bounded table remembers the entire divisor: outside the bounded atom
type both divisors must have coefficient zero. -/
theorem boundedTable_injective (n : ℕ) :
    Function.Injective (C.boundedTable n) := by
  intro D E htable
  apply Subtype.ext
  ext x
  by_cases hx : C.atomDegree x ≤ n
  · have hvalue := congrFun htable (⟨x, hx⟩ : C.AtomLE n)
    exact congrArg Fin.val hvalue
  · have hDx : D.1 x = 0 := by
      by_contra hne
      have hmem : x ∈ D.1.support := Finsupp.mem_support_iff.mpr hne
      exact hx (C.atomDegree_le_of_mem_support D.1 n (Nat.le_of_eq D.2) hmem)
    have hEx : E.1 x = 0 := by
      by_contra hne
      have hmem : x ∈ E.1.support := Finsupp.mem_support_iff.mpr hne
      exact hx (C.atomDegree_le_of_mem_support E.1 n (Nat.le_of_eq E.2) hmem)
    rw [hDx, hEx]

/-- Fixed-degree effective divisors form a finite type.  This uses bounded
support and bounded multiplicity, not a generated list of divisors. -/
noncomputable instance effDivOfDegreeFinite (n : ℕ) :
    Finite (C.EffDivOfDegree n) := by
  letI := Fintype.ofFinite (C.AtomLE n)
  exact Finite.of_injective (C.boundedTable n) (C.boundedTable_injective n)

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

/-- Regard an effective divisor as a signed divisor by casting each
nonnegative multiplicity to an integer. -/
noncomputable def effectiveToDivisor : C.EffDiv →+ C.Divisor :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp]
theorem effectiveToDivisor_apply (D : C.EffDiv) (x : C.Atom) :
    C.effectiveToDivisor D x = (D x : ℤ) := by
  rfl

/-- Passing from an effective divisor to the signed divisor group preserves
its degree.  The right side is merely the natural degree cast to `ℤ`. -/
theorem divisorDegree_effectiveToDivisor (D : C.EffDiv) :
    C.divisorDegree (C.effectiveToDivisor D) = (C.divDegree D : ℤ) := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | @single_add x m D hx hm ih =>
      simp only [map_add, C.divDegree_add, Nat.cast_add, ih]
      rw [C.divDegree_single]
      simp [effectiveToDivisor, divisorDegree]

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

namespace MazurProof.N25F_SectionFiniteness
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
/-- The nonzero elements of the genuine bounded-pole vector space. -/
abbrev NonzeroSection25Two (D : C.Divisor) :=
  {f : fullRiemannRochSpace25Two C principal hmin D // f ≠ 0}

private theorem section_value_ne_zero (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    (f.1 : L) ≠ 0 := fun h => f.2 (Subtype.ext h)

private def sectionUnit (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    Additive Lˣ :=
  Additive.ofMul (Units.mk0 (f.1 : L) (section_value_ne_zero C principal hmin D f))

private theorem section_divisor_nonneg (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    ∀ A, 0 ≤ D A + principal (sectionUnit C principal hmin D f) A := by
  rcases f.1.property with h | ⟨hf, h⟩
  · exact (section_value_ne_zero C principal hmin D f h).elim
  exact h

private def sectionEffectiveData (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    C.EffDiv :=
  Finsupp.mapRange Int.toNat rfl (D + principal (sectionUnit C principal hmin D f))

private theorem sectionEffectiveData_cast (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    C.effectiveToDivisor (sectionEffectiveData C principal hmin D f) =
      D + principal (sectionUnit C principal hmin D f) := by
  ext A
  change ((D A + principal (sectionUnit C principal hmin D f) A).toNat : ℤ) = _
  exact Int.natCast_toNat_eq_self.mpr (section_divisor_nonneg C principal hmin D f A)

/-- The effective divisor D+div(f), with its exact full-grading degree. -/
def effectiveDivisorOfNonzeroSection25Two (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    C.EffDivOfDegree
      (C.divisorDegree D).toNat := by
  refine ⟨sectionEffectiveData C principal hmin D f, ?_⟩
  have h : (C.divDegree (sectionEffectiveData C principal hmin D f) : ℤ) =
      C.divisorDegree D := by
    rw [← C.divisorDegree_effectiveToDivisor,
      sectionEffectiveData_cast C principal hmin, map_add, hzero, add_zero]
  simpa only [Int.toNat_natCast] using congrArg Int.toNat h

theorem effectiveDivisorOfNonzeroSection25Two_cast
    (D : C.Divisor) (f : NonzeroSection25Two C principal hmin D) :
    C.effectiveToDivisor (effectiveDivisorOfNonzeroSection25Two C principal hmin hzero D f).1 =
      D + principal
        (Additive.ofMul (Units.mk0 (f.1 : L) (section_value_ne_zero C principal hmin D f))) :=
  sectionEffectiveData_cast C principal hmin D f

include hinj in
/-- The actual constant-kernel theorem makes the effective-section map injective. -/
theorem effectiveDivisorOfNonzeroSection25Two_injective (D : C.Divisor) :
    Function.Injective (effectiveDivisorOfNonzeroSection25Two C principal hmin hzero D) := by
  intro f g h
  have he := congrArg (fun E => C.effectiveToDivisor E.1) h
  rw [effectiveDivisorOfNonzeroSection25Two_cast C principal hmin hzero,
    effectiveDivisorOfNonzeroSection25Two_cast C principal hmin hzero] at he
  have hu := hinj (add_left_cancel he)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : Additive Lˣ => (u.toMul : L)) hu

include hzero hinj in
/-- This uses the full grading's uniform fixed-degree finiteness producer. -/
theorem nonzeroSection25Two_finite (D : C.Divisor) : Finite (NonzeroSection25Two C principal hmin D) :=
  Finite.of_injective (effectiveDivisorOfNonzeroSection25Two C principal hmin hzero D)
    (effectiveDivisorOfNonzeroSection25Two_injective C principal hmin hzero hinj D)

include hzero hinj in
theorem fullRiemannRochSpace25Two_finite (D : C.Divisor) :
    Finite (fullRiemannRochSpace25Two C principal hmin D) := by
  classical
  letI := nonzeroSection25Two_finite C principal hmin hzero hinj D
  exact Finite.of_equiv (Option (NonzeroSection25Two C principal hmin D))
    (Equiv.optionSubtypeNe (0 : fullRiemannRochSpace25Two C principal hmin D))

include hzero hinj in
/-- Every actual bounded-pole section space is finite-dimensional over F2. -/
theorem fullRiemannRochSpace25Two_moduleFinite (D : C.Divisor) :
    Module.Finite (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) := by
  letI := fullRiemannRochSpace25Two_finite C principal hmin hzero hinj D
  infer_instance


end MazurProof.N25F_SectionFiniteness

namespace MazurProof.N25F_XSectionDimension
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
variable (XPoint : C.Atom)
variable (hle : ∀ D : C.Divisor,
  fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ≤
  fullRiemannRochSpace25Two C principal hmin D)
variable (hsub : ∀ D : C.Divisor, ∀ a b : L,
  a ∈ fullRiemannRochSpace25Two C principal hmin D →
  b ∈ fullRiemannRochSpace25Two C principal hmin D →
  a ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) →
  b ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) →
  a - b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1))
variable (hdegree : C.atomDegree XPoint = 1)
include hle hsub in
/-- Any section at the extremal X order spans the single possible new direction. -/
theorem fullRiemannRochSpace25Two_eq_sub_X_sup_span (D : C.Divisor)
    (a : L) (ha : a ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hanot : a ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)) :
    fullRiemannRochSpace25Two C principal hmin D =
      fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set L) := by
  apply le_antisymm
  · intro b hb
    by_cases hbn : b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)
    · exact le_sup_left hbn
    have hba := hsub D b a hb ha hbn hanot
    have haS : a ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set L) :=
      le_sup_right (Submodule.subset_span (Set.mem_singleton a))
    simpa only [sub_add_cancel] using
      (Submodule.add_mem _ (le_sup_left hba) haS)
  · refine sup_le (hle D) ?_
    exact Submodule.span_le.mpr (by intro b hb; simpa only [Set.mem_singleton_iff.mp hb] using ha)

include hzero hinj hle hsub in
/-- Removing the actual degree-one X point loses at most one independent section. -/
theorem finrank_fullRiemannRochSpace25Two_le_sub_X_add_one (D : C.Divisor) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) ≤
      Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)) + 1 := by
  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj (D - Finsupp.single XPoint 1)
  by_cases hback : fullRiemannRochSpace25Two C principal hmin D ≤
      fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1)
  · exact (Submodule.finrank_mono hback).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, hanot⟩ := SetLike.not_le_iff_exists.mp hback
  have ha0 : a ≠ 0 := by
    intro h
    apply hanot
    rw [h]
    exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  rw [fullRiemannRochSpace25Two_eq_sub_X_sup_span C principal hmin XPoint hle hsub D a ha hanot]
  simpa only [finrank_span_singleton ha0] using
    (Submodule.finrank_add_le_finrank_add_finrank
      (fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1))
      (Submodule.span (ZMod 2) ({a} : Set L)))

include hzero hinj hle hsub hdegree in
/-- The actual elementary upper bound follows by successively removing X,
ending in the already proved negative-degree zero space. -/
theorem finrank_fullRiemannRochSpace25Two_le_degree_add_one (D : C.Divisor) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) ≤
      (C.divisorDegree D + 1).toNat := by
  classical
  have hX : C.divisorDegree (Finsupp.single XPoint 1) = 1 := by
    simp [ClosedPointGrading.divisorDegree, hdegree]
  have hbound : ∀ n : ℕ, ∀ E : C.Divisor,
      C.divisorDegree E ≤ n →
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin E) ≤ n + 1 := by
    intro n
    induction n with
    | zero =>
        intro E hE
        have hneg : C.divisorDegree
            (E - Finsupp.single XPoint 1) < 0 := by
          rw [map_sub, hX]
          omega
        have hstep := finrank_fullRiemannRochSpace25Two_le_sub_X_add_one C principal hmin hzero hinj XPoint hle hsub E
        rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg C principal hmin hzero _ hneg,
          finrank_bot] at hstep
        exact hstep
    | succ n ih =>
        intro E hE
        have hsmall : C.divisorDegree
            (E - Finsupp.single XPoint 1) ≤ n := by
          rw [map_sub, hX]
          omega
        exact (finrank_fullRiemannRochSpace25Two_le_sub_X_add_one C principal hmin hzero hinj XPoint hle hsub E).trans
          (Nat.add_le_add_right (ih _ hsmall) 1)
  by_cases hneg : C.divisorDegree D < 0
  · rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg C principal hmin hzero D hneg, finrank_bot]
    exact Nat.zero_le _
  have h := hbound (C.divisorDegree D).toNat D (by omega)
  have he : (C.divisorDegree D + 1).toNat =
      (C.divisorDegree D).toNat + 1 := by omega
  rwa [he]

#print axioms fullRiemannRochSpace25Two_eq_sub_X_sup_span
#print axioms finrank_fullRiemannRochSpace25Two_le_sub_X_add_one
#print axioms finrank_fullRiemannRochSpace25Two_le_degree_add_one
end MazurProof.N25F_XSectionDimension
