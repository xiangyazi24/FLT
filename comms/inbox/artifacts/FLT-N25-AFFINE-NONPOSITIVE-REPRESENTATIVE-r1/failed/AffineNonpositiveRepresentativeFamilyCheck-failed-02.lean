import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.QuotientGroup.Basic
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
namespace MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading
variable (C : ClosedPointGrading)
abbrev DivisorClass (Principal : AddSubgroup C.Divisor) :=
  C.Divisor ⧸ Principal

/-- The class of a signed divisor in the quotient by principal divisors. -/
noncomputable def classOf (Principal : AddSubgroup C.Divisor) :
    C.Divisor →+ C.DivisorClass Principal :=
  QuotientAddGroup.mk' Principal

end MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading

namespace MazurProof.N25F_SectionClassFiber
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
omit [Algebra (ZMod 2) L] in
theorem class_eq_iff (D E : C.Divisor) :
  C.classOf principal.range D = C.classOf principal.range E ↔
  ∃ f : Additive Lˣ, principal f = D - E := by
  change ((D : C.Divisor ⧸ principal.range) = E) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl
/-- Effective full divisors whose class is the class of the actual signed divisor D. -/
abbrev FullEffectiveClassFiber25Two (D : C.Divisor) :=
  {E : C.EffDivOfDegree
      (C.divisorDegree D).toNat //
    C.classOf principal.range
      (C.effectiveToDivisor E.1) =
    C.classOf principal.range D}

/-- The actual section-to-divisor map lands in the correct full Picard fibre. -/
def nonzeroSectionToFullClassFiber25Two (D : C.Divisor)
    (f : NonzeroSection25Two C principal hmin D) : FullEffectiveClassFiber25Two C principal D := by
  refine ⟨effectiveDivisorOfNonzeroSection25Two C principal hmin hzero D f, ?_⟩
  rw [class_eq_iff C principal]
  have hf : (f.1 : L) ≠ 0 := fun h => f.2 (Subtype.ext h)
  refine ⟨Additive.ofMul (Units.mk0 (f.1 : L) hf), ?_⟩
  rw [effectiveDivisorOfNonzeroSection25Two_cast C principal hmin hzero]
  simp only [add_sub_cancel_left]

include hinj in
theorem nonzeroSectionToFullClassFiber25Two_injective (D : C.Divisor) :
    Function.Injective (nonzeroSectionToFullClassFiber25Two C principal hmin hzero D) := by
  intro f g h
  exact effectiveDivisorOfNonzeroSection25Two_injective C principal hmin hzero hinj D (congrArg Subtype.val h)

/-- A genuine principal representative of a class equality produces a section. -/
theorem nonzeroSectionToFullClassFiber25Two_surjective (D : C.Divisor) :
    Function.Surjective (nonzeroSectionToFullClassFiber25Two C principal hmin hzero D) := by
  intro E
  obtain ⟨f, hfdiv⟩ := (class_eq_iff C principal _ _).mp E.2
  have hrepr : D + principal f =
      C.effectiveToDivisor E.1.1 :=
    (add_comm D _).trans (eq_sub_iff_add_eq.mp hfdiv)
  have hf : (f.toMul : L) ≠ 0 := Units.ne_zero f.toMul
  have hunit : Additive.ofMul (Units.mk0 (f.toMul : L) hf) = f := by
    change Units.mk0 (f.toMul : L) hf = f.toMul
    exact Units.ext rfl
  have hmem : (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin D := by
    refine Or.inr ⟨hf, ?_⟩
    intro A
    rw [hunit]
    change 0 ≤ (D + principal f) A
    rw [hrepr]
    exact Int.natCast_nonneg _
  let g : NonzeroSection25Two C principal hmin D :=
    ⟨⟨(f.toMul : L), hmem⟩, fun h => hf (congrArg Subtype.val h)⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he : C.effectiveToDivisor
      (effectiveDivisorOfNonzeroSection25Two C principal hmin hzero D g).1 =
      C.effectiveToDivisor E.1.1 := by
    rw [effectiveDivisorOfNonzeroSection25Two_cast C principal hmin hzero]
    change D + principal (Additive.ofMul (Units.mk0 (f.toMul : L) hf)) = _
    rw [hunit, hrepr]
  ext A
  exact Int.ofNat_inj.mp (congrArg (fun H => H A) he)

/-- Over F2 the actual nonzero sections are exactly the effective class fibre. -/
def nonzeroSectionEquivFullClassFiber25Two (D : C.Divisor) :
    NonzeroSection25Two C principal hmin D ≃ FullEffectiveClassFiber25Two C principal D :=
  Equiv.ofBijective (nonzeroSectionToFullClassFiber25Two C principal hmin hzero D)
    ⟨nonzeroSectionToFullClassFiber25Two_injective C principal hmin hzero hinj D,
      nonzeroSectionToFullClassFiber25Two_surjective C principal hmin hzero D⟩

include hzero hinj in
theorem fullRiemannRochSpace25Two_card (D : C.Divisor) :
    Nat.card (fullRiemannRochSpace25Two C principal hmin D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) := by
  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj D
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fullRiemannRochSpace25Two C principal hmin D))

include hzero hinj in
theorem nonzeroSection25Two_card (D : C.Divisor) :
    Nat.card (NonzeroSection25Two C principal hmin D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) - 1 := by
  classical
  letI := nonzeroSection25Two_finite C principal hmin hzero hinj D
  have h := Nat.card_congr (Equiv.optionSubtypeNe (0 : fullRiemannRochSpace25Two C principal hmin D))
  rw [Finite.card_option, fullRiemannRochSpace25Two_card C principal hmin hzero hinj] at h
  change Nat.card (NonzeroSection25Two C principal hmin D) + 1 =
    2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) at h
  exact Nat.eq_sub_of_add_eq h

include hmin hzero hinj in
/-- The exact finite class-fibre cardinality, with the genuine section-space rank. -/
theorem fullEffectiveClassFiber25Two_card (D : C.Divisor) :
    Nat.card (FullEffectiveClassFiber25Two C principal D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) - 1 := by
  rw [← Nat.card_congr (nonzeroSectionEquivFullClassFiber25Two C principal hmin hzero hinj D), nonzeroSection25Two_card C principal hmin hzero hinj]

end MazurProof.N25F_SectionClassFiber

namespace MazurProof.N25F_SectionPrincipalTransport
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
/-- The actual principal relation controls multiplication of bounded-pole functions. -/
theorem mul_mem_fullRiemannRochSpace25Two (D E : C.Divisor)
    (f : Additive Lˣ) (hdiv : principal f = D - E)
    (a : L) (ha : a ∈ fullRiemannRochSpace25Two C principal hmin D) :
    (f.toMul : L) * a ∈ fullRiemannRochSpace25Two C principal hmin E := by
  rcases ha with rfl | ⟨ha, hbound⟩
  · exact Or.inl (mul_zero _)
  have hfa : (f.toMul : L) * a ≠ 0 := mul_ne_zero (Units.ne_zero _) ha
  refine Or.inr ⟨hfa, ?_⟩
  have hunit : Additive.ofMul (Units.mk0 ((f.toMul : L) * a) hfa) =
      f + Additive.ofMul (Units.mk0 a ha) := by
    change Units.mk0 ((f.toMul : L) * a) hfa = f.toMul * Units.mk0 a ha
    exact Units.ext rfl
  intro A
  rw [hunit, map_add]
  have hA := congrArg (fun H : C.Divisor => H A) hdiv
  simp only [Finsupp.sub_apply] at hA
  have hb := hbound A
  change 0 ≤ E A + (principal f A +
    principal (Additive.ofMul (Units.mk0 a ha)) A)
  omega

/-- Multiplication by an actual nonzero function is a linear equivalence of its section spaces. -/
def principalSectionLinearEquiv25Two (D E : C.Divisor)
    (f : Additive Lˣ) (hdiv : principal f = D - E) :
    fullRiemannRochSpace25Two C principal hmin D ≃ₗ[ZMod 2] fullRiemannRochSpace25Two C principal hmin E where
  toFun a := ⟨(f.toMul : L) * a.1,
    mul_mem_fullRiemannRochSpace25Two C principal hmin D E f hdiv a.1 a.2⟩
  invFun a := ⟨((-f).toMul : L) * a.1,
    mul_mem_fullRiemannRochSpace25Two C principal hmin E D (-f)
      (by rw [map_neg, hdiv, neg_sub]) a.1 a.2⟩
  left_inv a := by
    apply Subtype.ext
    change (↑f.toMul⁻¹ : L) * ((f.toMul : L) * a.1) = a.1
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv a := by
    apply Subtype.ext
    change (f.toMul : L) * ((↑f.toMul⁻¹ : L) * a.1) = a.1
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' r a := by
    apply Subtype.ext
    exact mul_smul_comm _ _ _

/-- The actual section dimension depends only on the full divisor class. -/
theorem finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq
    (D E : C.Divisor)
    (h : C.classOf principal.range D =
      C.classOf principal.range E) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin E) := by
  obtain ⟨f, hf⟩ := (N25F_SectionClassFiber.class_eq_iff C principal D E).mp h
  exact (principalSectionLinearEquiv25Two C principal hmin D E f hf).finrank_eq

/-- The genuine section rank descended to the full divisor-class quotient. -/
def fullClassSectionRank25Two :
    C.DivisorClass principal.range → ℕ :=
  Quotient.lift (fun D => Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D))
    (fun D E h => finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq C principal hmin D E (Quotient.sound h))

@[simp]
theorem fullClassSectionRank25Two_classOf (D : C.Divisor) :
    fullClassSectionRank25Two C principal hmin
      (C.classOf principal.range D) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) := rfl

end MazurProof.N25F_SectionPrincipalTransport

/-!
# Divisors from Dedekind-domain factorization

For a Dedekind domain, every nonzero fractional ideal has a finite height-one
valuation vector.  This file packages that vector as a `Finsupp`, proves that
it determines the fractional ideal, and constructs the subgroup of principal
divisors from nonzero elements of the fraction field.

This is the affine algebra underlying the divisor-class input used by the
curve zeta argument.  Applying it to a projective curve still requires the
geometric comparison between its closed points and height-one local data,
including the points outside any chosen affine chart.
-/

open scoped nonZeroDivisors

open IsDedekindDomain

noncomputable section

namespace MazurProof.CurveDedekindDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A Weil divisor on the spectrum of a Dedekind domain is a finite integer
combination of its height-one prime ideals. -/
abbrev Divisor := HeightOneSpectrum R →₀ ℤ

/-- The height-one valuation vector of a fractional ideal.  The finite support
is supplied by Dedekind factorization. -/
def fractionalIdealDivisor (I : FractionalIdeal R⁰ K) : Divisor (R := R) := by
  let support : Set (HeightOneSpectrum R) :=
    {v | FractionalIdeal.count K v I ≠ 0}
  have hsupport : support.Finite := by
    exact Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K) I)
  exact Finsupp.onFinset hsupport.toFinset
    (fun v ↦ FractionalIdeal.count K v I)
    (fun v hv ↦ hsupport.mem_toFinset.mpr hv)

@[simp]
theorem fractionalIdealDivisor_apply (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) :
    fractionalIdealDivisor I v = FractionalIdeal.count K v I := by
  rfl

/-- Multiplication of nonzero fractional ideals adds their valuation vectors. -/
theorem fractionalIdealDivisor_mul {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalIdealDivisor (I * J) =
      fractionalIdealDivisor I + fractionalIdealDivisor J := by
  ext v
  simp only [fractionalIdealDivisor_apply, Finsupp.add_apply]
  exact FractionalIdeal.count_mul K v hI hJ

/-- Nonzero fractional ideals are determined by their height-one valuation
vectors.  This is the uniqueness half of Dedekind factorization in divisor
form. -/
theorem fractionalIdealDivisor_injectiveOn_nonzero
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hdiv : fractionalIdealDivisor I = fractionalIdealDivisor J) : I = J := by
  calc
    I = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v I :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
    _ = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v J := by
      apply finprod_congr
      intro v
      congr 1
      simpa only [fractionalIdealDivisor_apply] using DFunLike.congr_fun hdiv v
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

/-- Principal fractional ideals define an additive homomorphism from nonzero
functions under multiplication to height-one divisors. -/
def principalDivisor : Additive Kˣ →+ Divisor (R := R) where
  toFun x := fractionalIdealDivisor
    (FractionalIdeal.spanSingleton R⁰ (x.toMul : K))
  map_zero' := by
    ext v
    change FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (1 : K)) = 0
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  map_add' x y := by
    change fractionalIdealDivisor
      (FractionalIdeal.spanSingleton R⁰ ((x.toMul * y.toMul : Kˣ) : K)) = _
    rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply fractionalIdealDivisor_mul
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.toMul.ne_zero

/-- The subgroup generated by divisors of nonzero fraction-field elements. -/
def principalDivisors : AddSubgroup (Divisor (R := R)) :=
  (principalDivisor (R := R) (K := K)).range

end MazurProof.CurveDedekindDivisor

/-! A genuine nonzero regular function can dominate any finitely supported
signed affine divisor, by membership in its fractional-ideal product. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_DedekindPrincipalMajorant

/-- Construct a real regular function satisfying all signed affine order lower bounds. -/
theorem exists_nonzero_regular_with_count_ge {R K : Type*}
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (D : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    ∃ a : R, ∃ ha : a ≠ 0, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      D v ≤ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  classical
  let I : FractionalIdeal R⁰ K :=
    D.prod fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m
  have hI : I ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  obtain ⟨a, ha, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  refine ⟨a, ha, ?_⟩
  intro v
  have hmap : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  have hcount := FractionalIdeal.count_mono K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hmap)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr haI)
  have he : FractionalIdeal.count K v I = D v :=
    FractionalIdeal.count_finsuppProd K v D
  rwa [he] at hcount

end MazurProof.N25F_DedekindPrincipalMajorant

namespace MazurProof.N25F_AffineNonpositiveRepresentative
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionPrincipalTransport
open N25F_DedekindPrincipalMajorant
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop := ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) := {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem isBoundary_iff (b : Boundary → C.Atom) (a : C.Atom) :
  IsBoundary C b a ↔ ∃ t, b t = a := Iff.rfl
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (ZMod 2) (FractionRing S)]
variable (principal : Additive ((FractionRing S)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing S)ˣ),
  (h.toMul : FractionRing S) = (f.toMul : FractionRing S) + (g.toMul : FractionRing S) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (hzero : ∀ f : Additive ((FractionRing S)ˣ), C.divisorDegree (principal f) = 0)
variable (boundaryAtom : Boundary → C.Atom)
variable (hbinj : Function.Injective boundaryAtom)
variable (hdegree : ∀ t, C.atomDegree (boundaryAtom t) = 1)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum S)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
variable (B : ℕ)
def basePoleDivisor : C.Divisor :=
  Finsupp.single (boundaryAtom .X) 1 + Finsupp.single (boundaryAtom .YZ) 1 +
    Finsupp.single (boundaryAtom .Z) 2
include hdegree in
theorem basePoleDivisor_degree : C.divisorDegree (basePoleDivisor C boundaryAtom) = 4 := by
  unfold basePoleDivisor
  rw [map_add, map_add]
  simp [ClosedPointGrading.divisorDegree, hdegree]
theorem basePoleDivisor_nonneg : 0 ≤ basePoleDivisor C boundaryAtom := by
  exact add_nonneg (add_nonneg (Finsupp.single_nonneg.mpr (by decide))
    (Finsupp.single_nonneg.mpr (by decide))) (Finsupp.single_nonneg.mpr (by decide))
private def affineHeightOnePart (D : C.Divisor) : IsDedekindDomain.HeightOneSpectrum S →₀ ℤ :=
  Finsupp.comapDomain (fun v => (e.symm v).1) D
    (Subtype.coe_injective.comp e.symm.injective).injOn

include haff in
/-- A real nonzero function dominates every affine coefficient of the given full divisor. -/
theorem exists_principal_affine_majorant25Two (D : C.Divisor) :
    ∃ f : Additive ((FractionRing S)ˣ), ∀ A : NonBoundary C boundaryAtom,
      D A.1 ≤ principal f A.1 := by
  obtain ⟨a, ha, hcount⟩ := exists_nonzero_regular_with_count_ge (K := (FractionRing S)) (affineHeightOnePart C S boundaryAtom e D)
  have hmap : algebraMap S (FractionRing S) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr ha
  let f : Additive ((FractionRing S)ˣ) := Additive.ofMul (Units.mk0 (algebraMap S (FractionRing S) a) hmap)
  refine ⟨f, ?_⟩
  intro A
  rw [haff f A]
  have h := hcount (e A)
  change (affineHeightOnePart C S boundaryAtom e D) (e A) ≤
    CurveDedekindDivisor.principalDivisor f (e A) at h
  simpa only [affineHeightOnePart C S boundaryAtom e, Finsupp.comapDomain_apply, Equiv.symm_apply_apply] using h

private def affinePrincipalShift (D : C.Divisor) : Additive ((FractionRing S)ˣ) :=
  Classical.choose (exists_principal_affine_majorant25Two C S principal boundaryAtom e haff D)

/-- The actual representative obtained by subtracting the constructed principal divisor. -/
def affineNonpositiveRepresentative25Two (D : C.Divisor) : C.Divisor :=
  D - principal (affinePrincipalShift C S principal boundaryAtom e haff D)

theorem affineNonpositiveRepresentative25Two_nonBoundary (D : C.Divisor)
    (A : NonBoundary C boundaryAtom) : affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D A.1 ≤ 0 := by
  exact sub_nonpos.mpr ((Classical.choose_spec (exists_principal_affine_majorant25Two C S principal boundaryAtom e haff D)) A)

include hzero in
/-- The genuine projective product formula preserves the full weighted degree. -/
theorem affineNonpositiveRepresentative25Two_degree (D : C.Divisor) :
    C.divisorDegree (affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D) =
      C.divisorDegree D := by
  rw [affineNonpositiveRepresentative25Two, map_sub, hzero, sub_zero]

theorem affineNonpositiveRepresentative25Two_classOf (D : C.Divisor) :
    C.classOf principal.range
      (affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D) =
    C.classOf principal.range D := by
  have hz : C.classOf principal.range
      (principal (affinePrincipalShift C S principal boundaryAtom e haff D)) = 0 := by
    apply QuotientAddGroup.eq_zero_iff.mpr
    exact ⟨affinePrincipalShift C S principal boundaryAtom e haff D, rfl⟩
  rw [affineNonpositiveRepresentative25Two, map_sub, hz, sub_zero]

theorem affineNonpositiveRepresentative25Two_finrank (D : C.Divisor) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin (affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D)) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) :=
  finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq C principal hmin _ _
    (affineNonpositiveRepresentative25Two_classOf C S principal boundaryAtom e haff D)

include hbinj in
/-- After the genuine principal shift, a multiple of H really dominates every coefficient. -/
theorem affineNonpositiveRepresentative25Two_le_basePole_multiple (D : C.Divisor) :
    ∃ n : ℕ, B ≤ n ∧
      ∀ A, affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D A ≤ ((n : ℤ) • (basePoleDivisor C boundaryAtom)) A := by
  classical
  let E := affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D
  let n := B + (E (boundaryAtom .X)).toNat +
    (E (boundaryAtom .YZ)).toNat + (E (boundaryAtom .Z)).toNat
  refine ⟨n, by omega, ?_⟩
  intro A
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : IsBoundary C boundaryAtom A
  · obtain ⟨t, rfl⟩ := (isBoundary_iff C boundaryAtom A).mp hA
    change E (boundaryAtom t) ≤ (n : ℤ) * (basePoleDivisor C boundaryAtom) (boundaryAtom t)
    cases t <;> simp only [basePoleDivisor, Finsupp.add_apply, Finsupp.single_apply,
      hbinj.eq_iff] <;> simp only [reduceCtorEq, ↓reduceIte, add_zero,
      zero_add, mul_one] <;> omega
  · have hnon := affineNonpositiveRepresentative25Two_nonBoundary C S principal boundaryAtom e haff D ⟨A, hA⟩
    have hpos : 0 ≤ (basePoleDivisor C boundaryAtom) A := by
      have h := basePoleDivisor_nonneg C boundaryAtom
      change ∀ a, 0 ≤ (basePoleDivisor C boundaryAtom) a at h
      exact h A
    exact hnon.trans (mul_nonneg (Int.natCast_nonneg n) hpos)

include hzero hdegree in
/-- Exact degree cost of imposing the effective complement after the shift. -/
theorem affineRepresentative_complement_degree (D : C.Divisor) (n : ℕ) :
    C.divisorDegree
      ((n : ℤ) • (basePoleDivisor C boundaryAtom) - affineNonpositiveRepresentative25Two C S principal boundaryAtom e haff D) =
      4 * (n : ℤ) - C.divisorDegree D := by
  rw [map_sub, map_zsmul, basePoleDivisor_degree C boundaryAtom hdegree, affineNonpositiveRepresentative25Two_degree C S principal hzero boundaryAtom e haff]
  simp only [zsmul_eq_mul, Int.cast_id, mul_comm]

#print axioms exists_principal_affine_majorant25Two
#print axioms affineNonpositiveRepresentative25Two
#print axioms affineNonpositiveRepresentative25Two_nonBoundary
#print axioms affineNonpositiveRepresentative25Two_degree
#print axioms affineNonpositiveRepresentative25Two_classOf
#print axioms affineNonpositiveRepresentative25Two_finrank
#print axioms affineNonpositiveRepresentative25Two_le_basePole_multiple
#print axioms affineRepresentative_complement_degree
end MazurProof.N25F_AffineNonpositiveRepresentative
