import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Logic.Equiv.Option
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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


namespace MazurProof.N25F_BoundarySectionFiltration
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness N25F_BinaryResidueCancellation
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (C : ClosedPointGrading) (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ, (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
 min (principal f A) (principal g A) ≤ principal h A)
variable (P : C.Atom)
variable (hcancel : ∀ a b : L, ∀ (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b),
 principal (Additive.ofMul (Units.mk0 a ha)) P = principal (Additive.ofMul (Units.mk0 b hb)) P →
 principal (Additive.ofMul (Units.mk0 b hb)) P < principal (Additive.ofMul (Units.mk0 (a-b) (sub_ne_zero.mpr hab))) P)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
theorem fullRiemannRochSpace25Two_mono {D E : C.Divisor} (h : D ≤ E) :
 fullRiemannRochSpace25Two C principal hmin D ≤ fullRiemannRochSpace25Two C principal hmin E := by
 intro f hf
 rcases hf with hz | ⟨hn,hf⟩
 · exact Or.inl hz
 · refine Or.inr ⟨hn, ?_⟩
   intro A
   have ha := h A
   have hb := hf A
   omega
private theorem unit_mk0_eq (f : Additive Lˣ) (hf : (f.toMul : L) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : L) hf) = f := by
  apply Additive.toMul.injective
  exact Units.ext rfl

theorem fullRiemannRochSpace25Two_sub_boundary_le (D : C.Divisor)  :
    fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1) ≤
      fullRiemannRochSpace25Two C principal hmin D := by
  classical
  apply fullRiemannRochSpace25Two_mono C principal hmin
  intro A
  by_cases hA : A = P
  · subst A
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
    omega
  · simp [hA, Ne.symm hA]

theorem mem_fullRiemannRochSpace25Two_sub_boundary_iff (D : C.Divisor)
     (f : Additive Lˣ)
    (hf : (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin D) :
    (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1) ↔
      -D P < principal f P := by
  classical
  have hb : ∀ A, 0 ≤ D A + principal f A := by
    rcases hf with h | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero h).elim
    simpa only [unit_mk0_eq f hf0] using hb
  constructor
  · intro hs
    rcases hs with h | ⟨hf0, hs⟩
    · exact (f.toMul.ne_zero h).elim
    have hp := hs P
    rw [unit_mk0_eq f hf0, Finsupp.sub_apply, Finsupp.single_eq_same] at hp
    omega
  · intro hp
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = P
    · subst A
      rw [Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · simpa [hA, Ne.symm hA] using hb A

theorem boundary_principal_eq_neg_of_not_mem (D : C.Divisor)
     (f : Additive Lˣ)
    (hf : (f.toMul : L) ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hnot : (f.toMul : L) ∉ fullRiemannRochSpace25Two C principal hmin
      (D - Finsupp.single P 1)) :
    principal f P = -D P := by
  have hn := mt (mem_fullRiemannRochSpace25Two_sub_boundary_iff C principal hmin P D f hf).mpr hnot
  rcases hf with h | ⟨hf0, hb⟩
  · exact (f.toMul.ne_zero h).elim
  have hp := hb P
  rw [unit_mk0_eq f hf0] at hp
  omega

include hcancel in
theorem sub_mem_fullRiemannRochSpace25Two_sub_boundary (D : C.Divisor)
     (a b : L) (ha : a ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hb : b ∈ fullRiemannRochSpace25Two C principal hmin D)
    (hanot : a ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1))
    (hbnot : b ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1)) :
    a - b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1) := by
  by_cases hab : a = b
  · rw [hab, sub_self]
    exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have ha0 : a ≠ 0 := by intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have hb0 : b ≠ 0 := by intro h; apply hbnot; rw [h]; exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have hpa := boundary_principal_eq_neg_of_not_mem C principal hmin P D (Additive.ofMul (Units.mk0 a ha0)) ha hanot
  have hpb := boundary_principal_eq_neg_of_not_mem C principal hmin P D (Additive.ofMul (Units.mk0 b hb0)) hb hbnot
  have hp := hcancel a b ha0 hb0 hab (hpa.trans hpb.symm)
  apply (mem_fullRiemannRochSpace25Two_sub_boundary_iff C principal hmin P D
    (Additive.ofMul (Units.mk0 (a - b) (sub_ne_zero.mpr hab)))
    ((fullRiemannRochSpace25Two C principal hmin D).sub_mem ha hb)).mpr
  omega

/- Each actual binary boundary condition costs at most one dimension. -/
include hcancel hzero hinj in
theorem finrank_fullRiemannRochSpace25Two_le_sub_boundary_add_one
    (D : C.Divisor)  :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) ≤
      Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1)) + 1 := by
  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj (D - Finsupp.single P 1)
  by_cases hle : fullRiemannRochSpace25Two C principal hmin D ≤
      fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1)
  · exact (Submodule.finrank_mono hle).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, hanot⟩ := SetLike.not_le_iff_exists.mp hle
  have ha0 : a ≠ 0 := by intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two C principal hmin _).zero_mem
  have he : fullRiemannRochSpace25Two C principal hmin D =
      fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set L) := by
    apply le_antisymm
    · intro b hb
      by_cases hbn : b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1)
      · exact Submodule.mem_sup_left hbn
      have hba := sub_mem_fullRiemannRochSpace25Two_sub_boundary C principal hmin P hcancel D b a hb ha hbn hanot
      have haS : a ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1) ⊔
          Submodule.span (ZMod 2) ({a} : Set L) :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton a))
      simpa only [sub_add_cancel] using (Submodule.add_mem _ (Submodule.mem_sup_left hba) haS)
    · refine sup_le (fullRiemannRochSpace25Two_sub_boundary_le C principal hmin P D) ?_
      apply Submodule.span_le.mpr
      intro b hb
      have hba : b = a := Set.mem_singleton_iff.mp hb
      subst b
      exact ha
  rw [he]
  simpa only [finrank_span_singleton ha0] using
    (Submodule.finrank_add_le_finrank_add_finrank
      (fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single P 1))
      (Submodule.span (ZMod 2) ({a} : Set L)))

/- A multiplicity-k constraint at any of the three actual boundary points costs at most k. -/
include hcancel hzero hinj in
theorem finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple
    (D : C.Divisor)  (k : ℕ) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin
        (D - (k : ℤ) • Finsupp.single P 1)) + k := by
  induction k generalizing D with
  | zero =>
      have hz : ((0 : ℕ) : ℤ) • Finsupp.single P (1 : ℤ) = 0 := by
        ext A
        simp [Finsupp.smul_apply]
      rw [hz, sub_zero, add_zero]
  | succ k ih =>
      have hstep := finrank_fullRiemannRochSpace25Two_le_sub_boundary_add_one C principal hmin P hcancel hzero hinj D
      have hrec := ih (D - Finsupp.single P 1)
      have he : Finsupp.single P (1 : ℤ) +
          (k : ℤ) • Finsupp.single P 1 =
          ((k + 1 : ℕ) : ℤ) • Finsupp.single P 1 := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]
      rw [sub_sub, he] at hrec
      omega


variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
variable (hcoeff : ∀ f : Additive Lˣ, principal f P = WithZero.log (Ring.ordFrac R (f.toMul : L)))
include e hcoeff in
theorem boundary_cancellation_from_DVR
    (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : principal (Additive.ofMul (Units.mk0 a ha)) P = principal (Additive.ofMul (Units.mk0 b hb)) P) :
    principal (Additive.ofMul (Units.mk0 b hb)) P <
      principal (Additive.ofMul (Units.mk0 (a-b) (sub_ne_zero.mpr hab))) P := by
  simp only [hcoeff] at h ⊢
  exact log_ordFrac_sub_gt_of_log_eq e a b ha hb hab h

include e hcoeff hzero hinj in
theorem boundary_multiplicity_cost_from_DVR (D : C.Divisor) (k : ℕ) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin D) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two C principal hmin
        (D - (k : ℤ) • Finsupp.single P 1)) + k := by
  exact finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple C principal hmin P
    (boundary_cancellation_from_DVR C principal P R e hcoeff) hzero hinj D k

#print axioms boundary_cancellation_from_DVR
#print axioms boundary_multiplicity_cost_from_DVR
#print axioms fullRiemannRochSpace25Two_sub_boundary_le
#print axioms mem_fullRiemannRochSpace25Two_sub_boundary_iff
#print axioms boundary_principal_eq_neg_of_not_mem
#print axioms sub_mem_fullRiemannRochSpace25Two_sub_boundary
#print axioms finrank_fullRiemannRochSpace25Two_le_sub_boundary_add_one
#print axioms finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple
end MazurProof.N25F_BoundarySectionFiltration
