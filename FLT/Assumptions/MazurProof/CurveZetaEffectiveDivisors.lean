import Mathlib

/-!
# Effective divisors from locally finite graded closed points

Closed points of a curve form an infinite set, but there are only finitely
many of each positive degree.  This module encodes that exact local-finiteness
condition and constructs effective divisors as finite multiplicity functions.

The main result is that effective divisors of any fixed total degree form a
finite type.  The proof is structural: a degree-`n` divisor is supported on
closed points of degree at most `n`, and every multiplicity is at most `n`.
No divisor or curve point is enumerated.
-/

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

/-- The number of effective divisors of degree `n`. -/
noncomputable def effectiveCount (n : ℕ) : ℕ := Nat.card (C.EffDivOfDegree n)

/-- An effective divisor of degree zero is the zero divisor. -/
theorem eq_zero_of_divDegree_eq_zero (D : C.EffDiv)
    (hdegree : C.divDegree D = 0) : D = 0 := by
  ext x
  have hterm : D x * C.atomDegree x = 0 := by
    exact Nat.eq_zero_of_le_zero (hdegree ▸ C.term_le_divDegree D x)
  exact (Nat.mul_eq_zero.mp hterm).resolve_right (C.atomDegree_pos x).ne'

/-- There is exactly one degree-zero effective divisor. -/
@[simp]
theorem effectiveCount_zero : C.effectiveCount 0 = 1 := by
  letI := Fintype.ofFinite (C.EffDivOfDegree 0)
  rw [effectiveCount, Nat.card_eq_fintype_card]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, C.divDegree_zero⟩, ?_⟩
  intro D
  apply Subtype.ext
  exact C.eq_zero_of_divDegree_eq_zero D.1 D.2

end ClosedPointGrading

end MazurProof.CurveZetaEffectiveDivisors
