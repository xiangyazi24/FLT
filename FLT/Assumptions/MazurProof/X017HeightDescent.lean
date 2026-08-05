import Mathlib.GroupTheory.Descent
import FLT.Assumptions.MazurProof.X017ExactSequence

/-!
# A two-coset height descent

Mathlib's general descent theorem proves finite generation from a finite set of
representatives modulo an endomorphism and compatible height inequalities.
For the standard `X₀(17)` model, the quotient modulo doubling is expected to
have the two representatives zero and the visible order-four point.  This
specialization shows that only one nontrivial translation estimate is needed.
-/

open scoped Pointwise

namespace MazurProof.X017HeightDescent

open MazurProof.X017ExactSequence

variable {G : Type*} [AddCommGroup G]

/-- A two-coset exhaustion for doubling is exactly the representative-set
cover required by the height descent theorem. -/
theorem twoCosetExhaustion_set_cover
    (T : G)
    (hrep :
      TwoCosetExhaustion (nsmulAddMonoidHom (α := G) 2) T) :
    ({0, T} : Set G) +
        ((nsmulAddMonoidHom (α := G) 2).range : Set G) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨g, hx | hx⟩ := hrep x
  · apply Set.mem_add.mpr
    exact ⟨0, by simp, 2 • g, ⟨g, rfl⟩, by simpa using hx.symm⟩
  · apply Set.mem_add.mpr
    exact ⟨T, by simp, 2 • g, ⟨g, rfl⟩, hx.symm⟩

/-- A height descent with representatives `{0,T}` modulo doubling.  The zero
representative follows from nonnegativity of the height, while the only
curve-specific translation estimate is the one for the fixed point `T`. -/
theorem fg_of_fixed_two_coset_height
    (T : G) (h : G → ℝ) [Northcott h]
    (C : ℝ) (hC : 0 ≤ C)
    (hcover :
      ({0, T} : Set G) +
          ((nsmulAddMonoidHom (α := G) 2).range : Set G) = Set.univ)
    (hnonneg : ∀ x, 0 ≤ h x)
    (htranslate : ∀ x, h x ≤ 2 * h (T + x) + C)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x)) :
    AddGroup.FG G := by
  apply AddGroup.fg_of_descent
    (f := nsmulAddMonoidHom (α := G) 2)
    (s := ({0, T} : Set G))
    (h := h) (a := 2) (b := 4) (c := C)
  · intro U x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using U.nsmul_mem hy 2
  · norm_num
  · norm_num
  · simp
  · exact hcover
  · intro g hg x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · simp only [zero_add]
      nlinarith [hnonneg x, hC]
    · exact htranslate x
  · intro x
    simpa using hdouble x

/-- The consumable form takes the same two-coset witness used by the sharpened
exact sequence, rather than asking the geometric layer to restate it as a
pointwise sumset equality. -/
theorem fg_of_fixed_two_coset_height_of_exhaustion
    (T : G) (h : G → ℝ) [Northcott h]
    (C : ℝ) (hC : 0 ≤ C)
    (hrep :
      TwoCosetExhaustion (nsmulAddMonoidHom (α := G) 2) T)
    (hnonneg : ∀ x, 0 ≤ h x)
    (htranslate : ∀ x, h x ≤ 2 * h (T + x) + C)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x)) :
    AddGroup.FG G :=
  fg_of_fixed_two_coset_height T h C hC
    (twoCosetExhaustion_set_cover T hrep)
    hnonneg htranslate hdouble

/-! ## Removing the fixed-translation estimate by orbit symmetrization -/

/-- Sum a height over the four translates by a point of order dividing four.
For the visible point on `X₀(17)`, this replaces a coordinate-wise translation
estimate by an exactly translation-invariant height. -/
def fourOrbitHeight (T : G) (h : G → ℝ) (x : G) : ℝ :=
  h x + h (T + x) + h (2 • T + x) + h (3 • T + x)

/-- The four-orbit height is invariant under translation by `T` when
`4 • T = 0`; translation merely cyclically permutes its four summands. -/
theorem fourOrbitHeight_add_left
    (T : G) (h : G → ℝ) (hT : 4 • T = 0) (x : G) :
    fourOrbitHeight T h (T + x) = fourOrbitHeight T h x := by
  simp only [fourOrbitHeight]
  have hTT : T + T = 2 • T := by simp [two_nsmul]
  have hT2T : T + 2 • T = 3 • T := by
    rw [show (3 : ℕ) = 1 + 2 by norm_num, add_nsmul, one_nsmul]
  have hT3T : T + 3 • T = 0 := by
    rw [show (4 : ℕ) = 1 + 3 by norm_num, add_nsmul, one_nsmul] at hT
    exact hT
  have h2TT : 2 • T + (T + x) = 3 • T + x := by
    calc
      2 • T + (T + x) = (T + 2 • T) + x := by abel
      _ = 3 • T + x := by rw [hT2T]
  have h3TT : 3 • T + (T + x) = x := by
    calc
      3 • T + (T + x) = (T + 3 • T) + x := by abel
      _ = x := by rw [hT3T, zero_add]
  rw [← add_assoc T T x, hTT, h2TT, h3TT]
  ring

/-- A nonnegative base height gives a nonnegative four-orbit height. -/
theorem fourOrbitHeight_nonneg
    (T : G) (h : G → ℝ) (hnonneg : ∀ x, 0 ≤ h x) (x : G) :
    0 ≤ fourOrbitHeight T h x := by
  simp only [fourOrbitHeight]
  have h0 := hnonneg x
  have h1 := hnonneg (T + x)
  have h2 := hnonneg (2 • T + x)
  have h3 := hnonneg (3 • T + x)
  linarith

/-- Northcott finiteness passes to the four-orbit height because its first
summand is the base height and all remaining summands are nonnegative. -/
theorem fourOrbitHeight_northcott
    (T : G) (h : G → ℝ) [Northcott h]
    (hnonneg : ∀ x, 0 ≤ h x) :
    Northcott (fourOrbitHeight T h) where
  finite_le B := by
    refine (Northcott.finite_le (h := h) B).subset ?_
    intro x hx
    have hT1 := hnonneg (T + x)
    have hT2 := hnonneg (2 • T + x)
    have hT3 := hnonneg (3 • T + x)
    simp only [Set.mem_setOf_eq, fourOrbitHeight] at hx ⊢
    linarith

/-- If doubling expands the base height by a factor four, then it expands the
four-orbit height by a factor two.  Doubling identifies opposite translates
in the order-four orbit, while the two unused target summands are
nonnegative. -/
theorem fourOrbitHeight_double_lower
    (T : G) (h : G → ℝ) (C : ℝ)
    (hT : 4 • T = 0)
    (hnonneg : ∀ x, 0 ≤ h x)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x))
    (x : G) :
    2 * fourOrbitHeight T h x - 2 * C ≤
      fourOrbitHeight T h (2 • x) := by
  have h0 := hdouble x
  have h1 := hdouble (T + x)
  have h2 := hdouble (2 • T + x)
  have h3 := hdouble (3 • T + x)
  have hodd1 := hnonneg (T + 2 • x)
  have hodd3 := hnonneg (3 • T + 2 • x)
  have h2T : 2 • (T + x) = 2 • T + 2 • x := by
    rw [nsmul_add]
  have h4T : 2 • (2 • T + x) = 2 • x := by
    rw [nsmul_add, ← mul_nsmul, show 2 * 2 = 4 by norm_num, hT, zero_add]
  have h6T : 2 • (3 • T + x) = 2 • T + 2 • x := by
    rw [nsmul_add, ← mul_nsmul]
    have h6 : 6 • T = 2 • T := by
      rw [show (6 : ℕ) = 4 + 2 by norm_num, add_nsmul, hT, zero_add]
    rw [h6]
  rw [h2T] at h1
  rw [h4T] at h2
  rw [h6T] at h3
  simp only [fourOrbitHeight]
  linarith

/-- A two-coset cover and the standard duplication bound imply finite
generation without any separate formula for translation by `T`.  The descent
uses expansion constants `a = 1` and `b = 2` for the symmetrized height. -/
theorem fg_of_fourOrbitHeight
    (T : G) (h : G → ℝ) [Northcott h]
    (C : ℝ) (hC : 0 ≤ C)
    (hT : 4 • T = 0)
    (hrep :
      TwoCosetExhaustion (nsmulAddMonoidHom (α := G) 2) T)
    (hnonneg : ∀ x, 0 ≤ h x)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x)) :
    AddGroup.FG G := by
  let H : G → ℝ := fourOrbitHeight T h
  letI : Northcott H := fourOrbitHeight_northcott T h hnonneg
  apply AddGroup.fg_of_descent
    (f := nsmulAddMonoidHom (α := G) 2)
    (s := ({0, T} : Set G))
    (h := H) (a := 1) (b := 2) (c := 2 * C)
  · intro U x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using U.nsmul_mem hy 2
  · norm_num
  · norm_num
  · simp
  · exact twoCosetExhaustion_set_cover T hrep
  · intro g hg x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      dsimp [H]
      simp only [zero_add, one_mul]
      linarith
    · rw [hg]
      dsimp [H]
      rw [one_mul, fourOrbitHeight_add_left T h hT x]
      linarith
  · intro x
    dsimp [H]
    exact fourOrbitHeight_double_lower T h C hT hnonneg hdouble x

end MazurProof.X017HeightDescent
