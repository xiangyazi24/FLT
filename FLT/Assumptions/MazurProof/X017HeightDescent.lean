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

end MazurProof.X017HeightDescent
