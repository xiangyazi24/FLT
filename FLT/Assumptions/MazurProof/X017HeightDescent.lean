import Mathlib.GroupTheory.Descent

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

variable {G : Type*} [AddCommGroup G]

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

end MazurProof.X017HeightDescent
