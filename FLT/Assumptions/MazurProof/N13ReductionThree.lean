import FLT.Assumptions.MazurProof.N13Mumford

/-!
# The N13 sextic over `F₃`

The reduction of the N13 sextic has four affine points.  The proof uses the
Frobenius identity `t³ = t` in `F₃`, rather than enumerating pairs of field
elements.
-/

namespace MazurProof.N13ReductionThree

abbrev F3 := ZMod 3

/-- The reduction modulo three of the N13 sextic. -/
def sextic (x : F3) : F3 :=
  x ^ 6 + x ^ 5 + 2 * x ^ 3 + x ^ 2 + 2 * x + 1

/-- The affine `F₃`-points of the reduced N13 model. -/
def IsAffinePoint (x y : F3) : Prop := y ^ 2 = sextic x

private theorem cube_eq (x : F3) : x ^ 3 = x :=
  ZMod.pow_card x

private theorem pow_four_eq_sq (x : F3) : x ^ 4 = x ^ 2 := by
  calc
    x ^ 4 = x * x ^ 3 := by ring
    _ = x * x := by rw [cube_eq]
    _ = x ^ 2 := by ring

private theorem pow_five_eq (x : F3) : x ^ 5 = x := by
  calc
    x ^ 5 = x ^ 2 * x ^ 3 := by ring
    _ = x ^ 2 * x := by rw [cube_eq]
    _ = x ^ 3 := by ring
    _ = x := cube_eq x

private theorem pow_six_eq_sq (x : F3) : x ^ 6 = x ^ 2 := by
  calc
    x ^ 6 = (x ^ 3) ^ 2 := by ring
    _ = x ^ 2 := by rw [cube_eq]

/-- A compact form of the reduced sextic, valid on all `F₃`-points. -/
theorem sextic_eq_one_sub_mul (x : F3) :
    sextic x = 1 - x * (x + 1) := by
  rw [sextic, pow_six_eq_sq, pow_five_eq, cube_eq]
  have hthree : (3 : F3) = 0 := by decide
  linear_combination (x ^ 2 + 2 * x) * hthree

private theorem sextic_ne_zero (x : F3) : sextic x ≠ 0 := by
  intro h
  have hq : x ^ 2 + x - 1 = 0 := by
    rw [sextic_eq_one_sub_mul] at h
    linear_combination -h
  have hc : x ^ 3 - x = 0 := by rw [cube_eq]; ring
  have hx : x = 1 := by
    linear_combination hc - x * hq + hq
  norm_num [hx] at hq

private theorem square_eq_one_of_ne_zero {y : F3} (hy : y ≠ 0) : y ^ 2 = 1 := by
  simpa using (ZMod.pow_card_sub_one_eq_one hy)

/-- The four affine points of the N13 sextic over `F₃`, in structural form. -/
theorem isAffinePoint_iff (x y : F3) :
    IsAffinePoint x y ↔
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  constructor
  · intro h
    change y ^ 2 = sextic x at h
    have hy : y ≠ 0 := by
      intro hy
      exact sextic_ne_zero x (by simpa [hy] using h.symm)
    have hy2 := square_eq_one_of_ne_zero hy
    have hxprod : x * (x + 1) = 0 := by
      rw [sextic_eq_one_sub_mul] at h
      linear_combination h - hy2
    have hyfac : (y - 1) * (y + 1) = 0 := by
      calc
        (y - 1) * (y + 1) = y ^ 2 - 1 := by ring
        _ = 0 := by rw [hy2]; norm_num
    have hycases : y = 1 ∨ y = -1 := by
      rcases mul_eq_zero.mp hyfac with h1 | h2
      · left; exact sub_eq_zero.mp h1
      · right; exact eq_neg_of_add_eq_zero_left h2
    rcases mul_eq_zero.mp hxprod with hx | hx
    · exact Or.inl ⟨hx, hycases⟩
    · right
      refine ⟨?_, hycases⟩
      exact eq_neg_of_add_eq_zero_left hx
  · rintro (⟨rfl, hy⟩ | ⟨rfl, hy⟩) <;>
      rcases hy with rfl | rfl <;>
      norm_num [IsAffinePoint, sextic]
    all_goals
      have hthree : (3 : F3) = 0 := by decide
      linear_combination hthree

/-- The affine reduced curve has exactly four rational points. -/
theorem affine_points_are_four (x y : F3) (h : IsAffinePoint x y) :
    (x, y) = (0, 1) ∨ (x, y) = (0, -1) ∨
      (x, y) = (-1, 1) ∨ (x, y) = (-1, -1) := by
  rcases isAffinePoint_iff x y |>.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    rcases hy with hy | hy <;> subst x <;> subst y <;> simp

end MazurProof.N13ReductionThree
