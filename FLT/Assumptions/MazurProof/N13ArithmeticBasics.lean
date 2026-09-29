import FLT.Assumptions.MazurProof.N13CurveModel
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N13Arithmetic

/-- The sextic is a norm from the quadratic extension obtained by adjoining i. -/
theorem sexticF13_norm_identity (x : ℚ) :
    N13CurveModel.sexticF13 x =
      (x ^ 3 + 2 * x ^ 2 - x - 1) ^ 2 +
        4 * (x * (x + 1)) ^ 2 := by
  unfold N13CurveModel.sexticF13
  ring

/-- In particular, no rational affine point is a hyperelliptic branch point. -/
theorem sexticF13_pos (x : ℚ) :
    0 < N13CurveModel.sexticF13 x := by
  by_cases h : x * (x + 1) = 0
  · rcases mul_eq_zero.mp h with hx | hx
    · subst x
      norm_num [N13CurveModel.sexticF13]
    · have hx' : x = -1 := by linarith
      rw [hx']
      norm_num [N13CurveModel.sexticF13]
  · rw [sexticF13_norm_identity]
    have hA : 0 ≤ (x ^ 3 + 2 * x ^ 2 - x - 1) ^ 2 :=
      sq_nonneg _
    have hB : 0 < (x * (x + 1)) ^ 2 :=
      sq_pos_of_ne_zero h
    nlinarith

end MazurProof.N13Arithmetic
