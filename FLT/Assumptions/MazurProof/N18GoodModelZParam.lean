import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic

/-!
# Formal parameter `z = -x/y` on the good model E0Good

Tier 2a of the no_five_descent_solution campaign (Fable plan).
-/

namespace MazurProof.N18RouteC.GoodModel

open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic

noncomputable section

/-- Formal parameter `z = -x/y` of a point on E0Good. -/
def zParamGood : E0GoodPoint → L
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zParamGood_zero : zParamGood (0 : E0GoodPoint) = 0 := rfl

@[simp] theorem zParamGood_some (x y : L)
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) :
    zParamGood (.some x y h) = -x / y := rfl

/-- z = 0 only at the origin. -/
theorem zParamGood_eq_zero {P : E0GoodPoint} (hz : zParamGood P = 0) : P = 0 := by
  rcases P with _ | ⟨x, y, hns⟩
  · rfl
  · simp [zParamGood] at hz
    -- hz : -x / y = 0, so x = 0
    rcases div_eq_zero_iff.mp hz with hx | hy
    · -- x = 0: check if (0, y) is on E0Good
      rw [neg_eq_zero] at hx
      exfalso
      have heq := (WeierstrassCurve.Affine.equation_iff 0 y).mp hns.1
      simp only [E0Good, zero_pow, mul_zero, add_zero, zero_mul] at heq
      -- heq says y² + (a₃)y = a₆, a specific equation in y
      -- Need to show no solution exists — this is curve-specific
      sorry
    · -- y = 0: similar
      sorry

end

end MazurProof.N18RouteC.GoodModel
