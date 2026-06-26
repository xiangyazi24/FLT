# Q845 (dm1): `preΨ₄ = -Ψ₂Sq²` at a root of `Ψ₃`

Here is the Lean proof.  It works over any `CommRing`, so it also works in the field case.  I avoid the final `linarith`: over an arbitrary field/ring there is no order, and the algebraic rearrangement is better done by `ring`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [CommRing K]

/-- The polynomial identity behind the `Ψ₃ = 0` specialization. -/
theorem preΨ₄_add_Ψ₂Sq_sq_eq_mul_Ψ₃ (W : WeierstrassCurve K) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  unfold preΨ₄ Ψ₂Sq Ψ₃ b₂ b₄ b₆ b₈
  ring

/-- At a root of `Ψ₃`, one has `preΨ₄ = -Ψ₂Sq²`. -/
theorem preΨ₄_eq_neg_Ψ₂Sq_sq_at_Ψ₃_root (W : WeierstrassCurve K) {x : K}
    (hΨ₃ : (W.Ψ₃).eval x = 0) :
    (W.preΨ₄).eval x = -(W.Ψ₂Sq.eval x) ^ 2 := by
  have hid := preΨ₄_add_Ψ₂Sq_sq_eq_mul_Ψ₃ (W := W)
  have hEval : (W.preΨ₄).eval x + (W.Ψ₂Sq.eval x) ^ 2 = 0 := by
    have h := congrArg (fun p : K[X] => p.eval x) hid
    simpa [hΨ₃] using h
  calc
    (W.preΨ₄).eval x
        = (W.preΨ₄).eval x + (W.Ψ₂Sq.eval x) ^ 2 - (W.Ψ₂Sq.eval x) ^ 2 := by
          ring
    _ = 0 - (W.Ψ₂Sq.eval x) ^ 2 := by
          rw [hEval]
    _ = -(W.Ψ₂Sq.eval x) ^ 2 := by
          ring

end WeierstrassCurve
```

A slightly shorter ending also works if you prefer the additive-group lemma style:

```lean
  exact eq_neg_of_add_eq_zero_right hEval
```

in place of the final `calc` block, provided that lemma name is available in the imported environment.  The `calc` version above is more self-contained.
