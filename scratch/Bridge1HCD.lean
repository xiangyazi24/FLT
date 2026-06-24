import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! # Bridge-1 coprimality, even case — foundation (hCD relation)

At a root of `Ψ₂Sq`, the EDS parameter `b = Ψ₂Sq² = 0`, and `preΨ' n = preNormEDS' 0 Ψ₃ preΨ₄ n`.
The even closed-forms need the on-`Ψ₂Sq`-root relation `preΨ₄² + 4·Ψ₃³ = 0`.

CAS-VERIFIED (sympy): `preΨ₄² + 4·Ψ₃³ = Q1·Ψ₂Sq + Q2·b_relation` exactly (remainder 0).
Cofactors have RATIONAL coefficients (denominators up to 4096) because dividing by `Ψ₂Sq`
(leading coeff 4) introduces powers of 4; `linear_combination` over a field handles this. -/

open Polynomial

namespace WeierstrassCurve
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

-- hCD: at a `Ψ₂Sq`-root, `preΨ₄² + 4·Ψ₃³ = 0`. CAS-verified identity, rational cofactor lift.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root {x : k} (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 + 4 * (W.Ψ₃.eval x) ^ 3 = 0 := by
  have hbrel : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by linear_combination -W.b_relation
  rw [WeierstrassCurve.Ψ₂Sq] at hs
  rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_ofNat, eval_one] at hs ⊢
  linear_combination (norm := ring_nf) (((28:k)*x^9
        + (21:k)*x^8*W.b₂
        + (4:k)*x^7*W.b₂^2
        + (72:k)*x^7*W.b₄
        + (28:k)*x^6*W.b₂*W.b₄
        + (84:k)*x^6*W.b₆
        + (131/4:k)*x^5*W.b₂*W.b₆
        + (205/4:k)*x^5*W.b₄^2
        + (37:k)*x^5*W.b₈
        - (3/16:k)*x^4*W.b₂^2*W.b₆
        + (3/16:k)*x^4*W.b₂*W.b₄^2
        + (59/4:k)*x^4*W.b₂*W.b₈
        + (126:k)*x^4*W.b₄*W.b₆
        + (3/64:k)*x^3*W.b₂^3*W.b₆
        - (3/64:k)*x^3*W.b₂^2*W.b₄^2
        - (3/16:k)*x^3*W.b₂^2*W.b₈
        - (11/8:k)*x^3*W.b₂*W.b₄*W.b₆
        + (11/8:k)*x^3*W.b₄^3
        + (123/2:k)*x^3*W.b₄*W.b₈
        + (84:k)*x^3*W.b₆^2
        - (3/256:k)*x^2*W.b₂^4*W.b₆
        + (3/256:k)*x^2*W.b₂^3*W.b₄^2
        + (3/64:k)*x^2*W.b₂^3*W.b₈
        + (7/16:k)*x^2*W.b₂^2*W.b₄*W.b₆
        - (7/16:k)*x^2*W.b₂*W.b₄^3
        - (7/4:k)*x^2*W.b₂*W.b₄*W.b₈
        - (43/16:k)*x^2*W.b₂*W.b₆^2
        + (43/16:k)*x^2*W.b₄^2*W.b₆
        + (379/4:k)*x^2*W.b₆*W.b₈
        + (3/1024:k)*x*W.b₂^5*W.b₆
        - (3/1024:k)*x*W.b₂^4*W.b₄^2
        - (3/256:k)*x*W.b₂^4*W.b₈
        - (17/128:k)*x*W.b₂^3*W.b₄*W.b₆
        + (17/128:k)*x*W.b₂^2*W.b₄^3
        + (17/32:k)*x*W.b₂^2*W.b₄*W.b₈
        + (23/32:k)*x*W.b₂^2*W.b₆^2
        - (1/32:k)*x*W.b₂*W.b₄^2*W.b₆
        - (35/8:k)*x*W.b₂*W.b₆*W.b₈
        - (11/16:k)*x*W.b₄^4
        - (5/4:k)*x*W.b₄^2*W.b₈
        + (34:k)*x*W.b₈^2
        - (3/4096:k)*W.b₂^6*W.b₆
        + (3/4096:k)*W.b₂^5*W.b₄^2
        + (3/1024:k)*W.b₂^5*W.b₈
        + (5/128:k)*W.b₂^4*W.b₄*W.b₆
        - (5/128:k)*W.b₂^3*W.b₄^3
        - (5/32:k)*W.b₂^3*W.b₄*W.b₈
        - (49/256:k)*W.b₂^3*W.b₆^2
        - (51/256:k)*W.b₂^2*W.b₄^2*W.b₆
        + (73/64:k)*W.b₂^2*W.b₆*W.b₈
        + (25/64:k)*W.b₂*W.b₄^4
        + (19/16:k)*W.b₂*W.b₄^2*W.b₈
        + (27/16:k)*W.b₂*W.b₄*W.b₆^2
        - (1/2:k)*W.b₂*W.b₈^2
        - (27/16:k)*W.b₄^3*W.b₆
        - (35/4:k)*W.b₄*W.b₆*W.b₈
        + W.b₆^3)) * hs + (((3/4096:k)*x^2*W.b₂^6
        - (23/512:k)*x^2*W.b₂^4*W.b₄
        + (13/64:k)*x^2*W.b₂^3*W.b₆
        + (21/32:k)*x^2*W.b₂^2*W.b₄^2
        - (3/8:k)*x^2*W.b₂^2*W.b₈
        - (57/16:k)*x^2*W.b₂*W.b₄*W.b₆
        - (11/8:k)*x^2*W.b₄^3
        + (3:k)*x^2*W.b₄*W.b₈
        + (27/16:k)*x^2*W.b₆^2
        + (3/2048:k)*x*W.b₂^5*W.b₄
        - (3/1024:k)*x*W.b₂^4*W.b₆
        - (5/64:k)*x*W.b₂^3*W.b₄^2
        + (33/64:k)*x*W.b₂^2*W.b₄*W.b₆
        + (25/32:k)*x*W.b₂*W.b₄^3
        - (3/4:k)*x*W.b₂*W.b₄*W.b₈
        - (23/32:k)*x*W.b₂*W.b₆^2
        - (65/16:k)*x*W.b₄^2*W.b₆
        - (1/2:k)*x*W.b₆*W.b₈
        + (3/4096:k)*W.b₂^5*W.b₆
        - (5/128:k)*W.b₂^3*W.b₄*W.b₆
        + (49/256:k)*W.b₂^2*W.b₆^2
        + (25/64:k)*W.b₂*W.b₄^2*W.b₆
        - (3/8:k)*W.b₂*W.b₆*W.b₈
        - (27/16:k)*W.b₄*W.b₆^2
        - W.b₈^2)) * hbrel

end WeierstrassCurve
