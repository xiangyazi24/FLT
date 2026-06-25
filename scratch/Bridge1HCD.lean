module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Tactic.LinearCombination

/-! # Bridge-1 coprimality, even case — foundation (hCD relation)

At a root of `Ψ₂Sq`, the EDS parameter `b = Ψ₂Sq² = 0`, and `preΨ' n = preNormEDS' 0 Ψ₃ preΨ₄ n`.
The even closed-forms need the on-`Ψ₂Sq`-root relation `preΨ₄² + 4·Ψ₃³ = 0`.

CAS-VERIFIED (sympy): `preΨ₄² + 4·Ψ₃³ = A·Ψ₂Sq + B·b_relation` with INTEGER cofactors A, B
(remainder 0 over ℤ), so the `linear_combination` closes over every field `k` incl. char 2/3. -/

open Polynomial

namespace WeierstrassCurve
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

set_option maxRecDepth 16000 in
-- large integer cofactor  needs more heartbeats
set_option maxHeartbeats 4000000 in
/-- hCD: at a `Ψ₂Sq`-root, `preΨ₄² + 4·Ψ₃³ = 0`. CAS-verified, integer cofactor lift. -/
public lemma preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root {x : k} (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 + 4 * (W.Ψ₃.eval x) ^ 3 = 0 := by
  have hbrel : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by linear_combination -W.b_relation
  rw [WeierstrassCurve.Ψ₂Sq] at hs
  rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_ofNat] at hs ⊢
  linear_combination ((W.b₆^3
        - (6:k)*W.b₄*W.b₆*W.b₈
        - W.b₄^3*W.b₆
        - (19:k)*W.b₂*W.b₈^2
        + W.b₂*W.b₄*W.b₆^2
        - (5:k)*W.b₂*W.b₄^2*W.b₈
        - (35:k)*W.b₂^2*W.b₆*W.b₈
        - (10:k)*W.b₂^2*W.b₄^2*W.b₆
        + (10:k)*W.b₂^3*W.b₆^2
        + (120:k)*x*W.b₈^2
        + (23:k)*x*W.b₄^2*W.b₈
        + (145:k)*x*W.b₂*W.b₆*W.b₈
        + (42:k)*x*W.b₂*W.b₄^2*W.b₆
        - (42:k)*x*W.b₂^2*W.b₆^2
        + (96:k)*x^2*W.b₆*W.b₈
        + (3:k)*x^2*W.b₄^2*W.b₆
        - (3:k)*x^2*W.b₂*W.b₆^2
        + (84:k)*x^3*W.b₆^2
        + (60:k)*x^3*W.b₄*W.b₈
        + x^3*W.b₄^3
        - x^3*W.b₂*W.b₄*W.b₆
        + (126:k)*x^4*W.b₄*W.b₆
        + (14:k)*x^4*W.b₂*W.b₈
        + (40:k)*x^5*W.b₈
        + (52:k)*x^5*W.b₄^2
        + (32:k)*x^5*W.b₂*W.b₆
        + (84:k)*x^6*W.b₆
        + (28:k)*x^6*W.b₂*W.b₄
        + (72:k)*x^7*W.b₄
        + (4:k)*x^7*W.b₂^2
        + (21:k)*x^8*W.b₂
        + (28:k)*x^9)) * hs + ((-W.b₈^2
        - W.b₄*W.b₆^2
        - (5:k)*W.b₂*W.b₆*W.b₈
        - (10:k)*W.b₂^2*W.b₆^2
        + (21:k)*x*W.b₆*W.b₈
        - (2:k)*x*W.b₄^2*W.b₆
        + (42:k)*x*W.b₂*W.b₆^2
        - (10:k)*x*W.b₂*W.b₄*W.b₈
        - (20:k)*x*W.b₂^2*W.b₄*W.b₆
        + (2:k)*x^2*W.b₆^2
        + (46:k)*x^2*W.b₄*W.b₈
        + (83:k)*x^2*W.b₂*W.b₄*W.b₆
        - (5:k)*x^2*W.b₂^2*W.b₈
        - (10:k)*x^2*W.b₂^3*W.b₆
        + (3:k)*x^3*W.b₄*W.b₆
        + (3:k)*x^3*W.b₂*W.b₈
        + (2:k)*x^3*W.b₂^2*W.b₆
        + (86:k)*x^4*W.b₈
        + (2:k)*x^4*W.b₄^2
        + (171:k)*x^4*W.b₂*W.b₆
        + (2:k)*x^5*W.b₆
        + x^5*W.b₂*W.b₄
        + (3:k)*x^8)) * hbrel

end WeierstrassCurve
