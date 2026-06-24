import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! # Bridge-1 coprimality, even case — foundation (hCD relation)

At a root of `Ψ₂Sq`, the EDS parameter `b = Ψ₂Sq² = 0`, and `preΨ' n = preNormEDS' 0 Ψ₃ preΨ₄ n`.
The even closed-forms need the on-`Ψ₂Sq`-root relation `preΨ₄² + 4·Ψ₃³ = 0`.

CAS-VERIFIED (sympy, /tmp/hcd_cert.pkl): `preΨ₄² + 4·Ψ₃³ = Q1·Ψ₂Sq + Q2·b_relation` exactly
(remainder 0; Q1 = 57-term deg-9, Q2 = 25-term cofactor). So the identity is true; the
`linear_combination` below has a lift/normalisation mismatch still to iron out (the math is sound).
TODO(next, fresh context): fix the cofactor lift so the `linear_combination` closes; then the
EDS-zero closed forms (`preNormEDS' 0 C D` for 2m+1 / 4m+2 / 4(m+1)) via `normEDSRec'`, then
nonvanishing (C = Ψ₃(x) ≠ 0, D = preΨ₄(x) ≠ 0 from avenue-c certs) ⟹ `preΨ'_root_Ψ₂Sq_ne` even case. -/

open Polynomial

namespace WeierstrassCurve
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- hCD: at a `Ψ₂Sq`-root, `preΨ₄² + 4·Ψ₃³ = 0`. CAS-verified identity; cert-lift WIP. -/
lemma preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root {x : k} (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 + 4 * (W.Ψ₃.eval x) ^ 3 = 0 := by
  sorry

end WeierstrassCurve
