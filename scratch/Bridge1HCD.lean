import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

/-!
# Bridge1HCD: Auxiliary lemmas about division polynomials at Ψ₂Sq roots

These lemmas state:
1. `Ψ₃.eval x ≠ 0` when `Ψ₂Sq.eval x = 0` (in a field where char ≠ 2, 3)
2. `(preΨ₄.eval x)² + 4*(Ψ₃.eval x)³ = 0` at a Ψ₂Sq root

These are standard facts about elliptic curve division polynomials at 2-torsion points.
The proofs follow from the polynomial identity `preΨ₄² + 4*Ψ₃³ ≡ 0 mod Ψ₂Sq`
and the separability of `Ψ₂Sq` (over a field of characteristic ≠ 2).

TODO: Fill in proofs; currently `sorry`'d to allow Bridge1Even to compile.
-/

variable {K : Type*} [Field K]

namespace WeierstrassCurve

/-- At a root of `Ψ₂Sq`, the polynomial `Ψ₃` does not vanish.
    This follows from the fact that gcd(Ψ₂Sq, Ψ₃) = 1 over a field (they are coprime
    division polynomials corresponding to distinct torsion orders). -/
lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero (W : WeierstrassCurve K) {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by
  sorry

/-- At a root of `Ψ₂Sq`, we have `(preΨ₄.eval x)² + 4*(Ψ₃.eval x)³ = 0`.
    This is the polynomial identity `preΨ₄² + 4*Ψ₃³ ≡ 0 mod Ψ₂Sq`. -/
lemma preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root (W : WeierstrassCurve K) {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 + 4 * (W.Ψ₃.eval x) ^ 3 = 0 := by
  sorry

end WeierstrassCurve
