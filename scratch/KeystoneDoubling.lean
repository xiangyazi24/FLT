module

public import scratch.PsiSomos
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# Keystone doubling — the division-polynomial duplication identities

`ΨSq_two_mul : W.ΨSq (2*m) = dupDenH (W.Φ m) (W.ΨSq m)` and the numerator analogue. These are the
x-coordinate duplication formulas; via a Ψ₃-saturated `linear_combination` over `preΨ_adjacent_somos`
(Adj) + `preΨ_invariant` (Inv, = Ward `InvarRel` on ψ) + `b_relation` (bRel), then cancel `Ψ₃≠0`.
All four parity×num/den cofactor certificates were CAS-verified (see `KEYSTONE_DOUBLING_CERT.md`).
-/

namespace WeierstrassCurve

open Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Homogeneous x-doubling numerator on `R[X]` representatives. -/
@[expose] public noncomputable def dupNumP (Xc Zc : R[X]) : R[X] :=
  Xc ^ 4 - C W.b₄ * Xc ^ 2 * Zc ^ 2 - C (2 * W.b₆) * Xc * Zc ^ 3 - C W.b₈ * Zc ^ 4

/-- Homogeneous x-doubling denominator on `R[X]` representatives. -/
@[expose] public noncomputable def dupDenP (Xc Zc : R[X]) : R[X] :=
  C 4 * Xc ^ 3 * Zc + C W.b₂ * Xc ^ 2 * Zc ^ 2 + C (2 * W.b₄) * Xc * Zc ^ 3 + C W.b₆ * Zc ^ 4

/-- Base sanity: the doubling map at `[X, 1]` is `[Φ 2, ΨSq 2]`. -/
public lemma dupNumP_X_one : W.dupNumP X 1 = W.Φ 2 := by
  rw [dupNumP, W.Φ_two]; ring

/-- `ΨSq (2m)` expanded into `preΨ` (always-even index). -/
public lemma ΨSq_two_mul_expand (m : ℤ) :
    W.ΨSq (2 * m) =
      W.Ψ₂Sq * W.preΨ m ^ 2 *
        (W.preΨ (m - 1) ^ 2 * W.preΨ (m + 2) - W.preΨ (m - 2) * W.preΨ (m + 1) ^ 2) ^ 2 := by
  rw [W.ΨSq_even m]; ring

/-- Eval bridge: `dupNumP` evaluated is the value-level doubling numerator (in `W.b_i`). -/
public lemma dupNumP_eval (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupNumP Xc Zc).eval x
      = (Xc.eval x) ^ 4 - W.b₄ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        - 2 * W.b₆ * (Xc.eval x) * (Zc.eval x) ^ 3 - W.b₈ * (Zc.eval x) ^ 4 := by
  simp only [dupNumP, eval_sub, eval_mul, eval_pow, eval_C]

/-- Eval bridge: `dupDenP` evaluated is the value-level doubling denominator. -/
public lemma dupDenP_eval (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupDenP Xc Zc).eval x
      = 4 * (Xc.eval x) ^ 3 * (Zc.eval x) + W.b₂ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        + 2 * W.b₄ * (Xc.eval x) * (Zc.eval x) ^ 3 + W.b₆ * (Zc.eval x) ^ 4 := by
  simp only [dupDenP, eval_add, eval_mul, eval_pow, eval_C, eval_ofNat]

end WeierstrassCurve
