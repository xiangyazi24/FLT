import scratch.PsiSomos
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

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
noncomputable def dupNumP (Xc Zc : R[X]) : R[X] :=
  Xc ^ 4 - C W.b₄ * Xc ^ 2 * Zc ^ 2 - C (2 * W.b₆) * Xc * Zc ^ 3 - C W.b₈ * Zc ^ 4

/-- Homogeneous x-doubling denominator on `R[X]` representatives. -/
noncomputable def dupDenP (Xc Zc : R[X]) : R[X] :=
  C 4 * Xc ^ 3 * Zc + C W.b₂ * Xc ^ 2 * Zc ^ 2 + C (2 * W.b₄) * Xc * Zc ^ 3 + C W.b₆ * Zc ^ 4

/-- Base sanity: the doubling map at `[X, 1]` is `[Φ 2, ΨSq 2]`. -/
lemma dupNumP_X_one : W.dupNumP X 1 = W.Φ 2 := by
  rw [dupNumP, W.Φ_two]; ring

/-- `ΨSq (2m)` expanded into `preΨ` (always-even index). -/
lemma ΨSq_two_mul_expand (m : ℤ) :
    W.ΨSq (2 * m) =
      W.Ψ₂Sq * W.preΨ m ^ 2 *
        (W.preΨ (m - 1) ^ 2 * W.preΨ (m + 2) - W.preΨ (m - 2) * W.preΨ (m + 1) ^ 2) ^ 2 := by
  rw [W.ΨSq_even m]; ring

end WeierstrassCurve
