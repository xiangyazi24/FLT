/-
  scratch/ProjectiveFormulaXY.lean
  Projective division-polynomial X-component formulas.
  ATOM 4a: mk W.toAffine (addX(P, R_m) - ψ_{m-1}² · φ_{m+1}) = 0
  Status: m=1 0-sorry, m=2 1-sorry (integral identity).
-/
module

import scratch.ProjectiveFormula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial

/-! ## m = 1 -/

section M1

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

set_option maxHeartbeats 800000 in
private theorem addX_self_eq :
    Jacobian.addX W.toPoly
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1]) =
    -2 * W.toAffine.polynomial := by
  unfold Jacobian.addX Affine.polynomial WeierstrassCurve.toPoly WeierstrassCurve.map
  simp; ring

/-- **ATOM 4a (m=1).** 0 sorry, 0 custom axiom. -/
theorem mk_addX_divPoly_m1 :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (Jacobian.addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ 1, (Polynomial.X : R[X][X]), W.ψ 1]) -
       W.ψ 0 ^ 2 * W.φ 2) = 0 := by
  rw [φ_one, ψ_one, ψ_zero]
  simp only [zero_pow (two_ne_zero), zero_mul, sub_zero]
  rw [addX_self_eq]; simp [AdjoinRoot.mk_self]

end M1

/-! ## m = 2 -/

section M2_helpers

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private theorem ψ₂_explicit :
    W.ψ 2 = 2 * (Polynomial.X : R[X][X]) +
    Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
    Polynomial.C (Polynomial.C W.a₃) := by
  rw [ψ_two]; unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring

end M2_helpers

section M2

variable {R : Type*} [CommRing R] [Invertible (2 : R)] (W : WeierstrassCurve R)

set_option maxHeartbeats 32000000 in
private theorem addX_elim_ωP :
    Polynomial.C (Polynomial.C (2 : R)) *
      (Jacobian.addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ 2, W.ωP 2, W.ψ 2]) - W.φ 3) =
    Polynomial.C (Polynomial.C (2 : R)) *
      (Jacobian.addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ 2, 0, W.ψ 2]) - W.φ 3) -
    W.ψ 2 * (W.ψ (2 * 2) - W.ψ 2 ^ 2 *
        (Polynomial.C (Polynomial.C W.a₁) * W.φ 2 +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ 2 ^ 2)) := by
  have hω := W.two_mul_ψ_mul_ωP 2
  rw [ψ₂_explicit] at hω ⊢
  simp only [map_ofNat] at hω ⊢
  unfold Jacobian.addX WeierstrassCurve.toPoly WeierstrassCurve.map
  simp only [RingHom.comp_apply, Matrix.cons_val]
  linear_combination (norm := ring)
    -(2 * (Polynomial.X : R[X][X]) +
      Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
      Polynomial.C (Polynomial.C W.a₃)) * hω

-- The integral identity. This is the core computational step.
-- After full unfolding, the expression is a polynomial in CC(aᵢ), CX, X
-- with integer coefficients, and we need polynomial ∣ expression.
-- CAS-verified. Lean proof requires providing the ~40-term quotient.
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 8000 in
private theorem two_mul_addX_sub_phi3_dvd :
    W.toAffine.polynomial ∣
      (Polynomial.C (Polynomial.C (2 : R)) *
        (Jacobian.addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ 2, 0, W.ψ 2]) - W.φ 3) -
       W.ψ 2 * (W.ψ (2 * 2) - W.ψ 2 ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ 2 +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ 2 ^ 2))) := by
  rw [show (2 * 2 : ℤ) = 4 from rfl, ψ_four, φ_two, φ_three, ψ₂_explicit]
  unfold Jacobian.addX WeierstrassCurve.toPoly WeierstrassCurve.map
    Affine.polynomial WeierstrassCurve.ψ₂ Affine.polynomialY
    WeierstrassCurve.Ψ₃ WeierstrassCurve.preΨ₄
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    RingHom.comp_apply, Matrix.cons_val, map_ofNat]
  sorry

/-- **ATOM 4a (m=2).** X-component identity for m=2. 1 sorry (integral polynomial identity). -/
theorem mk_addX_divPoly_m2 :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (Jacobian.addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ 2, W.ωP 2, W.ψ 2]) -
       W.ψ 1 ^ 2 * W.φ 3) = 0 := by
  rw [ψ_one, one_pow, one_mul, AdjoinRoot.mk_eq_zero]
  have h := addX_elim_ωP W
  have hd := two_mul_addX_sub_phi3_dvd W
  rw [← h] at hd
  exact (IsUnit.dvd_mul_left (by
    rw [Polynomial.isUnit_C, Polynomial.isUnit_C]
    exact isUnit_of_invertible 2)).mp hd

end M2

#print axioms mk_addX_divPoly_m1
#print axioms mk_addX_divPoly_m2

