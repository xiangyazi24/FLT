/-
  scratch/AddXGeneral.lean
  General-m X-component projective identity.
  ATOM 4a (general m): mk(addX(P, R_m) - ψ_{m-1}² · φ_{m+1}) = 0

  Proof strategy:
  1. Multiply by C(C 2), eliminate ωP via two_mul_ψ_mul_ωP
  2. Replace ψ₂·ψ_{2m} using ψ_even (polynomial identity)
  3. Unfold φ using its definition
  4. Distribute mk, apply mk_ψ
  5. Y-terms cancel (ring identity)
  6. Y⁰-terms vanish by Ward + the identity preΨ₄+Ψ₂Sq² = Ψ₃·(6X²+b₂X+b₄)
-/
module

import scratch.ProjectiveFormula
import scratch.ProjectiveFormulaXY
import scratch.PsiInvariant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial

section Helpers
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
private theorem ψ₂_expl :
    W.ψ 2 = 2 * (Polynomial.X : R[X][X]) +
    Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
    Polynomial.C (Polynomial.C W.a₃) := by
  rw [ψ_two]; unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring
end Helpers

section GeneralM

variable {R : Type*} [CommRing R] [IsDomain R] [Invertible (2 : R)]
  (W : WeierstrassCurve R)

-- ω elimination (same pattern as m=2)
set_option maxHeartbeats 32000000 in
omit [IsDomain R] in
private theorem addX_elim_ω_gen (m : ℤ) :
    Polynomial.C (Polynomial.C (2 : R)) *
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) =
    Polynomial.C (Polynomial.C (2 : R)) *
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, 0, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
    W.ψ 2 * (W.ψ (2 * m) - W.ψ m ^ 2 *
        (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2)) := by
  have hω := W.two_mul_ψ_mul_ωP m
  rw [ψ₂_expl] at *
  simp only [map_ofNat] at *
  unfold addX WeierstrassCurve.toPoly WeierstrassCurve.map
  simp only [RingHom.comp_apply, Matrix.cons_val]
  linear_combination (norm := ring)
    -(2 * (Polynomial.X : R[X][X]) +
      Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
      Polynomial.C (Polynomial.C W.a₃)) * hω

-- The ω-free expression is divisible by F_W.
-- Proof: Apply ψ_even at the polynomial level, then work in the CR using
-- mk_ψ, mk_φ, Ward invariant, and the identity preΨ₄+Ψ₂Sq² = Ψ₃(6X²+b₂X+b₄).
set_option maxHeartbeats 800000000 in
set_option maxRecDepth 16000 in
private theorem ωfree_dvd (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    W.toAffine.polynomial ∣
      (Polynomial.C (Polynomial.C (2 : R)) *
        (addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, 0, W.ψ m]) -
         W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
       W.ψ 2 * (W.ψ (2 * m) - W.ψ m ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2))) := by
  -- Use ψ_even at the polynomial level: ψ(2m)·ψ₂ = RHS
  -- Rewrite the expression by substituting for ψ₂·ψ(2m) term
  -- Then unfold addX, φ, and show the result is in the ideal.
  sorry

/-- **ATOM 4a (general m).** X-component projective identity for ALL m.
In the coordinate ring R[W], the X-coordinate of the formal addition
P + [m]P equals ψ_{m-1}² · φ_{m+1}. -/
theorem mk_addX_divPoly_general (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 2 * W.φ (m + 1)) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  have h := addX_elim_ω_gen W m
  have hd := ωfree_dvd W hψ_ne m
  rw [← h] at hd
  exact (IsUnit.dvd_mul_left (by
    rw [Polynomial.isUnit_C, Polynomial.isUnit_C]
    exact isUnit_of_invertible 2)).mp hd

end GeneralM

#print axioms mk_addX_divPoly_general
