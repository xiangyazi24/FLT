module

import scratch.ProjectiveFormula
import scratch.ProjectiveFormulaXY
import scratch.PsiInvariant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial
open FLT.EDS (mk_ψ_eq mk_C_injective psi_adjacent_somos mk_psi_adjacent_somos)

section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

set_option maxHeartbeats 64000000 in
private lemma addX_ring_id (m : ℤ) :
    addX W.toPoly
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, 0, W.ψ m]) * W.ψ m ^ 2
    + W.ψ m ^ 6 * W.toAffine.polynomial
    = ((Polynomial.X : R[X][X]) * W.ψ m ^ 3) ^ 2
      + Polynomial.C (Polynomial.C W.a₁) *
        ((Polynomial.X : R[X][X]) * W.ψ m ^ 3) * W.ψ m *
        (W.ψ (m - 1) * W.ψ (m + 1))
      - Polynomial.C (Polynomial.C W.a₂) * W.ψ m ^ 2 * (W.ψ (m - 1) * W.ψ (m + 1)) ^ 2
      - Polynomial.C (Polynomial.X : R[X]) * W.ψ m ^ 2 * (W.ψ (m - 1) * W.ψ (m + 1)) ^ 2
      - W.φ m * (W.ψ (m - 1) * W.ψ (m + 1)) ^ 2
      + W.φ m ^ 3 + Polynomial.C (Polynomial.C W.a₂) * W.φ m ^ 2 * W.ψ m ^ 2
      + Polynomial.C (Polynomial.C W.a₄) * W.φ m * W.ψ m ^ 4
      + Polynomial.C (Polynomial.C W.a₆) * W.ψ m ^ 6 := by
  unfold addX WeierstrassCurve.toPoly WeierstrassCurve.map
    Affine.polynomial WeierstrassCurve.φ
  simp only [RingHom.comp_apply, Matrix.cons_val,
    map_add, map_sub, map_mul, map_pow]
  ring

/-- Cross-identity: complement-sum for the division-polynomial EDS (in the CR). -/
lemma mk_cross_identity (m : ℤ) :
    let A := Affine.CoordinateRing.mk W.toAffine
    A (W.ψ (m + 2)) * A (W.ψ (m - 1)) ^ 2
    + A (W.ψ (m - 2)) * A (W.ψ (m + 1)) ^ 2
    + (4 * A (Polynomial.C (Polynomial.X : R[X])) ^ 3
        + (A (Polynomial.C (Polynomial.C W.a₁)) ^ 2
            + 4 * A (Polynomial.C (Polynomial.C W.a₂)))
          * A (Polynomial.C (Polynomial.X : R[X])) ^ 2
        + (2 * A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.C W.a₃))
            + 4 * A (Polynomial.C (Polynomial.C W.a₄)))
          * A (Polynomial.C (Polynomial.X : R[X]))
        + (A (Polynomial.C (Polynomial.C W.a₃)) ^ 2
            + 4 * A (Polynomial.C (Polynomial.C W.a₆))))
      * A (W.ψ m) ^ 3
    = (6 * A (Polynomial.C (Polynomial.X : R[X])) ^ 2
        + (A (Polynomial.C (Polynomial.C W.a₁)) ^ 2
            + 4 * A (Polynomial.C (Polynomial.C W.a₂)))
          * A (Polynomial.C (Polynomial.X : R[X]))
        + (A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.C W.a₃))
            + 2 * A (Polynomial.C (Polynomial.C W.a₄))))
      * A (W.ψ m) * A (W.ψ (m + 1)) * A (W.ψ (m - 1)) := by
  sorry

variable [IsDomain R] [Invertible (2 : R)]

set_option maxHeartbeats 800000000 in
set_option maxRecDepth 16000 in
theorem probe (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    AdjoinRoot.mk W.toAffine.polynomial
      ((Polynomial.C (Polynomial.C (2 : R)) *
        (addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, 0, W.ψ m]) -
         W.ψ (m - 1) ^ 2 * W.φ (m + 1)) -
       W.ψ₂ * (W.ψ (2 * m) - W.ψ m ^ 2 *
          (Polynomial.C (Polynomial.C W.a₁) * W.φ m +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ m ^ 2))) * W.ψ m ^ 2) = 0 := by
  have h_ring := addX_ring_id W m
  have h_even := W.ψ_even m
  set A := AdjoinRoot.mk W.toAffine.polynomial with hA
  have h_mk_ring := congrArg A h_ring
  have h_mk_even := congrArg A h_even
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at h_mk_ring h_mk_even ⊢
  rw [show A W.toAffine.polynomial = 0 from AdjoinRoot.mk_self] at h_mk_ring
  simp only [mul_zero, add_zero] at h_mk_ring
  -- Unfold φ
  have h_φm : A (W.φ m) = A (Polynomial.C (Polynomial.X : R[X])) * A (W.ψ m) ^ 2 -
      A (W.ψ (m + 1)) * A (W.ψ (m - 1)) := by
    have : W.φ m = Polynomial.C (Polynomial.X : R[X]) * W.ψ m ^ 2 - W.ψ (m + 1) * W.ψ (m - 1) := by
      unfold WeierstrassCurve.φ; ring
    rw [this]; simp [map_sub, map_mul, map_pow]
  have h_φm1 : A (W.φ (m + 1)) = A (Polynomial.C (Polynomial.X : R[X])) * A (W.ψ (m + 1)) ^ 2 -
      A (W.ψ (m + 2)) * A (W.ψ m) := by
    have : W.φ (m + 1) = Polynomial.C (Polynomial.X : R[X]) * W.ψ (m + 1) ^ 2 - W.ψ (m + 2) * W.ψ m := by
      unfold WeierstrassCurve.φ; ring
    rw [this]; simp [map_sub, map_mul, map_pow]
  rw [h_φm] at h_mk_ring
  rw [h_φm, h_φm1]
  -- Expand ψ₂
  have h_ψ2 : A W.ψ₂ = 2 * A (Polynomial.X : R[X][X]) +
      A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.X : R[X])) +
      A (Polynomial.C (Polynomial.C W.a₃)) := by
    have : W.ψ₂ = 2 * (Polynomial.X : R[X][X]) + Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) + Polynomial.C (Polynomial.C W.a₃) := by
      unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring
    rw [this]; simp [map_add, map_mul, map_ofNat]
  rw [h_ψ2] at h_mk_even ⊢
  -- Curve equation in the CR
  have h_curve : A (Polynomial.X : R[X][X]) ^ 2 =
    - A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.X : R[X])) * A (Polynomial.X : R[X][X])
    - A (Polynomial.C (Polynomial.C W.a₃)) * A (Polynomial.X : R[X][X])
    + A (Polynomial.C (Polynomial.X : R[X])) ^ 3
    + A (Polynomial.C (Polynomial.C W.a₂)) * A (Polynomial.C (Polynomial.X : R[X])) ^ 2
    + A (Polynomial.C (Polynomial.C W.a₄)) * A (Polynomial.C (Polynomial.X : R[X]))
    + A (Polynomial.C (Polynomial.C W.a₆)) := by
    have h := congrArg A (show W.toAffine.polynomial =
      (Polynomial.X : R[X][X]) ^ 2
      + Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) * (Polynomial.X : R[X][X])
      + Polynomial.C (Polynomial.C W.a₃) * (Polynomial.X : R[X][X])
      - Polynomial.C (Polynomial.X : R[X]) ^ 3
      - Polynomial.C (Polynomial.C W.a₂) * Polynomial.C (Polynomial.X : R[X]) ^ 2
      - Polynomial.C (Polynomial.C W.a₄) * Polynomial.C (Polynomial.X : R[X])
      - Polynomial.C (Polynomial.C W.a₆) by
        unfold Affine.polynomial; simp; ring)
    simp only [map_sub, map_add, map_mul, map_pow] at h
    have hFW : A W.toAffine.polynomial = 0 := AdjoinRoot.mk_self
    linear_combination hFW - h
  -- Abbreviations for readability
  set cx := A (Polynomial.C (Polynomial.X : R[X]))
  set cy := A (Polynomial.X : R[X][X])
  set ca1 := A (Polynomial.C (Polynomial.C W.a₁))
  set ca2 := A (Polynomial.C (Polynomial.C W.a₂))
  set ca3 := A (Polynomial.C (Polynomial.C W.a₃))
  set ca4 := A (Polynomial.C (Polynomial.C W.a₄))
  set ca6 := A (Polynomial.C (Polynomial.C W.a₆))
  -- Cross-identity
  have h_cross :
    A (W.ψ (m + 2)) * A (W.ψ (m - 1)) ^ 2 + A (W.ψ (m - 2)) * A (W.ψ (m + 1)) ^ 2
    + (4 * cx ^ 3
        + (ca1 ^ 2 + 4 * ca2) * cx ^ 2
        + (2 * ca1 * ca3 + 4 * ca4) * cx
        + (ca3 ^ 2 + 4 * ca6))
      * A (W.ψ m) ^ 3
    = (6 * cx ^ 2 + (ca1 ^ 2 + 4 * ca2) * cx + (ca1 * ca3 + 2 * ca4))
      * A (W.ψ m) * A (W.ψ (m + 1)) * A (W.ψ (m - 1)) :=
    mk_cross_identity W m
  -- Final linear_combination
  linear_combination (norm := ring)
    2 * h_mk_ring
    - A (W.ψ m) ^ 2 * h_mk_even
    + 2 * A (W.ψ m) ^ 6 * h_curve
    + A (W.ψ m) ^ 3 * h_cross

end
