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
    map_add, map_mul, map_pow]
  ring

set_option maxHeartbeats 64000000 in
private lemma preΨ₄_add_Ψ₂Sq_sq :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.Ψ₃ * (6 * Polynomial.X ^ 2 + C W.b₂ * Polynomial.X + C W.b₄) := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    C_add, C_mul, C_pow, C_sub, map_ofNat]
  ring

private lemma h_factor_cr :
    Affine.CoordinateRing.mk W (Polynomial.C W.preΨ₄) +
      (Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₂Sq)) ^ 2
    = Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₃) *
      Affine.CoordinateRing.mk W (Polynomial.C (6 * Polynomial.X ^ 2 + C W.b₂ * Polynomial.X + C W.b₄)) := by
  rw [← map_pow (Affine.CoordinateRing.mk W),
      ← map_pow (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)),
      ← map_add (Affine.CoordinateRing.mk W),
      ← map_add (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)),
      preΨ₄_add_Ψ₂Sq_sq,
      map_mul (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)),
      map_mul (Affine.CoordinateRing.mk W)]

set_option maxHeartbeats 16000000 in
private lemma mk_C_Ψ₂Sq_expand :
    Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₂Sq)
    = 4 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : R[X])) ^ 3
      + (Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₁)) ^ 2
          + 4 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₂)))
        * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : R[X])) ^ 2
      + (2 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₁))
            * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₃))
          + 4 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₄)))
        * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : R[X]))
      + (Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₃)) ^ 2
          + 4 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₆))) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

set_option maxHeartbeats 16000000 in
private lemma mk_C_half_deriv_expand :
    Affine.CoordinateRing.mk W (Polynomial.C (6 * Polynomial.X ^ 2 + C W.b₂ * Polynomial.X + C W.b₄))
    = 6 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : R[X])) ^ 2
      + (Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₁)) ^ 2
          + 4 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₂)))
        * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : R[X]))
      + (Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₁))
            * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₃))
          + 2 * Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C W.a₄))) := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

set_option maxHeartbeats 64000000 in
lemma mk_cross_identity [IsDomain R] (h3 : (3 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
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
  have h_inv := WeierstrassCurve.mk_invariant_descended W hψ_ne m
  simp only [map_mul, map_add, map_pow] at h_inv
  have h_sq := Affine.CoordinateRing.mk_ψ₂_sq W
  have h4 : Affine.CoordinateRing.mk W W.ψ₂ ^ 4
      = (Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₂Sq)) ^ 2 := by
    calc _ = (Affine.CoordinateRing.mk W W.ψ₂ ^ 2) ^ 2 := by ring
      _ = _ := by rw [h_sq]
  rw [h_sq, h4] at h_inv
  rw [h_factor_cr] at h_inv
  have hΨ₃_ne : W.Ψ₃ ≠ 0 := W.Ψ₃_ne_zero h3
  have hΨ₃_mk : Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₃) ≠ 0 :=
    fun h => hΨ₃_ne (mk_C_injective W (by simpa using h))
  have h_rearr : Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₃) *
      Affine.CoordinateRing.mk W (Polynomial.C (6 * Polynomial.X ^ 2 + C W.b₂ * Polynomial.X + C W.b₄)) *
      (Affine.CoordinateRing.mk W (W.ψ (m + 1)) * Affine.CoordinateRing.mk W (W.ψ m) *
       Affine.CoordinateRing.mk W (W.ψ (m - 1)))
    = Affine.CoordinateRing.mk W (Polynomial.C W.Ψ₃) *
      (Affine.CoordinateRing.mk W (Polynomial.C (6 * Polynomial.X ^ 2 + C W.b₂ * Polynomial.X + C W.b₄)) *
       (Affine.CoordinateRing.mk W (W.ψ (m + 1)) * Affine.CoordinateRing.mk W (W.ψ m) *
        Affine.CoordinateRing.mk W (W.ψ (m - 1)))) := by ring
  rw [h_rearr] at h_inv
  have h_cancelled := mul_left_cancel₀ hΨ₃_mk h_inv
  rw [mk_C_Ψ₂Sq_expand] at h_cancelled
  rw [mk_C_half_deriv_expand] at h_cancelled
  linear_combination (norm := ring) h_cancelled

variable [IsDomain R] [Invertible (2 : R)]

set_option maxHeartbeats 800000000 in
set_option maxRecDepth 16000 in
theorem probe (h3 : (3 : R) ≠ 0) (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
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
  have h_ψ2 : A W.ψ₂ = 2 * A (Polynomial.X : R[X][X]) +
      A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.X : R[X])) +
      A (Polynomial.C (Polynomial.C W.a₃)) := by
    have : W.ψ₂ = 2 * (Polynomial.X : R[X][X]) + Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) + Polynomial.C (Polynomial.C W.a₃) := by
      unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring
    rw [this]; simp [map_add, map_mul, map_ofNat]
  rw [h_ψ2] at h_mk_even ⊢
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
  set cx := A (Polynomial.C (Polynomial.X : R[X]))
  set cy := A (Polynomial.X : R[X][X])
  set ca1 := A (Polynomial.C (Polynomial.C W.a₁))
  set ca2 := A (Polynomial.C (Polynomial.C W.a₂))
  set ca3 := A (Polynomial.C (Polynomial.C W.a₃))
  set ca4 := A (Polynomial.C (Polynomial.C W.a₄))
  set ca6 := A (Polynomial.C (Polynomial.C W.a₆))
  have h_cross :
    A (W.ψ (m + 2)) * A (W.ψ (m - 1)) ^ 2 + A (W.ψ (m - 2)) * A (W.ψ (m + 1)) ^ 2
    + (4 * cx ^ 3
        + (ca1 ^ 2 + 4 * ca2) * cx ^ 2
        + (2 * ca1 * ca3 + 4 * ca4) * cx
        + (ca3 ^ 2 + 4 * ca6))
      * A (W.ψ m) ^ 3
    = (6 * cx ^ 2 + (ca1 ^ 2 + 4 * ca2) * cx + (ca1 * ca3 + 2 * ca4))
      * A (W.ψ m) * A (W.ψ (m + 1)) * A (W.ψ (m - 1)) :=
    mk_cross_identity W h3 hψ_ne m
  linear_combination (norm := ring)
    2 * h_mk_ring
    - A (W.ψ m) ^ 2 * h_mk_even
    + 2 * A (W.ψ m) ^ 6 * h_curve
    + A (W.ψ m) ^ 3 * h_cross

end
