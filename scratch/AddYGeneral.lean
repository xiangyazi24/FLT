/-
  scratch/AddYGeneral.lean
  General-m Y-component projective identity.
  ATOM 4b (general m): mk(addY(P, R_m) - ψ_{m-1}³ · ωP_{m+1}) = 0
-/

import scratch.AddXGeneral
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial
open FLT.EDS (mk_ψ_eq mk_C_injective psi_adjacent_somos mk_psi_adjacent_somos)

noncomputable section GeneralM

variable {R : Type*} [CommRing R] [IsDomain R] [Invertible (2 : R)]
  (W : WeierstrassCurve R)

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 1: negAddY factored via negAddY_eq'
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 32000000 in
omit [IsDomain R] in
private lemma negAddY_factored (m : ℤ) :
    negAddY W.toPoly
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, W.ωP m, W.ψ m]) * W.ψ m ^ 3 =
    ((Polynomial.X : R[X][X]) * W.ψ m ^ 3 - W.ωP m) *
      (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) * W.ψ m ^ 2 -
       Polynomial.C (Polynomial.X : R[X]) * W.ψ m ^ 2 *
        (W.ψ (m - 1) * W.ψ (m + 1)) ^ 2) +
    (Polynomial.X : R[X][X]) * W.ψ m ^ 3 *
      (W.ψ (m - 1) * W.ψ (m + 1)) ^ 3 := by
  have h := negAddY_eq' (W' := W.toPoly)
    (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
    (![W.φ m, W.ωP m, W.ψ m])
  simp only [Matrix.cons_val, one_mul, mul_one, one_pow] at h
  have hZ : addZ
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, W.ωP m, W.ψ m]) =
    W.ψ (m - 1) * W.ψ (m + 1) :=
    addZ_divPoly_eq W m (Polynomial.X : R[X][X]) (W.ωP m)
  rw [hZ] at h; exact h

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 2: addY expansion
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
omit [IsDomain R] in
private lemma addY_expand (m : ℤ) :
    addY W.toPoly
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, W.ωP m, W.ψ m]) =
    -(negAddY W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]))
    - Polynomial.C (Polynomial.C W.a₁) *
        addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, W.ωP m, W.ψ m]) *
        (W.ψ (m - 1) * W.ψ (m + 1))
    - Polynomial.C (Polynomial.C W.a₃) * (W.ψ (m - 1) * W.ψ (m + 1)) ^ 3 := by
  simp only [addY, negY_eq, Matrix.cons_val]
  have ha1 : W.toPoly.a₁ = Polynomial.C (Polynomial.C W.a₁) := by
    unfold WeierstrassCurve.toPoly WeierstrassCurve.map; simp [RingHom.comp_apply]
  have ha3 : W.toPoly.a₃ = Polynomial.C (Polynomial.C W.a₃) := by
    unfold WeierstrassCurve.toPoly WeierstrassCurve.map; simp [RingHom.comp_apply]
  have hZ : addZ
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, W.ωP m, W.ψ m]) =
    W.ψ (m - 1) * W.ψ (m + 1) :=
    addZ_divPoly_eq W m (Polynomial.X : R[X][X]) (W.ωP m)
  rw [ha1, ha3, hZ]

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 3: φ definition
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] [Invertible (2 : R)] in
private lemma phi_minus_x_psi_sq (k : ℤ) :
    W.φ k - Polynomial.C (Polynomial.X : R[X]) * W.ψ k ^ 2 =
    -(W.ψ (k + 1) * W.ψ (k - 1)) := by
  unfold WeierstrassCurve.φ; ring

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 4: EDS shifted identity
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] [Invertible (2 : R)] in
private lemma eds_shifted_identity (m : ℤ) :
    W.ψ m ^ 2 * W.ψ (m + 3) * W.ψ (m - 1) -
    W.ψ (m - 2) * W.ψ (m + 1) ^ 2 * W.ψ (m + 2) =
    W.ψ₂ ^ 2 * W.ψ (2 * m + 1) := by
  have hS1 := psi_adjacent_somos W (m + 1)
  conv at hS1 =>
    rw [show (m + 1 : ℤ) + 2 = m + 3 from by ring,
        show (m + 1 : ℤ) - 2 = m - 1 from by ring,
        show (m + 1 : ℤ) + 1 = m + 2 from by ring,
        show (m + 1 : ℤ) - 1 = m from by ring]
  have hS2 := psi_adjacent_somos W m
  have hOdd : W.ψ (2 * m + 1) = W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3 := by
    rw [WeierstrassCurve.ψ]
    exact normEDS_odd W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) m
  have h1 : W.ψ m ^ 2 * (W.ψ (m + 3) * W.ψ (m - 1)) =
      W.ψ₂ ^ 2 * W.ψ (m + 2) * W.ψ m ^ 3 - Polynomial.C W.Ψ₃ * W.ψ (m + 1) ^ 2 * W.ψ m ^ 2 := by
    calc W.ψ m ^ 2 * (W.ψ (m + 3) * W.ψ (m - 1))
        = W.ψ m ^ 2 * (W.ψ₂ ^ 2 * W.ψ (m + 2) * W.ψ m - Polynomial.C W.Ψ₃ * W.ψ (m + 1) ^ 2) := by rw [hS1]
      _ = _ := by ring
  have h2 : W.ψ (m + 1) ^ 2 * (W.ψ (m + 2) * W.ψ (m - 2)) =
      W.ψ₂ ^ 2 * W.ψ (m + 1) ^ 3 * W.ψ (m - 1) - Polynomial.C W.Ψ₃ * W.ψ m ^ 2 * W.ψ (m + 1) ^ 2 := by
    calc W.ψ (m + 1) ^ 2 * (W.ψ (m + 2) * W.ψ (m - 2))
        = W.ψ (m + 1) ^ 2 * (W.ψ₂ ^ 2 * W.ψ (m + 1) * W.ψ (m - 1) - Polynomial.C W.Ψ₃ * W.ψ m ^ 2) := by rw [hS2]
      _ = _ := by ring
  calc W.ψ m ^ 2 * W.ψ (m + 3) * W.ψ (m - 1) -
      W.ψ (m - 2) * W.ψ (m + 1) ^ 2 * W.ψ (m + 2)
      = (W.ψ m ^ 2 * (W.ψ (m + 3) * W.ψ (m - 1))) -
        (W.ψ (m + 1) ^ 2 * (W.ψ (m + 2) * W.ψ (m - 2))) := by ring
    _ = (W.ψ₂ ^ 2 * W.ψ (m + 2) * W.ψ m ^ 3 - Polynomial.C W.Ψ₃ * W.ψ (m + 1) ^ 2 * W.ψ m ^ 2) -
        (W.ψ₂ ^ 2 * W.ψ (m + 1) ^ 3 * W.ψ (m - 1) - Polynomial.C W.Ψ₃ * W.ψ m ^ 2 * W.ψ (m + 1) ^ 2) := by
          rw [h1, h2]
    _ = W.ψ₂ ^ 2 * (W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3) := by ring
    _ = W.ψ₂ ^ 2 * W.ψ (2 * m + 1) := by rw [← hOdd]

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 5: ψTwoMulQuotP · ψ₂
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] [Invertible (2 : R)] in
private lemma psiTMQ_mul_psi2 (k : ℤ) :
    W.ψTwoMulQuotP k * W.ψ₂ =
    W.ψ (k - 1) ^ 2 * W.ψ (k + 2) - W.ψ (k - 2) * W.ψ (k + 1) ^ 2 := by
  simp only [WeierstrassCurve.ψ, WeierstrassCurve.ψTwoMulQuotP]
  exact complEDS₂_mul_b W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) k

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 6: mk(ψ_m) ≠ 0
-- ═══════════════════════════════════════════════════════════════════

omit [Invertible (2 : R)] in
private lemma mk_ψ_ne_zero' (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0)
    (m : ℤ) (hm : m ≠ 0) :
    AdjoinRoot.mk W.toAffine.polynomial (W.ψ m) ≠ 0 := by
  rw [Affine.CoordinateRing.mk_ψ]
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    have h2 := hψ_ne 2 (by omega); rwa [ψ_two] at h2
  have hΨ_ne : W.Ψ m ≠ 0 := by
    rw [WeierstrassCurve.Ψ]
    have hC : Polynomial.C (W.preΨ m) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (W.preΨ_ne_zero (hcast m hm))
    by_cases heven : Even m
    · simp only [heven, ↓reduceIte]; exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]; exact hC
  have hΨ_deg : (W.Ψ m).natDegree < W.toAffine.polynomial.natDegree := by
    rw [Affine.natDegree_polynomial, WeierstrassCurve.Ψ]
    by_cases heven : Even m
    · simp only [heven, ↓reduceIte]
      calc (Polynomial.C (W.preΨ m) * W.ψ₂).natDegree
          ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
            (Nat.add_le_add (Polynomial.natDegree_C _).le
              (by rw [WeierstrassCurve.ψ₂, Affine.polynomialY]; exact Polynomial.natDegree_linear_le))
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have : (Polynomial.C (W.preΨ m)).natDegree = 0 := Polynomial.natDegree_C _; omega
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt Affine.monic_polynomial hΨ_ne hΨ_deg

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 7: cc(2)·cc(⅟2) = 1
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] in
private lemma cc2_half : Polynomial.C (Polynomial.C (2 : R)) *
    Polynomial.C (Polynomial.C (⅟(2 : R))) = (1 : R[X][X]) := by
  rw [← map_mul, ← map_mul, mul_invOf_self, map_one, map_one]

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 8: 2 · ωP unfolded
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] in
private lemma two_ωP_expand (n : ℤ) :
    (2 : R[X][X]) * W.ωP n =
    W.ψTwoMulQuotP n - W.ψ n *
      (Polynomial.C (Polynomial.C W.a₁) *
        (Polynomial.C (Polynomial.X : R[X]) * W.ψ n ^ 2 -
         W.ψ (n + 1) * W.ψ (n - 1)) +
       Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2) := by
  unfold WeierstrassCurve.ωP WeierstrassCurve.φ
  have hcc2 : Polynomial.C (Polynomial.C (2 : R)) = (2 : R[X][X]) := by
    simp [map_ofNat]
  rw [← hcc2]
  calc Polynomial.C (Polynomial.C (2 : R)) *
      (Polynomial.C (Polynomial.C (⅟(2 : R))) *
        (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) *
            (Polynomial.C (Polynomial.X : R[X]) * W.ψ n ^ 2 -
             W.ψ (n + 1) * W.ψ (n - 1)) +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)))
      = Polynomial.C (Polynomial.C (2 : R)) * Polynomial.C (Polynomial.C (⅟(2 : R))) *
        (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) *
            (Polynomial.C (Polynomial.X : R[X]) * W.ψ n ^ 2 -
             W.ψ (n + 1) * W.ψ (n - 1)) +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)) := by ring
    _ = 1 * (W.ψTwoMulQuotP n - W.ψ n *
          (Polynomial.C (Polynomial.C W.a₁) *
            (Polynomial.C (Polynomial.X : R[X]) * W.ψ n ^ 2 -
             W.ψ (n + 1) * W.ψ (n - 1)) +
           Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 2)) := by
      rw [cc2_half]
    _ = _ := by ring

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 9: ψ₂ definition
-- ═══════════════════════════════════════════════════════════════════

omit [IsDomain R] [Invertible (2 : R)] in
private lemma psi2_def : W.ψ₂ = 2 * (Polynomial.X : R[X][X]) +
    Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
    Polynomial.C (Polynomial.C W.a₃) := by
  unfold WeierstrassCurve.ψ₂ Affine.polynomialY; simp [map_ofNat]; ring

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 10: Key polynomial identity
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 128000000 in
omit [IsDomain R] in
private lemma two_psi2_E_identity (m : ℤ) :
    (2 : R[X][X]) * W.ψ₂ *
      (((Polynomial.X : R[X][X]) * W.ψ m ^ 3 - W.ωP m) * W.ψ (m + 2) -
       W.ψ (m - 1) * ((Polynomial.X : R[X][X]) * W.ψ (m + 1) ^ 3 +
         Polynomial.C (Polynomial.C W.a₁) *
           (Polynomial.C (Polynomial.X : R[X]) * W.ψ (m + 1) ^ 2 -
            W.ψ (m + 2) * W.ψ m) * W.ψ (m + 1) +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ (m + 1) ^ 3 + W.ωP (m + 1))) =
    -(W.ψ m ^ 2 * W.ψ (m + 3) * W.ψ (m - 1) -
      W.ψ (m - 2) * W.ψ (m + 1) ^ 2 * W.ψ (m + 2) -
      W.ψ₂ ^ 2 * (W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3))
    - W.ψ (m + 2) * (W.ψTwoMulQuotP m * W.ψ₂ -
        (W.ψ (m - 1) ^ 2 * W.ψ (m + 2) - W.ψ (m - 2) * W.ψ (m + 1) ^ 2))
    - W.ψ (m - 1) * (W.ψTwoMulQuotP (m + 1) * W.ψ₂ -
        (W.ψ m ^ 2 * W.ψ (m + 3) - W.ψ (m - 1) * W.ψ (m + 2) ^ 2)) := by
  have h1 := two_ωP_expand W m
  have h2 := two_ωP_expand W (m + 1)
  conv at h2 =>
    rw [show (m + 1 : ℤ) + 1 = m + 2 from by ring,
        show (m + 1 : ℤ) - 1 = m from by ring]
  rw [psi2_def W]
  linear_combination (norm := ring)
    -(2 * (Polynomial.X : R[X][X]) +
      Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
      Polynomial.C (Polynomial.C W.a₃)) * W.ψ (m + 2) * h1
    - (2 * (Polynomial.X : R[X][X]) +
       Polynomial.C (Polynomial.C W.a₁) * Polynomial.C (Polynomial.X : R[X]) +
       Polynomial.C (Polynomial.C W.a₃)) * W.ψ (m - 1) * h2

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 11: CR identity mk(E) = 0
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 32000000 in
private lemma mk_E_eq_zero
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0) (m : ℤ) :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (((Polynomial.X : R[X][X]) * W.ψ m ^ 3 - W.ωP m) * W.ψ (m + 2) -
       W.ψ (m - 1) * ((Polynomial.X : R[X][X]) * W.ψ (m + 1) ^ 3 +
         Polynomial.C (Polynomial.C W.a₁) *
           (Polynomial.C (Polynomial.X : R[X]) * W.ψ (m + 1) ^ 2 -
            W.ψ (m + 2) * W.ψ m) * W.ψ (m + 1) +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ (m + 1) ^ 3 + W.ωP (m + 1))) = 0 := by
  set A := AdjoinRoot.mk W.toAffine.polynomial
  set E := ((Polynomial.X : R[X][X]) * W.ψ m ^ 3 - W.ωP m) * W.ψ (m + 2) -
       W.ψ (m - 1) * ((Polynomial.X : R[X][X]) * W.ψ (m + 1) ^ 3 +
         Polynomial.C (Polynomial.C W.a₁) *
           (Polynomial.C (Polynomial.X : R[X]) * W.ψ (m + 1) ^ 2 -
            W.ψ (m + 2) * W.ψ m) * W.ψ (m + 1) +
         Polynomial.C (Polynomial.C W.a₃) * W.ψ (m + 1) ^ 3 + W.ωP (m + 1))
  suffices h : A ((2 : R[X][X]) * W.ψ₂ * E) = 0 by
    simp only [map_mul, map_ofNat] at h
    have h2_ne : (2 : AdjoinRoot W.toAffine.polynomial) ≠ 0 := by
      have : IsUnit (2 : R) := isUnit_of_invertible 2
      exact (((this.map (Polynomial.C : R →+* R[X])).map
        (Polynomial.C : R[X] →+* R[X][X])).map A).ne_zero
    have hψ₂_ne : A W.ψ₂ ≠ 0 := by
      rw [← ψ_two]; exact mk_ψ_ne_zero' W hψ_ne hcast 2 (by omega)
    exact mul_left_cancel₀ (mul_ne_zero h2_ne hψ₂_ne) (by rw [h, mul_zero])
  have h_poly := two_psi2_E_identity W m
  rw [h_poly]
  simp only [map_neg, map_sub, map_mul, map_pow]
  have h_eds := eds_shifted_identity W m
  have h_tmq := psiTMQ_mul_psi2 W m
  have h_tmq1 := psiTMQ_mul_psi2 W (m + 1)
  conv at h_tmq1 =>
    rw [show (m + 1 : ℤ) - 1 = m from by ring,
        show (m + 1 : ℤ) - 2 = m - 1 from by ring,
        show (m + 1 : ℤ) + 1 = m + 2 from by ring,
        show (m + 1 : ℤ) + 2 = m + 3 from by ring]
  have h_odd : W.ψ (2 * m + 1) = W.ψ (m + 2) * W.ψ m ^ 3 -
      W.ψ (m - 1) * W.ψ (m + 1) ^ 3 := by
    rw [WeierstrassCurve.ψ]
    exact normEDS_odd W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) m
  have hA_eds := congrArg A h_eds
  have hA_tmq := congrArg A h_tmq
  have hA_tmq1 := congrArg A h_tmq1
  have hA_odd := congrArg A h_odd
  simp only [map_sub, map_mul, map_pow] at hA_eds hA_tmq hA_tmq1 hA_odd
  linear_combination (norm := ring)
    -hA_eds + -1 * A W.ψ₂ ^ 2 * hA_odd
    - A (W.ψ (m + 2)) * hA_tmq
    - A (W.ψ (m - 1)) * hA_tmq1

-- ═══════════════════════════════════════════════════════════════════
-- LEMMA 12: Factoring identity in the CR
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 400000000 in
private lemma mk_factoring
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0) (m : ℤ) :
    let A := AdjoinRoot.mk W.toAffine.polynomial
    A ((addY W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 3 * W.ωP (m + 1)) * W.ψ m ^ 3) = 0 := by
  set A := AdjoinRoot.mk W.toAffine.polynomial
  have h_negAddY := negAddY_factored W m
  have h_phi := phi_minus_x_psi_sq W (m + 1)
  conv at h_phi =>
    rw [show (m + 1 : ℤ) + 1 = m + 2 from by ring,
        show (m + 1 : ℤ) - 1 = m from by ring]
  have h_addX := mk_addX_divPoly_general W hψ_ne hcast m
  have h_addX_expanded : A (addX W.toPoly
      (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
      (![W.φ m, W.ωP m, W.ψ m])) =
    A (W.ψ (m - 1)) ^ 2 * A (Polynomial.C (Polynomial.X : R[X])) * A (W.ψ (m + 1)) ^ 2 -
    A (W.ψ (m - 1)) ^ 2 * A (W.ψ (m + 2)) * A (W.ψ m) := by
    have h' : A (addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m])) =
      A (W.ψ (m - 1) ^ 2 * W.φ (m + 1)) := by
      have := congrArg A (show addX W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) =
        (addX W.toPoly
          (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
          (![W.φ m, W.ωP m, W.ψ m]) - W.ψ (m - 1) ^ 2 * W.φ (m + 1)) +
        W.ψ (m - 1) ^ 2 * W.φ (m + 1) from by ring)
      rw [map_add, h_addX, zero_add] at this; exact this
    have hA_phi := congrArg A h_phi
    simp only [map_sub, map_mul, map_neg, map_pow] at hA_phi h'
    rw [h']; linear_combination A (W.ψ (m - 1)) ^ 2 * hA_phi
  have h_E := mk_E_eq_zero W hψ_ne hcast m
  have hA_negAddY := congrArg A h_negAddY
  simp only [map_mul, map_sub, map_add, map_pow] at hA_negAddY
  simp only [map_sub, map_mul, map_add, map_pow] at h_E
  rw [h_addX_expanded] at hA_negAddY
  rw [addY_expand W m]
  simp only [map_mul, map_sub, map_neg, map_add, map_pow]
  rw [h_addX_expanded]
  linear_combination (norm := ring)
    -hA_negAddY + A (W.ψ m) ^ 3 * A (W.ψ (m - 1)) ^ 2 * h_E

-- ═══════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 16000000 in
/-- **ATOM 4b (general m).** Y-component projective identity for ALL m.
In the coordinate ring R[W], the Y-coordinate of the formal addition
P + [m]P equals ψ_{m-1}³ · ωP_{m+1}. -/
theorem mk_addY_divPoly_general (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hcast : ∀ (k : ℤ), k ≠ 0 → (k : R) ≠ 0) (m : ℤ) :
    (AdjoinRoot.mk W.toAffine.polynomial)
      (addY W.toPoly
        (![Polynomial.C (Polynomial.X : R[X]), (Polynomial.X : R[X][X]), 1])
        (![W.φ m, W.ωP m, W.ψ m]) -
       W.ψ (m - 1) ^ 3 * W.ωP (m + 1)) = 0 := by
  set A := AdjoinRoot.mk W.toAffine.polynomial
  by_cases hm : m = 0
  · subst hm
    simp only [ψ_zero, φ_zero, show (0 : ℤ) - 1 = -1 from by ring,
      show (0 : ℤ) + 1 = 1 from by ring, ψ_neg, ψ_one]
    simp only [addY, negY_eq, addX, negAddY, addZ, Matrix.cons_val]
    simp only [WeierstrassCurve.toPoly, WeierstrassCurve.map, RingHom.comp_apply]
    simp only [WeierstrassCurve.ωP, WeierstrassCurve.ψTwoMulQuotP, WeierstrassCurve.φ,
      ψ_zero, ψ_one, complEDS₂_zero, complEDS₂_one, WeierstrassCurve.ψ₂,
      Affine.polynomialY, map_ofNat]
    ring_nf
    simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, ψ_zero, map_zero]
    have h2t : 2 * A (Polynomial.C (Polynomial.C (⅟(2:R)))) = 1 := by
      change A (Polynomial.C (Polynomial.C 2)) * A (Polynomial.C (Polynomial.C (⅟(2:R)))) = 1
      show A (Polynomial.C (Polynomial.C 2) * Polynomial.C (Polynomial.C (⅟(2:R)))) = 1
      rw [show Polynomial.C (Polynomial.C (2:R)) * Polynomial.C (Polynomial.C (⅟(2:R))) =
        Polynomial.C (Polynomial.C ((2:R) * ⅟(2:R))) from by rw [map_mul, map_mul]]
      rw [mul_invOf_self, map_one, map_one, map_one]
    linear_combination
      -((4 * A (Polynomial.C (Polynomial.C (⅟(2:R)))) + 1) * A X +
        (2 * A (Polynomial.C (Polynomial.C (⅟(2:R)))) + 1) *
          (A (Polynomial.C (Polynomial.C W.a₁)) * A (Polynomial.C (Polynomial.X : R[X])) +
           A (Polynomial.C (Polynomial.C W.a₃)))) * h2t
  · have h_fact := mk_factoring W hψ_ne hcast m
    have hψ_ne_m := mk_ψ_ne_zero' W hψ_ne hcast m hm
    simp only at h_fact
    rw [map_mul, map_sub, map_mul, map_pow] at h_fact
    have hψ3_ne : A (W.ψ m) ^ 3 ≠ 0 := pow_ne_zero 3 hψ_ne_m
    exact (mul_eq_zero.mp h_fact).resolve_right hψ3_ne

end GeneralM

#print axioms mk_addY_divPoly_general
