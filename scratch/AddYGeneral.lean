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
-- MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════════

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
  sorry

end GeneralM

#print axioms mk_addY_divPoly_general
