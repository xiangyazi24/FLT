import scratch.KeystoneDoubling
import scratch.PsiInvariant

open Polynomial
open scoped Polynomial
open FLT.EDS

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

-- Assumed already defined in your file:
-- def dupDenP (W : WeierstrassCurve R) (Xc Zc : R[X]) : R[X] := ...
-- def dupNumP (W : WeierstrassCurve R) (Xc Zc : R[X]) : R[X] := ...

private lemma bRel_poly (W : WeierstrassCurve R) :
    C W.b₂ * C W.b₆ - (C W.b₄)^2 - C (4 : R) * C W.b₈ = (0 : R[X]) := by
  have hb0 : W.b₂ * W.b₆ - W.b₄^2 - (4 : R) * W.b₈ = 0 := by
    have hb := b_relation (W := W)
    -- hb : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄^2
    rw [← hb]
    ring
  have hbC := congrArg (fun z : R => (C z : R[X])) hb0
  simpa [map_sub, map_mul, map_pow] using hbC

private lemma preΨ_adjacent_somos_res
    (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0) (m : ℤ) :
    W.preΨ (m - 2) * W.preΨ (m + 2)
      - (if Even m then 1 else W.Ψ₂Sq^2) *
          (W.preΨ (m - 1) * W.preΨ (m + 1))
      + W.Ψ₃ * W.preΨ m^2 = 0 := by
  have h := preΨ_adjacent_somos W h4 m
  linear_combination (norm := ring_nf) h

private lemma preΨ_invariant_res
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (m : ℤ) :
    W.Ψ₃ *
        (W.preΨ (m + 2) * W.preΨ (m - 1)^2
          + W.preΨ (m + 1)^2 * W.preΨ (m - 2)
          + (if Even m then W.Ψ₂Sq^2 else 1) * W.preΨ m^3)
      - (W.preΨ₄ + W.Ψ₂Sq^2) *
          (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) = 0 := by
  have h := preΨ_invariant_raw W h4 hψ_ne m
  linear_combination (norm := ring_nf) h

private lemma preΨ_2m_add_one_even
    (W : WeierstrassCurve R) {m : ℤ} (hm : Even m) :
    W.preΨ (2*m + 1)
      = W.preΨ (m + 2) * W.preΨ m^3 * W.Ψ₂Sq^2
        - W.preΨ (m - 1) * W.preΨ (m + 1)^3 := by
  rw [W.preΨ_odd m]; simp [hm]

private lemma preΨ_2m_sub_one_even
    (W : WeierstrassCurve R) {m : ℤ} (hm_m1 : ¬ Even (m - 1)) :
    W.preΨ (2*m - 1)
      = W.preΨ (m + 1) * W.preΨ (m - 1)^3
        - W.preΨ (m - 2) * W.preΨ m^3 * W.Ψ₂Sq^2 := by
  have h := W.preΨ_odd (m - 1)
  rw [show 2 * (m - 1) + 1 = 2*m - 1 by ring] at h
  rw [h]; simp [hm_m1]; ring

private lemma preΨ_2m_add_one_odd
    (W : WeierstrassCurve R) {m : ℤ} (hm : ¬ Even m) :
    W.preΨ (2*m + 1)
      = W.preΨ (m + 2) * W.preΨ m^3
        - W.preΨ (m - 1) * W.preΨ (m + 1)^3 * W.Ψ₂Sq^2 := by
  rw [W.preΨ_odd m]; simp [hm]

private lemma preΨ_2m_sub_one_odd
    (W : WeierstrassCurve R) {m : ℤ} (hm_m1 : Even (m - 1)) :
    W.preΨ (2*m - 1)
      = W.preΨ (m + 1) * W.preΨ (m - 1)^3 * W.Ψ₂Sq^2
        - W.preΨ (m - 2) * W.preΨ m^3 := by
  have h := W.preΨ_odd (m - 1)
  rw [show 2 * (m - 1) + 1 = 2*m - 1 by ring] at h
  rw [h]; simp [hm_m1]; ring

private lemma ΨSq_two_mul_sat_even
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : Even m) :
    W.Ψ₃ * (W.ΨSq (2*m) - dupDenP W (W.Φ m) (W.ΨSq m)) = 0 := by
  have hAdj := preΨ_adjacent_somos_res W h4 m
  have hInv := preΨ_invariant_res W h4 hψ_ne m
  have hb := bRel_poly W
  have h2m : Even (2*m) := ⟨m, by ring⟩

  let Pm2 : R[X] := W.preΨ (m - 2)
  let Pm1 : R[X] := W.preΨ (m - 1)
  let P0  : R[X] := W.preΨ m
  let P1  : R[X] := W.preΨ (m + 1)
  let P2  : R[X] := W.preΨ (m + 2)
  let s   : R[X] := W.Ψ₂Sq
  let c3  : R[X] := W.Ψ₃
  let d4  : R[X] := W.preΨ₄
  let ell : R[X] := (6 : R[X]) * X^2 + C W.b₂ * X + C W.b₄
  let rho0 : R[X] :=
    (9 : R[X]) * X^4 + (2 : R[X]) * C W.b₂ * X^3
      + (4 : R[X]) * C W.b₄ * X^2 + (3 : R[X]) * C W.b₆ * X + C W.b₈

  rw [W.ΨSq_even m]
  linear_combination (norm :=
    (simp only [dupDenP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      Pm2, Pm1, P0, P1, P2, s, c3, d4, ell, rho0, hm, h2m, if_true, if_false, ite_true, ite_false, mul_one, one_mul, map_mul, map_ofNat, map_pow, map_add, map_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
      (-(4 : R[X]) * P0^2 * P1^2 * Pm1^2 * s * c3) * hAdj
    + ((-P0^2 * s * (P0^3 * s^2 - P0 * P1 * Pm1 * ell - P1^2 * Pm2)
          + P0^2 * Pm1^2 * s * P2) * hInv)
    + ((P0^3 * P1 * Pm1 * s
          * (P0^3 * s^2 * X^2
              - P0 * P1 * Pm1 * rho0
              - P1^2 * Pm2 * X^2
              - P2 * Pm1^2 * X^2)) * hb)

private lemma Φ_two_mul_sat_even
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : Even m) :
    W.Ψ₃ * (W.Φ (2*m) - dupNumP W (W.Φ m) (W.ΨSq m)) = 0 := by
  have hAdj := preΨ_adjacent_somos_res W h4 m
  have hInv := preΨ_invariant_res W h4 hψ_ne m
  have hb := bRel_poly W
  have h2m : Even (2*m) := ⟨m, by ring⟩
  have hm_m1 : ¬ Even (m - 1) := by rw [Int.even_sub_one, not_not]; exact hm
  have hp := preΨ_2m_add_one_even W hm
  have hm' := preΨ_2m_sub_one_even W hm_m1

  let Pm2 : R[X] := W.preΨ (m - 2)
  let Pm1 : R[X] := W.preΨ (m - 1)
  let P0  : R[X] := W.preΨ m
  let P1  : R[X] := W.preΨ (m + 1)
  let P2  : R[X] := W.preΨ (m + 2)
  let s   : R[X] := W.Ψ₂Sq
  let c3  : R[X] := W.Ψ₃
  let d4  : R[X] := W.preΨ₄
  let eta : R[X] := C W.b₆ + C W.b₄ * X - (2 : R[X]) * X^3
  let rho1 : R[X] :=
    (5 : R[X]) * X^4 + C W.b₂ * X^3
      + (2 : R[X]) * C W.b₄ * X^2 + (2 : R[X]) * C W.b₆ * X + C W.b₈

  rw [WeierstrassCurve.Φ]
  rw [W.ΨSq_even m]
  rw [hp, hm']
  linear_combination (norm :=
    (simp only [dupNumP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      Pm2, Pm1, P0, P1, P2, s, c3, d4, eta, rho1, hm, h2m, if_true, if_false, ite_true, ite_false, mul_one, one_mul, map_mul, map_ofNat, map_pow, map_add, map_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
      (P0^2 * s * c3 * (P0^4 * s^3 - (4 : R[X]) * P1^2 * Pm1^2 * X)) * hAdj
    + ((-P0^2 * s * (P0^3 * s^2 * X + P0 * P1 * Pm1 * eta - P1^2 * Pm2 * X)
          + P0^2 * Pm1^2 * X * s * P2) * hInv)
    + ((P0^3 * P1 * Pm1 * X * s
          * (P0^3 * s^2 * X^2
              - P0 * P1 * Pm1 * rho1
              - P1^2 * Pm2 * X^2
              - P2 * Pm1^2 * X^2)) * hb)

private lemma ΨSq_two_mul_sat_odd
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * (W.ΨSq (2*m) - dupDenP W (W.Φ m) (W.ΨSq m)) = 0 := by
  have hAdj := preΨ_adjacent_somos_res W h4 m
  have hInv := preΨ_invariant_res W h4 hψ_ne m
  have hb := bRel_poly W
  have h2m : Even (2*m) := ⟨m, by ring⟩

  let Pm2 : R[X] := W.preΨ (m - 2)
  let Pm1 : R[X] := W.preΨ (m - 1)
  let P0  : R[X] := W.preΨ m
  let P1  : R[X] := W.preΨ (m + 1)
  let P2  : R[X] := W.preΨ (m + 2)
  let s   : R[X] := W.Ψ₂Sq
  let c3  : R[X] := W.Ψ₃
  let d4  : R[X] := W.preΨ₄
  let ell : R[X] := (6 : R[X]) * X^2 + C W.b₂ * X + C W.b₄
  let rho0 : R[X] :=
    (9 : R[X]) * X^4 + (2 : R[X]) * C W.b₂ * X^3
      + (4 : R[X]) * C W.b₄ * X^2 + (3 : R[X]) * C W.b₆ * X + C W.b₈

  rw [W.ΨSq_even m]
  linear_combination (norm :=
    (simp only [dupDenP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      Pm2, Pm1, P0, P1, P2, s, c3, d4, ell, rho0, hm, h2m, if_true, if_false, ite_true, ite_false, mul_one, one_mul, map_mul, map_ofNat, map_pow, map_add, map_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
      (-(4 : R[X]) * P0^2 * P1^2 * Pm1^2 * s * c3) * hAdj
    + ((P0^2 * s * (-P0^3 + P0 * P1 * Pm1 * ell + P1^2 * Pm2)
          + P0^2 * Pm1^2 * s * P2) * hInv)
    + ((P0^3 * P1 * Pm1 * s
          * (P0^3 * X^2
              - P0 * P1 * Pm1 * rho0
              - P1^2 * Pm2 * X^2
              - P2 * Pm1^2 * X^2)) * hb)

private lemma Φ_two_mul_sat_odd
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * (W.Φ (2*m) - dupNumP W (W.Φ m) (W.ΨSq m)) = 0 := by
  have hAdj := preΨ_adjacent_somos_res W h4 m
  have hInv := preΨ_invariant_res W h4 hψ_ne m
  have hb := bRel_poly W
  have h2m : Even (2*m) := ⟨m, by ring⟩
  have hm_m1 : Even (m - 1) := by rw [Int.even_sub_one]; exact hm
  have hp := preΨ_2m_add_one_odd W hm
  have hm' := preΨ_2m_sub_one_odd W hm_m1

  let Pm2 : R[X] := W.preΨ (m - 2)
  let Pm1 : R[X] := W.preΨ (m - 1)
  let P0  : R[X] := W.preΨ m
  let P1  : R[X] := W.preΨ (m + 1)
  let P2  : R[X] := W.preΨ (m + 2)
  let s   : R[X] := W.Ψ₂Sq
  let c3  : R[X] := W.Ψ₃
  let d4  : R[X] := W.preΨ₄
  let eta : R[X] := C W.b₆ + C W.b₄ * X - (2 : R[X]) * X^3
  let rho1 : R[X] :=
    (5 : R[X]) * X^4 + C W.b₂ * X^3
      + (2 : R[X]) * C W.b₄ * X^2 + (2 : R[X]) * C W.b₆ * X + C W.b₈

  rw [WeierstrassCurve.Φ]
  rw [W.ΨSq_even m]
  rw [hp, hm']
  linear_combination (norm :=
    (simp only [dupNumP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      Pm2, Pm1, P0, P1, P2, s, c3, d4, eta, rho1, hm, h2m, if_true, if_false, ite_true, ite_false, mul_one, one_mul, map_mul, map_ofNat, map_pow, map_add, map_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
      (P0^2 * c3 * (P0^4 - (4 : R[X]) * P1^2 * Pm1^2 * X * s)) * hAdj
    + ((P0^2 * s * (-P0^3 * X - P0 * P1 * Pm1 * eta + P1^2 * Pm2 * X)
          + P0^2 * Pm1^2 * X * s * P2) * hInv)
    + ((P0^3 * P1 * Pm1 * X * s
          * (P0^3 * X^2
              - P0 * P1 * Pm1 * rho1
              - P1^2 * Pm2 * X^2
              - P2 * Pm1^2 * X^2)) * hb)

/-- Denominator part of x-coordinate doubling for division polynomials. -/
lemma ΨSq_two_mul
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (m : ℤ) :
    W.ΨSq (2*m) = dupDenP W (W.Φ m) (W.ΨSq m) := by
  apply sub_eq_zero.mp
  have hsat : W.Ψ₃ * (W.ΨSq (2*m) - dupDenP W (W.Φ m) (W.ΨSq m)) = 0 := by
    by_cases hm : Even m
    · exact ΨSq_two_mul_sat_even W h4 hψ_ne hm
    · exact ΨSq_two_mul_sat_odd W h4 hψ_ne hm
  exact (mul_eq_zero.mp hsat).resolve_left hc3

/-- Numerator part of x-coordinate doubling for division polynomials. -/
lemma Φ_two_mul
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (m : ℤ) :
    W.Φ (2*m) = dupNumP W (W.Φ m) (W.ΨSq m) := by
  apply sub_eq_zero.mp
  have hsat : W.Ψ₃ * (W.Φ (2*m) - dupNumP W (W.Φ m) (W.ΨSq m)) = 0 := by
    by_cases hm : Even m
    · exact Φ_two_mul_sat_even W h4 hψ_ne hm
    · exact Φ_two_mul_sat_odd W h4 hψ_ne hm
  exact (mul_eq_zero.mp hsat).resolve_left hc3

end

end WeierstrassCurve
