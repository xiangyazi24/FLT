import scratch.KeystoneDoubling
import scratch.PsiInvariant

/-!
# Keystone differential addition — the x-only diff-add duplication identity (odd index).

`ΨSq (2m+1) = deltaP²` (definitional, `ΨSq_odd`) and the numerator analogue
`Φ (2m+1) = sumNumP − deltaP²·X` via a Ψ₃-saturated `linear_combination` over
`preΨ_adjacent_somos` (Adj) + `preΨ_invariant` (Inv) at m and m+1 + `b_relation` (bRel),
then cancel `Ψ₃≠0`.  Design: ChatGPT dm1 git-drop a3191d16; cofactors CAS-extracted here.
-/

open Polynomial
open scoped Polynomial
open FLT.EDS

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `deltaP = X0·Z1 − X1·Z0` on `R[X]` representatives. -/
noncomputable def deltaP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  X0 * Z1 - X1 * Z0

/-- Homogeneous numerator for `x₊ + x₋` on `R[X]` representatives. -/
noncomputable def sumNumP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  C (2 : R) * X0 * X1 * (X0 * Z1 + X1 * Z0)
    + C W.b₂ * X0 * X1 * Z0 * Z1
    + C W.b₄ * Z0 * Z1 * (X0 * Z1 + X1 * Z0)
    + C W.b₆ * Z0 ^ 2 * Z1 ^ 2

/-- x-only differential-addition numerator on representatives. -/
noncomputable def diffAddNumP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  sumNumP W X0 Z0 X1 Z1 - (deltaP W X0 Z0 X1 Z1) ^ 2 * X

/-- x-only differential-addition denominator on representatives. -/
noncomputable def diffAddDenP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  (deltaP W X0 Z0 X1 Z1) ^ 2

/-- Eval bridge for `deltaP`. -/
lemma deltaP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (deltaP W X0 Z0 X1 Z1).eval x = X0.eval x * Z1.eval x - X1.eval x * Z0.eval x := by
  simp only [deltaP, eval_sub, eval_mul]

/-- Eval bridge for `sumNumP`. -/
lemma sumNumP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (sumNumP W X0 Z0 X1 Z1).eval x =
      2 * X0.eval x * X1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₂ * X0.eval x * X1.eval x * Z0.eval x * Z1.eval x
        + W.b₄ * Z0.eval x * Z1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₆ * (Z0.eval x) ^ 2 * (Z1.eval x) ^ 2 := by
  simp only [sumNumP, eval_add, eval_mul, eval_pow, eval_C]

/-- Eval bridge for `diffAddNumP`. -/
lemma diffAddNumP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (diffAddNumP W X0 Z0 X1 Z1).eval x =
      (sumNumP W X0 Z0 X1 Z1).eval x - ((deltaP W X0 Z0 X1 Z1).eval x) ^ 2 * x := by
  simp only [diffAddNumP, eval_sub, eval_mul, eval_pow, eval_X]

/-- Eval bridge for `diffAddDenP`. -/
lemma diffAddDenP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (diffAddDenP W X0 Z0 X1 Z1).eval x = ((deltaP W X0 Z0 X1 Z1).eval x) ^ 2 := by
  simp only [diffAddDenP, eval_pow]

private lemma bRel_poly (W : WeierstrassCurve R) :
    C W.b₂ * C W.b₆ - (C W.b₄) ^ 2 - C (4 : R) * C W.b₈ = (0 : R[X]) := by
  have hb0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - (4 : R) * W.b₈ = 0 := by
    have hb := b_relation (W := W); rw [← hb]; ring
  have hbC := congrArg (fun z : R => (C z : R[X])) hb0
  simpa [map_sub, map_mul, map_pow] using hbC

private lemma preΨ_adjacent_somos_res (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0) (m : ℤ) :
    W.preΨ (m - 2) * W.preΨ (m + 2)
      - (if Even m then 1 else W.Ψ₂Sq ^ 2) * (W.preΨ (m - 1) * W.preΨ (m + 1))
      + W.Ψ₃ * W.preΨ m ^ 2 = 0 := by
  have h := preΨ_adjacent_somos W h4 m
  linear_combination (norm := ring_nf) h

private lemma preΨ_invariant_res (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    W.Ψ₃ * (W.preΨ (m + 2) * W.preΨ (m - 1) ^ 2 + W.preΨ (m + 1) ^ 2 * W.preΨ (m - 2)
          + (if Even m then W.Ψ₂Sq ^ 2 else 1) * W.preΨ m ^ 3)
      - (W.preΨ₄ + W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) = 0 := by
  have h := preΨ_invariant_raw W h4 hψ_ne m
  linear_combination (norm := ring_nf) h

private lemma preΨ_2m_add_one_even (W : WeierstrassCurve R) {m : ℤ} (hm : Even m) :
    W.preΨ (2 * m + 1)
      = W.preΨ (m + 2) * W.preΨ m ^ 3 * W.Ψ₂Sq ^ 2 - W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 := by
  simpa [hm] using W.preΨ_odd m

private lemma preΨ_2m_add_one_odd (W : WeierstrassCurve R) {m : ℤ} (hm : ¬ Even m) :
    W.preΨ (2 * m + 1)
      = W.preΨ (m + 2) * W.preΨ m ^ 3 - W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * W.Ψ₂Sq ^ 2 := by
  simpa [hm] using W.preΨ_odd m

private lemma preΨ_2m_even (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (2 * m)
      = W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2)
        - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 := W.preΨ_even m

private lemma preΨ_2m_add_two (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (2 * m + 2)
      = W.preΨ m ^ 2 * W.preΨ (m + 1) * W.preΨ (m + 3)
        - W.preΨ (m - 1) * W.preΨ (m + 1) * W.preΨ (m + 2) ^ 2 := by
  have h := W.preΨ_even (m + 1)
  rw [show (2 : ℤ) * (m + 1) = 2 * m + 2 by ring, show m + 1 - 1 = m by ring,
    show m + 1 + 2 = m + 3 by ring, show m + 1 - 2 = m - 1 by ring,
    show m + 1 + 1 = m + 2 by ring] at h
  rw [h]

/-- Denominator identity: `ΨSq(2m+1) = deltaP²`, purely definitional via `ΨSq_odd`. -/
lemma ΨSq_two_mul_add_one (W : WeierstrassCurve R) (m : ℤ) :
    W.ΨSq (2 * m + 1)
      = diffAddDenP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) := by
  by_cases hm : Even m
  · have hm1 : ¬ Even (m + 1) := by simp [Int.even_add_one, hm]
    rw [W.ΨSq_odd m]
    simp only [diffAddDenP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      if_pos hm, if_neg hm1, show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring]
    ring
  · have hm1 : Even (m + 1) := by simpa [Int.even_add_one, Int.not_even_iff_odd] using hm
    rw [W.ΨSq_odd m]
    simp only [diffAddDenP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      if_neg hm, if_pos hm1, show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring]
    ring


private lemma Φ_two_mul_add_one_sat_even (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) {m : ℤ} (hm : Even m) :
    W.Ψ₃ * (W.Φ (2 * m + 1)
        - diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))) = 0 := by
  have hAdj0 := preΨ_adjacent_somos_res W h4 m
  have hInv0 := preΨ_invariant_res W h4 hψ_ne m
  have hAdj1 := preΨ_adjacent_somos_res W h4 (m + 1)
  have hInv1 := preΨ_invariant_res W h4 hψ_ne (m + 1)
  have hb := bRel_poly W
  have hm1 : ¬ Even (m + 1) := by simp [Int.even_add_one, hm]
  have h2m1 : ¬ Even (2 * m + 1) := m.not_even_two_mul_add_one
  simp only [show m + 1 - 2 = m - 1 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 1 - 1 = m by ring, show m + 1 + 1 = m + 2 by ring,
    if_pos hm, if_neg hm1] at hAdj0 hInv0 hAdj1 hInv1
  rw [WeierstrassCurve.Φ, show (2 * m + 1 + 1 : ℤ) = 2 * m + 2 by ring,
    show (2 * m + 1 - 1 : ℤ) = 2 * m by ring, if_neg h2m1,
    W.ΨSq_odd m, preΨ_2m_even W m, preΨ_2m_add_two W m]
  linear_combination (norm :=
    (simp only [diffAddNumP, sumNumP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      show (m + 1 + 1 : ℤ) = m + 2 by ring, show (m + 1 - 1 : ℤ) = m by ring,
      hm, hm1, if_true, if_false, ite_true, ite_false, mul_one, one_mul,
      map_mul, map_ofNat, map_pow, map_add, map_sub,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
    (-(12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 7
          - (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (18 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (5 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (15 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (2 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)) * hAdj0
    + ((4 : R[X]) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X ^ 3
          + (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X ^ 2 * (C W.b₂)
          + (2 : R[X]) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X * (C W.b₄)
          + (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * (C W.b₆)) * hInv0
    + (-(36 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 7
          - (21 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (54 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (15 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (45 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (18 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (27 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₂) * (C W.b₆)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₄) ^ 2
          + (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₈)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄) ^ 3
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄) * (C W.b₈)
          + (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (8 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₈) ^ 2) * hAdj1
    + ((4 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂)
          + (2 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₄)
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * (C W.b₆)
          + (24 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 5
          + (10 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 4 * (C W.b₂)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₂) ^ 2
          + (16 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₂) * (C W.b₄)
          + (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₆)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₄) ^ 2
          + (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₈)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (C W.b₄) * (C W.b₆)
          - (64 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 9
          - (48 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 8 * (C W.b₂)
          - (12 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 7 * (C W.b₂) ^ 2
          - (96 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 7 * (C W.b₄)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 6 * (C W.b₂) ^ 3
          - (48 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 6 * (C W.b₂) * (C W.b₄)
          - (48 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 6 * (C W.b₆)
          - (6 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄)
          - (24 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 5 * (C W.b₂) * (C W.b₆)
          - (48 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 5 * (C W.b₄) ^ 2
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₆)
          - (12 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 2
          - (48 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 4 * (C W.b₄) * (C W.b₆)
          - (12 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (8 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 3 * (C W.b₄) ^ 3
          - (12 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 3 * (C W.b₆) ^ 2
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          - (12 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (6 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * (C W.b₆) ^ 3) * hInv1
    + (-(W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 5
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 3 * (C W.b₄)
          + (2 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 2 * (C W.b₆)
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X * (C W.b₈)
          - (54 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 7
          - (26 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (55 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (39 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (14 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (2 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (13 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 4 * (C W.b₂)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 3 * (C W.b₄)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 2 * (C W.b₆)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X * (C W.b₈)
          + (48 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 11
          + (40 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 10 * (C W.b₂)
          + (11 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 9 * (C W.b₂) ^ 2
          + (96 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 9 * (C W.b₄)
          + (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 8 * (C W.b₂) ^ 3
          + (52 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 8 * (C W.b₂) * (C W.b₄)
          + (72 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 8 * (C W.b₆)
          + (7 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 7 * (C W.b₂) ^ 2 * (C W.b₄)
          + (38 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 7 * (C W.b₂) * (C W.b₆)
          + (60 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 7 * (C W.b₄) ^ 2
          + (16 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 7 * (C W.b₈)
          + (5 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂) ^ 2 * (C W.b₆)
          + (16 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂) * (C W.b₄) ^ 2
          + (8 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂) * (C W.b₈)
          + (84 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₄) * (C W.b₆)
          + (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₈)
          + (22 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (12 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄) ^ 3
          + (16 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄) * (C W.b₈)
          + (27 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₆) ^ 2
          + (4 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (7 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₆) ^ 2
          + (24 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₆)
          + (8 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆) * (C W.b₈)
          + (2 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (4 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₈)
          + (15 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 2
          + (4 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + (3 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₆) ^ 3
          + (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2 * (C W.b₈)
          + (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 9
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 8 * (C W.b₂)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 6 * (C W.b₂) * (C W.b₄)
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 6 * (C W.b₆)
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₂) * (C W.b₆)
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₄) ^ 2
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 4 * (C W.b₂) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 4 * (C W.b₄) * (C W.b₆)
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (6 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 3 * (C W.b₆) ^ 2
          - (5 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 2 * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X * (C W.b₈) ^ 2) * hb

private lemma Φ_two_mul_add_one_sat_odd (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * (W.Φ (2 * m + 1)
        - diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))) = 0 := by
  have hAdj0 := preΨ_adjacent_somos_res W h4 m
  have hInv0 := preΨ_invariant_res W h4 hψ_ne m
  have hAdj1 := preΨ_adjacent_somos_res W h4 (m + 1)
  have hInv1 := preΨ_invariant_res W h4 hψ_ne (m + 1)
  have hb := bRel_poly W
  have hm1 : Even (m + 1) := by simpa [Int.even_add_one, Int.not_even_iff_odd] using hm
  have h2m1 : ¬ Even (2 * m + 1) := m.not_even_two_mul_add_one
  simp only [show m + 1 - 2 = m - 1 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 1 - 1 = m by ring, show m + 1 + 1 = m + 2 by ring,
    if_neg hm, if_pos hm1] at hAdj0 hInv0 hAdj1 hInv1
  rw [WeierstrassCurve.Φ, show (2 * m + 1 + 1 : ℤ) = 2 * m + 2 by ring,
    show (2 * m + 1 - 1 : ℤ) = 2 * m by ring, if_neg h2m1,
    W.ΨSq_odd m, preΨ_2m_even W m, preΨ_2m_add_two W m]
  linear_combination (norm :=
    (simp only [diffAddNumP, sumNumP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      show (m + 1 + 1 : ℤ) = m + 2 by ring, show (m + 1 - 1 : ℤ) = m by ring,
      hm, hm1, if_true, if_false, ite_true, ite_false, mul_one, one_mul,
      map_mul, map_ofNat, map_pow, map_add, map_sub,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow]; ring1))
    (-(12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 7
          - (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (18 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (5 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (15 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (2 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (W.preΨ (m - 1)) * (W.preΨ m) * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)) * hAdj0
    + ((4 : R[X]) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X ^ 3
          + (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X ^ 2 * (C W.b₂)
          + (2 : R[X]) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * X * (C W.b₄)
          + (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 3)) * (C W.b₆)) * hInv0
    + (-(36 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 7
          - (21 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (54 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (15 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (45 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (18 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (27 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₂) * (C W.b₆)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₄) ^ 2
          + (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 5 * (C W.b₈)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄) ^ 3
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄) * (C W.b₈)
          + (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (8 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₈) ^ 2) * hAdj1
    + ((4 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 3
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂)
          + (2 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * X * (C W.b₄)
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) * (W.preΨ (m + 1)) * (W.preΨ (m + 2)) * (C W.b₆)
          + (24 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 5
          + (10 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 4 * (C W.b₂)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₂) ^ 2
          + (16 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 3 * (C W.b₄)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₂) * (C W.b₄)
          + (6 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X ^ 2 * (C W.b₆)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₄) ^ 2
          + (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * X * (C W.b₈)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (C W.b₄) * (C W.b₆)
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 3
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X ^ 2 * (C W.b₂)
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * X * (C W.b₄)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) * (C W.b₆)) * hInv1
    + (-(W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 5
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 3 * (C W.b₄)
          + (2 : R[X]) * (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X ^ 2 * (C W.b₆)
          + (W.preΨ (m - 1)) ^ 2 * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) ^ 2 * X * (C W.b₈)
          - (54 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 7
          - (26 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 6 * (C W.b₂)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₂) ^ 2
          - (55 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 5 * (C W.b₄)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂) * (C W.b₄)
          - (39 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₆)
          - (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄) ^ 2
          - (14 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₈)
          - (2 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₂) * (C W.b₈)
          - (13 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₄) * (C W.b₆)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₄) * (C W.b₈)
          - (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * X * (C W.b₆) ^ 2
          - (W.preΨ (m - 1)) * (W.preΨ m) ^ 3 * (W.preΨ (m + 1)) ^ 3 * (W.preΨ (m + 2)) * (C W.b₆) * (C W.b₈)
          + (48 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 11
          + (40 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 10 * (C W.b₂)
          + (11 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 9 * (C W.b₂) ^ 2
          + (96 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 9 * (C W.b₄)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 8 * (C W.b₂) ^ 3
          + (52 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 8 * (C W.b₂) * (C W.b₄)
          + (72 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 8 * (C W.b₆)
          + (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 7 * (C W.b₂) ^ 2 * (C W.b₄)
          + (38 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 7 * (C W.b₂) * (C W.b₆)
          + (60 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 7 * (C W.b₄) ^ 2
          + (16 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 7 * (C W.b₈)
          + (5 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 6 * (C W.b₂) ^ 2 * (C W.b₆)
          + (16 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 6 * (C W.b₂) * (C W.b₄) ^ 2
          + (8 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 6 * (C W.b₂) * (C W.b₈)
          + (84 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 6 * (C W.b₄) * (C W.b₆)
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₈)
          + (22 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (12 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5 * (C W.b₄) ^ 3
          + (16 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5 * (C W.b₄) * (C W.b₈)
          + (27 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 5 * (C W.b₆) ^ 2
          + (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 4 * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (7 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 4 * (C W.b₂) * (C W.b₆) ^ 2
          + (24 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₆)
          + (8 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 4 * (C W.b₆) * (C W.b₈)
          + (2 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 3 * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₈)
          + (15 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 2
          + (4 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + (3 : R[X]) * (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X ^ 2 * (C W.b₆) ^ 3
          + (W.preΨ (m - 1)) * (W.preΨ m) ^ 2 * (W.preΨ (m + 1)) ^ 5 * X * (C W.b₆) ^ 2 * (C W.b₈)
          + (3 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 5
          + (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 4 * (C W.b₂)
          + (3 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 3 * (C W.b₄)
          + (3 : R[X]) * (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X ^ 2 * (C W.b₆)
          + (W.preΨ m) ^ 5 * (W.preΨ (m + 1)) ^ 2 * (W.preΨ (m + 2)) * X * (C W.b₈)
          + (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 9
          + (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 8 * (C W.b₂)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 6 * (C W.b₂) * (C W.b₄)
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 6 * (C W.b₆)
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₂) * (C W.b₆)
          - (3 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₄) ^ 2
          - (2 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 5 * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 4 * (C W.b₂) * (C W.b₈)
          - (9 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 4 * (C W.b₄) * (C W.b₆)
          - (4 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (6 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 3 * (C W.b₆) ^ 2
          - (5 : R[X]) * (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X ^ 2 * (C W.b₆) * (C W.b₈)
          - (W.preΨ m) ^ 4 * (W.preΨ (m + 1)) ^ 4 * X * (C W.b₈) ^ 2) * hb

/-- Numerator identity: `Φ(2m+1) = diffAddNumP`, after cancelling `Ψ₃≠0`. -/
lemma Φ_two_mul_add_one (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (hc3 : W.Ψ₃ ≠ 0) (m : ℤ) :
    W.Φ (2 * m + 1)
      = diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) := by
  apply sub_eq_zero.mp
  have hsat : W.Ψ₃ * (W.Φ (2 * m + 1)
        - diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))) = 0 := by
    by_cases hm : Even m
    · exact Φ_two_mul_add_one_sat_even W h4 hψ_ne hm
    · exact Φ_two_mul_add_one_sat_odd W h4 hψ_ne hm
  exact (mul_eq_zero.mp hsat).resolve_left hc3

/-- Projective differential-addition identity (scalar `c = 1`). -/
lemma diffAdd_projective_two_mul_add_one (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (hc3 : W.Ψ₃ ≠ 0) (m : ℤ) :
    W.Φ (2 * m + 1) * diffAddDenP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))
      = W.ΨSq (2 * m + 1) * diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) := by
  rw [ΨSq_two_mul_add_one W m, Φ_two_mul_add_one W h4 hψ_ne hc3 m]; ring

end

end WeierstrassCurve
