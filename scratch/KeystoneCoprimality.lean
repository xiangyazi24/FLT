import scratch.PsiSomos

/-!
# Keystone avenue (c): division-polynomial coprimality (non-circular)

Goal: `¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)` for an elliptic curve, WITHOUT
`xPair_ne_zero_of_isElliptic` (which is proved through the keystone induction).

This file establishes the **local-invertibility propagation core** (the `Ψ₃.eval x ≠ 0`
stratum): if two adjacent `preΨ` values vanish at `x` and `Ψ₃.eval x ≠ 0`, the gap-2
Somos relation centred at the shifted index forces the neighbouring `preΨ` square to
vanish, propagating the adjacent-zero pair toward `preΨ 1 = 1` (contradiction).

Design + verification: ChatGPT (dm1, git-drop 2f7ea375); the nonsingularity sublemma's
resultant certificate `resultant(Ψ₂Sq, Ψ₃) = -Δ²  (mod bRel)` was CAS-verified.
Remaining strata (`Ψ₃.eval x = 0` rank-3 apparition, `Ψ₂Sq.eval x = 0` 2-torsion, the
resultant certificates, and the index inductions) are isolated as named sorries below.
-/

open Polynomial
open scoped Polynomial
open FLT.EDS

set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

private abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k := (W.preΨ i).eval x
private abbrev sx (W : WeierstrassCurve k) (x : k) : k := W.Ψ₂Sq.eval x
private abbrev c3x (W : WeierstrassCurve k) (x : k) : k := W.Ψ₃.eval x

/-- `b_relation` in distributed-C form. -/
private lemma bRelC (W : WeierstrassCurve k) :
    C W.b₂ * C W.b₆ - (C W.b₄) ^ 2 - C 4 * C W.b₈ = (0 : k[X]) := by
  have h0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    have hb := W.b_relation; linear_combination -hb
  have := congrArg (fun z : k => (C z : k[X])) h0
  simpa [map_sub, map_mul, map_pow] using this

/-- Resultant/Bezout certificate `A·Ψ₂Sq + B·Ψ₃ = C(-Δ²)` (CAS-extracted, uses `b_relation`). -/
private lemma bezout_Ψ₂Sq_Ψ₃ (W : WeierstrassCurve k) :
    (-(6 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (6 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (12 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (252 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (216 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (288 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (972 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (81 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (72 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (351 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (108 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (432 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + X * (C W.b₂) ^ 4 * (C W.b₈)
          - (7 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (6 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (50 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (3 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (288 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (168 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (216 : k[X]) * X * (C W.b₄) ^ 4
          + (432 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (1134 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (192 : k[X]) * X * (C W.b₈) ^ 2
          + (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (4 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (3 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (7 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (36 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (16 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (108 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (432 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (729 : k[X]) * (C W.b₆) ^ 3) * W.Ψ₂Sq
      + ((8 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (8 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (16 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (336 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (288 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (384 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (1296 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (2 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (2 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (80 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (72 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (32 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (360 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (144 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (576 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (C W.b₂) ^ 4 * (C W.b₈)
          + (5 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (4 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (48 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (204 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (176 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (144 : k[X]) * (C W.b₄) ^ 4
          - (384 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (864 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (256 : k[X]) * (C W.b₈) ^ 2) * W.Ψ₃
      = C (- W.Δ ^ 2) := by
  have hb := bRelC W
  linear_combination (norm :=
    (simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    ((-(12 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (4 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (80 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (32 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (64 : k[X]) * (C W.b₄) ^ 4
          + (112 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          - (324 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          - (64 : k[X]) * (C W.b₈) ^ 2)) * hb

/-- On an elliptic curve, `Ψ₂Sq` and `Ψ₃` have no common root. -/
lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by
  intro hc3
  have hb := congrArg (fun p : k[X] => p.eval x) (bezout_Ψ₂Sq_Ψ₃ W)
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_neg, eval_ofNat, eval_X,
    hs, hc3, mul_zero, zero_mul, add_zero] at hb
  have hΔ2 : W.Δ ^ 2 = 0 := by linear_combination hb
  exact (W.isUnit_Δ.ne_zero) (pow_eq_zero_iff (by norm_num) |>.mp hΔ2)

lemma Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 :=
  fun hs => Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero W hs hc3

/-- Evaluated adjacent-Somos relation. -/
private lemma eval_preΨ_adjacent_somos
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0) (r : ℤ) :
    pe W x (r - 2) * pe W x (r + 2)
      - (if Even r then 1 else (sx W x) ^ 2) * (pe W x (r - 1) * pe W x (r + 1))
      + c3x W x * (pe W x r) ^ 2 = 0 := by
  have h := preΨ_adjacent_somos W h4 r
  have := congrArg (fun p : k[X] => p.eval x) h
  simp only [pe, sx, c3x, eval_mul, eval_sub, eval_add, eval_pow,
    apply_ite (fun p : k[X] => p.eval x), eval_one] at this ⊢
  linear_combination this

/-- Propagation downward: adjacent zeros `(r, r+1)` force `r-1` to vanish (needs `Ψ₃.eval x ≠ 0`). -/
private lemma preΨ_prev_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r - 1) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r - 1)
  have hsquare : c3x W x * (pe W x (r - 1)) ^ 2 = 0 := by
    have e1 : (r - 1) - 2 = r - 3 := by ring
    have e2 : (r - 1) + 2 = r + 1 := by ring
    have e3 : (r - 1) - 1 = r - 2 := by ring
    have e4 : (r - 1) + 1 = r := by ring
    rw [e1, e2, e3, e4, hr1, hr] at h
    linear_combination h
  have hsq : (pe W x (r - 1)) ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-- Propagation upward: adjacent zeros `(r, r+1)` force `r+2` to vanish (needs `Ψ₃.eval x ≠ 0`). -/
private lemma preΨ_next_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r + 2) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r + 2)
  have hsquare : c3x W x * (pe W x (r + 2)) ^ 2 = 0 := by
    have e1 : (r + 2) - 2 = r := by ring
    have e3 : (r + 2) - 1 = r + 1 := by ring
    have e4 : (r + 2) + 1 = r + 3 := by ring
    rw [e1, e3, e4, hr, hr1] at h
    linear_combination h
  have hsq : (pe W x (r + 2)) ^ 2 = 0 := (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq



/-- On the `Ψ₃.eval x ≠ 0` stratum, no two adjacent `preΨ` vanish at `x`: the adjacent-zero
pair would propagate (both directions) to index `1`, contradicting `preΨ 1 = 1`. -/
private lemma no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    (hc3x : c3x W x ≠ 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  rintro ⟨hr, hr1⟩
  have hup : ∀ n, r ≤ n → (pe W x n = 0 ∧ pe W x (n + 1) = 0) := by
    intro n hn
    induction n, hn using Int.le_induction with
    | base => exact ⟨hr, hr1⟩
    | succ m _ ih =>
        refine ⟨ih.2, ?_⟩
        rw [show m + 1 + 1 = m + 2 by ring]
        exact preΨ_next_zero_of_adjacent_zero W x h4 hc3x ih.1 ih.2
  have hdown : ∀ n, n ≤ r → (pe W x n = 0 ∧ pe W x (n + 1) = 0) := by
    intro n hn
    induction n, hn using Int.leInductionDown with
    | base => exact ⟨hr, hr1⟩
    | pred m _ ih =>
        refine ⟨preΨ_prev_zero_of_adjacent_zero W x h4 hc3x ih.1 ih.2, ?_⟩
        rw [show m - 1 + 1 = m by ring]; exact ih.1
  have h1 : pe W x 1 = 0 := by
    rcases le_total r 1 with h | h
    · exact (hup 1 h).1
    · exact (hdown 1 h).1
  rw [pe, preΨ_one, eval_one] at h1
  exact one_ne_zero h1

end

end WeierstrassCurve
