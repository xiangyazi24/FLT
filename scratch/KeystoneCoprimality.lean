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

set_option maxHeartbeats 1000000000
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

/-- Resultant/Bezout certificate `A·Ψ₃ + B·preΨ₄ = C(Δ⁴)` (CAS-extracted, uses `b_relation`). -/
private lemma bezout_Ψ₃_preΨ₄ (W : WeierstrassCurve k) :
    ((2 : k[X]) * X ^ 5 * (C W.b₂) ^ 7 * (C W.b₈) ^ 2
          - (4 : k[X]) * X ^ 5 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + (2 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          - (200 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 2
          - (72 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (596 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + (36 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3
          + (1440 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (144 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈)
          - (324 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (5792 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (648 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (1134 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₆) ^ 4
          - (1152 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₈) ^ 3
          + (108 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆)
          - (18144 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (1674 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (74304 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (17496 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (5832 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈)
          + (10692 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (36288 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (227232 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (40824 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4
          + (56448 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 3
          + (295488 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (4374 : k[X]) * X ^ 5 * (C W.b₄) ^ 6 * (C W.b₆)
          - (25272 : k[X]) * X ^ 5 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (34992 : k[X]) * X ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (284256 : k[X]) * X ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (886464 : k[X]) * X ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (314928 : k[X]) * X ^ 5 * (C W.b₆) ^ 5
          - (508032 : k[X]) * X ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          + X ^ 4 * (C W.b₂) ^ 8 * (C W.b₈) ^ 2
          - (2 : k[X]) * X ^ 4 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + X ^ 4 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          - (102 : k[X]) * X ^ 4 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 2
          - (34 : k[X]) * X ^ 4 * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈)
          + (300 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + (16 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3
          + (734 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 2
          - (72 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈)
          - (162 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (3062 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (468 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (519 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₆) ^ 4
          - (808 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₈) ^ 3
          + (54 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆)
          - (9384 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (513 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (37632 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (8502 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (3024 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈)
          + (5238 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (22656 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (117450 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (18792 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4
          + (41216 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 3
          + (149832 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (2187 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆)
          - (2430 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (28188 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (133920 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (444528 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (144342 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₆) ^ 5
          - (327264 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 3
          - (4374 : k[X]) * X ^ 4 * (C W.b₄) ^ 6 * (C W.b₈)
          + (4374 : k[X]) * X ^ 4 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          + (40824 : k[X]) * X ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (89424 : k[X]) * X ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (56862 : k[X]) * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (127008 : k[X]) * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (235872 : k[X]) * X ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (52488 : k[X]) * X ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          + (131712 : k[X]) * X ^ 4 * (C W.b₈) ^ 4
          + (4 : k[X]) * X ^ 3 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₈) ^ 2
          + X ^ 3 * (C W.b₂) ^ 7 * (C W.b₆) ^ 2 * (C W.b₈)
          - (9 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 3
          + (7 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₆) * (C W.b₈) ^ 2
          + (5 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (415 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (256 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (22 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₆) ^ 4
          - (92 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₈) ^ 3
          + (1334 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (252 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (3176 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (223 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₆) ^ 3 * (C W.b₈)
          - (306 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₈)
          - (864 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (12176 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (729 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (3357 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 4
          + (2400 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈) ^ 3
          + (1092 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (270 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆)
          - (40401 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (9423 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (180648 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (50220 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (6075 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) ^ 5
          - (30224 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          + (12393 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₈)
          + (28917 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (71604 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (511272 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (64395 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (85680 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (808272 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (972 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆) ^ 4 * (C W.b₈)
          + (53312 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₈) ^ 4
          - (10935 : k[X]) * X ^ 3 * (C W.b₄) ^ 7 * (C W.b₆)
          - (57348 : k[X]) * X ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (91854 : k[X]) * X ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (674352 : k[X]) * X ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          - (2118960 : k[X]) * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (734832 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          - (1213632 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (38880 : k[X]) * X ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (10 : k[X]) * X ^ 2 * (C W.b₂) ^ 7 * (C W.b₆) * (C W.b₈) ^ 2
          - (4 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (17 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + X ^ 2 * (C W.b₂) ^ 6 * (C W.b₆) ^ 4
          + (10 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₈) ^ 3
          + (5 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (5 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (1047 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (316 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₆) ^ 3 * (C W.b₈)
          + (385 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (2840 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (84 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 4
          - (1084 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₈) ^ 3
          + (7260 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (1572 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (756 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (31940 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (5541 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (6075 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) ^ 5
          - (2992 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          + (270 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          + (270 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (11694 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (87183 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (189 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (35568 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (390492 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (75816 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (5600 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈) ^ 4
          + (57591 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (24543 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (220104 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (1193076 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (270459 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 5
          + (127344 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          + (1469664 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (10935 : k[X]) * X ^ 2 * (C W.b₄) ^ 7 * (C W.b₈)
          - (10935 : k[X]) * X ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          + (102060 : k[X]) * X ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          - (356238 : k[X]) * X ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (28431 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (317520 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          + (2036448 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (4639356 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (329280 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (1614006 : k[X]) * X ^ 2 * (C W.b₆) ^ 6
          - (2558304 : k[X]) * X ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          + (9 : k[X]) * X * (C W.b₂) ^ 7 * (C W.b₈) ^ 3
          - (25 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (7 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₆) ^ 3 * (C W.b₈)
          + (2 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (12 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (5 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 4
          - (880 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 3
          - (274 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (3098 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (258 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (165 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) ^ 5
          + (5720 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 3
          - (705 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (2112 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (846 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (25048 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (4872 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (6114 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆) ^ 4 * (C W.b₈)
          - (5264 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₈) ^ 4
          + (720 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (270 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (88896 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (702 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (5994 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 5
          - (285184 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (71352 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (25272 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (71523 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (28188 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (157248 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          + (959256 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (170424 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (244608 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 4
          - (45927 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 6
          + (1082928 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (29160 : k[X]) * X * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          + (10935 : k[X]) * X * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          - (9072 : k[X]) * X * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (375192 : k[X]) * X * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (148716 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (903168 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (3251664 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (1259712 : k[X]) * X * (C W.b₆) ^ 5 * (C W.b₈)
          - (1843968 : k[X]) * X * (C W.b₆) * (C W.b₈) ^ 4
          + (C W.b₂) ^ 8 * (C W.b₈) ^ 3
          - (3 : k[X]) * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (3 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (111 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 3
          - (27 : k[X]) * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (424 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (25 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (7 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) ^ 5
          + (864 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          - (78 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (456 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (18 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (3760 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (2290 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (693 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          - (1632 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈) ^ 4
          + (126 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (14034 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (2511 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (1422 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          - (43432 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (7432 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (54 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          + (3663 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (13410 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          + (1107 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (39944 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          + (200916 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (26406 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (88816 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (1944 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 6
          + (179888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (5103 : k[X]) * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          - (5346 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          + (48600 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (211410 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (45684 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (103824 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (756648 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (188568 : k[X]) * (C W.b₂) * (C W.b₆) ^ 5 * (C W.b₈)
          - (639744 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 4
          + (2187 : k[X]) * (C W.b₄) ^ 7 * (C W.b₆) ^ 2
          - (20412 : k[X]) * (C W.b₄) ^ 6 * (C W.b₈) ^ 2
          + (46899 : k[X]) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (6561 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 4
          + (190512 : k[X]) * (C W.b₄) ^ 4 * (C W.b₈) ^ 3
          - (666360 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (983664 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (592704 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈) ^ 4
          - (308367 : k[X]) * (C W.b₄) * (C W.b₆) ^ 6
          + (1553328 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (400464 : k[X]) * (C W.b₆) ^ 4 * (C W.b₈) ^ 2
          + (614656 : k[X]) * (C W.b₈) ^ 5) * W.Ψ₃
      + (-(3 : k[X]) * X ^ 3 * (C W.b₂) ^ 7 * (C W.b₈) ^ 2
          + (6 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (3 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          + (300 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 2
          + (108 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          - (894 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - (54 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3
          - (2160 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          + (216 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈)
          + (486 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (8688 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (972 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (1701 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆) ^ 4
          + (1728 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₈) ^ 3
          - (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆)
          + (27216 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (2511 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (111456 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (26244 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (8748 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈)
          - (16038 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (54432 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (340848 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (61236 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4
          - (84672 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 3
          - (443232 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (6561 : k[X]) * X ^ 3 * (C W.b₄) ^ 6 * (C W.b₆)
          + (37908 : k[X]) * X ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (52488 : k[X]) * X ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (426384 : k[X]) * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (1329696 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (472392 : k[X]) * X ^ 3 * (C W.b₆) ^ 5
          + (762048 : k[X]) * X ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          - X ^ 2 * (C W.b₂) ^ 8 * (C W.b₈) ^ 2
          + (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          + (103 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 2
          + (33 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈)
          - (301 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - (15 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3
          - (741 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 2
          + (72 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈)
          + (162 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (3145 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (540 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (495 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆) ^ 4
          + (924 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₈) ^ 3
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆)
          + (9540 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (351 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (37872 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (8379 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          - (3078 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈)
          - (5184 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (24912 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (119367 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (17982 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4
          - (47712 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 3
          - (150876 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆)
          - (2673 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (33534 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (129816 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (445176 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (137781 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 5
          + (363888 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 3
          + (6561 : k[X]) * X ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          - (6561 : k[X]) * X ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (61236 : k[X]) * X ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (134136 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (85293 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (190512 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (353808 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (78732 : k[X]) * X ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (197568 : k[X]) * X ^ 2 * (C W.b₈) ^ 4
          - (2 : k[X]) * X * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₈) ^ 2
          - X * (C W.b₂) ^ 7 * (C W.b₆) ^ 2 * (C W.b₈)
          + (5 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + X * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 3
          - (7 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₆) * (C W.b₈) ^ 2
          - (3 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (214 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (186 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (21 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₆) ^ 4
          + (80 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₈) ^ 3
          - (738 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (216 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (1644 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (273 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) ^ 3 * (C W.b₈)
          + (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₈)
          + (540 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (6360 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (1593 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (2079 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 4
          - (2944 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈) ^ 3
          - (1116 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆)
          + (22329 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (7695 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (101736 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (35640 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (5832 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 5
          + (27024 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (6561 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₈)
          - (18225 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          + (35964 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (277992 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (18954 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (33264 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (488592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (11664 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 4 * (C W.b₈)
          - (47040 : k[X]) * X * (C W.b₂) * (C W.b₈) ^ 4
          + (6561 : k[X]) * X * (C W.b₄) ^ 7 * (C W.b₆)
          + (29160 : k[X]) * X * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (59049 : k[X]) * X * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (371952 : k[X]) * X * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (1183896 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (393660 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 5
          + (677376 : k[X]) * X * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          + (58320 : k[X]) * X * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (3 : k[X]) * (C W.b₂) ^ 7 * (C W.b₆) * (C W.b₈) ^ 2
          + (2 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (5 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (C W.b₂) ^ 6 * (C W.b₆) ^ 4
          - (9 : k[X]) * (C W.b₂) ^ 6 * (C W.b₈) ^ 3
          - (3 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (356 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (67 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) ^ 3 * (C W.b₈)
          - (216 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (900 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 4
          + (800 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₈) ^ 3
          - (2238 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (756 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (54 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (11934 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (3519 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (2187 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 5
          - (824 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          - (162 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          + (7065 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (27513 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (4374 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (22104 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (132516 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (15066 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          + (5264 : k[X]) * (C W.b₂) ^ 2 * (C W.b₈) ^ 4
          - (26973 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (2187 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (84888 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          - (404838 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (118098 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 5
          - (3024 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (441288 : k[X]) * (C W.b₂) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (6561 : k[X]) * (C W.b₄) ^ 7 * (C W.b₈)
          - (61236 : k[X]) * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (181521 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (39366 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          + (190512 : k[X]) * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          - (818424 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (1522152 : k[X]) * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          - (197568 : k[X]) * (C W.b₄) * (C W.b₈) ^ 4
          - (531441 : k[X]) * (C W.b₆) ^ 6
          + (789264 : k[X]) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3) * W.preΨ₄
      = C (W.Δ ^ 4) := by
  have hb := bRelC W
  linear_combination (norm :=
    (simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    (((30 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 3
          + (3 : k[X]) * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (477 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (6 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (C W.b₂) ^ 5 * (C W.b₆) ^ 5
          - (114 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          + (384 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (2912 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (1242 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (2628 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (56 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          + (408 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈) ^ 4
          - (4864 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (6560 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (10544 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          - (25252 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (162 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          + (5184 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (1667 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (2048 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 7 * (C W.b₈)
          + (16768 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          - (8030 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          - (5484 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          + (78624 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          + (21392 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          - (84711 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (70956 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          - (23520 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (2187 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 6
          - (13276 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (14336 : k[X]) * (C W.b₂) * (C W.b₄) ^ 8 * (C W.b₆)
          + (40960 : k[X]) * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          - (131328 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          - (72789 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          + (284688 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          - (347733 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (3416 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          + (139968 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (83106 : k[X]) * (C W.b₂) * (C W.b₆) ^ 5 * (C W.b₈)
          + (121520 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 4
          + (4096 : k[X]) * (C W.b₄) ^ 10
          - (16384 : k[X]) * (C W.b₄) ^ 8 * (C W.b₈)
          + (55296 : k[X]) * (C W.b₄) ^ 7 * (C W.b₆) ^ 2
          + (58975 : k[X]) * (C W.b₄) ^ 6 * (C W.b₈) ^ 2
          - (216810 : k[X]) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (279936 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 4
          - (154252 : k[X]) * (C W.b₄) ^ 4 * (C W.b₈) ^ 3
          + (577584 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (905418 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          + (235984 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈) ^ 4
          + (590490 : k[X]) * (C W.b₄) * (C W.b₆) ^ 6
          - (635040 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          + (297432 : k[X]) * (C W.b₆) ^ 4 * (C W.b₈) ^ 2
          - (153664 : k[X]) * (C W.b₈) ^ 5)) * hb

/-- On an elliptic curve, `Ψ₃` and `preΨ₄` have no common root. -/
lemma preΨ₄_eval_ne_of_Ψ₃_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : (W.preΨ 4).eval x ≠ 0 := by
  rw [show W.preΨ 4 = W.preΨ₄ from by simpa using W.preΨ'_four ▸ rfl]
  intro hd4
  have hb := congrArg (fun p : k[X] => p.eval x) (bezout_Ψ₃_preΨ₄ W)
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_neg, eval_ofNat, eval_X,
    hc3, hd4, mul_zero, zero_mul, add_zero] at hb
  have hΔ4 : W.Δ ^ 4 = 0 := by linear_combination -hb
  exact (W.isUnit_Δ.ne_zero) (pow_eq_zero_iff (by norm_num) |>.mp hΔ4)

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
