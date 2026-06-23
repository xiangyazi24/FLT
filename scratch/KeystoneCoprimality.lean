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

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

private abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k := (W.preΨ i).eval x
private abbrev sx (W : WeierstrassCurve k) (x : k) : k := W.Ψ₂Sq.eval x
private abbrev c3x (W : WeierstrassCurve k) (x : k) : k := W.Ψ₃.eval x

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

end

end WeierstrassCurve
