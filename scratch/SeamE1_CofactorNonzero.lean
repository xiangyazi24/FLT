module

public import scratch.SeamE1_SeparabilityCore

/-! # Cofactor nonvanishing at roots of the half-index

At a root of `preΨ'(k)` with `Ψ₃(x) ≠ 0` and `(2:K) ≠ 0`, the even cofactor
is nonzero. Uses the Somos relation and parity of c_k = c_{k-2}.
-/

set_option maxHeartbeats 3200000

@[expose] public section

open Polynomial

namespace WeierstrassCurve.SeparabilityCofactor

variable {K : Type*} [Field K]

/-- Evaluated adjacent Somos relation. -/
private lemma eval_adj_somos (W : WeierstrassCurve K) (x : K) (h4 : (4 : K) ≠ 0) (r : ℤ) :
    pe W x (r - 2) * pe W x (r + 2)
      - (if Even r then 1 else (sx W x) ^ 2) * (pe W x (r - 1) * pe W x (r + 1))
      + c3x W x * (pe W x r) ^ 2 = 0 := by
  have h := FLT.EDS.preΨ_adjacent_somos W h4 r
  have h2 := congrArg (fun p : K[X] => p.eval x) h
  simp only [pe, sx, c3x, eval_mul, eval_sub, eval_pow,
    apply_ite (fun p : K[X] => p.eval x), eval_one] at h2 ⊢
  linear_combination h2

/-- At a root of `preΨ'(k)` where `Ψ₃(x) ≠ 0` and `(2:K) ≠ 0`,
the even cofactor `pe(k-1)² · pe(k+2) - pe(k-2) · pe(k+1)²` is nonzero.

Proof idea: assuming cofactor = 0, from three Somos relations (at m = k, k-1, k-2)
specialized to `pe(k) = 0`, derive `2 · c3x · pe(k-2)² = 0`, contradiction. -/
public theorem evenCofactor_ne_zero_of_Ψ₃_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] (x : K) (h4 : (4 : K) ≠ 0)
    (h2 : (2 : K) ≠ 0)
    {m : ℕ}
    (hroot : pe W x (↑(m + 3) : ℤ) = 0)
    (hΨ₃ : c3x W x ≠ 0)
    (hkm1 : pe W x (↑(m + 3) - 1 : ℤ) ≠ 0)
    (hkm2 : pe W x (↑(m + 3) - 2 : ℤ) ≠ 0) :
    pe W x (↑(m + 2) : ℤ) ^ 2 * pe W x (↑(m + 5) : ℤ) -
      pe W x (↑(m + 1) : ℤ) * pe W x (↑(m + 4) : ℤ) ^ 2 ≠ 0 := by
  -- Set k = m + 3 for readability
  set k : ℤ := ↑(m + 3)
  -- Abbreviations for readability
  set a := pe W x (k - 1) -- pe(k-1), nonzero
  set b := pe W x (k - 2) -- pe(k-2), nonzero
  set p := pe W x (k + 1) -- pe(k+1)
  set q := pe W x (k + 2) -- pe(k+2)
  set r := pe W x (k - 3) -- pe(k-3)
  set C := c3x W x -- Ψ₃(x), nonzero
  set c := if Even k then (1 : K) else (sx W x) ^ 2 -- parity coeff
  -- Index equalities
  have ek1 : (↑(m + 2) : ℤ) = k - 1 := by simp [k]; ring
  have ek2 : (↑(m + 1) : ℤ) = k - 2 := by simp [k]; ring
  have ek4 : (↑(m + 4) : ℤ) = k + 1 := by simp [k]; ring
  have ek5 : (↑(m + 5) : ℤ) = k + 2 := by simp [k]; ring
  rw [ek1, ek2, ek4, ek5]
  -- Assume cofactor = 0 and derive contradiction
  intro hcof
  -- The cofactor equation: a² * q = b * p²
  have hcof_eq : a ^ 2 * q = b * p ^ 2 := by
    change pe W x (k - 1) ^ 2 * pe W x (k + 2) -
      pe W x (k - 2) * pe W x (k + 1) ^ 2 = 0 at hcof
    linarith
  -- Somos at m = k (with pe(k) = 0): q * b = c * p * a
  have hS0 := eval_adj_somos W x h4 k
  have hS_k : q * b = c * (p * a) := by
    have hzero : C * pe W x k ^ 2 = 0 := by rw [hroot]; ring
    change pe W x (k - 2) * pe W x (k + 2) -
      (if Even k then 1 else sx W x ^ 2) * (pe W x (k - 1) * pe W x (k + 1)) +
      c3x W x * pe W x k ^ 2 = 0 at hS0
    nlinarith
  -- Somos at m = k-1 (with pe(k) = 0): p * r = -C * a²
  have hS_km1' := eval_adj_somos W x h4 (k - 1)
  have hS_km1 : p * r = -C * a ^ 2 := by
    have e1 : k - 1 - 2 = k - 3 := by ring
    have e2 : k - 1 + 2 = k + 1 := by ring
    have e3 : k - 1 - 1 = k - 2 := by ring
    have e4 : k - 1 + 1 = k := by ring
    rw [e1, e2, e3, e4] at hS_km1'
    -- hS_km1': r * p - (if Even (k-1) ...) * (b * pe(k)) + C * a² = 0
    -- pe(k) = 0, so middle term vanishes
    have hzero : (if Even (k - 1) then 1 else sx W x ^ 2) * (pe W x (k - 2) * pe W x k) = 0 := by
      rw [hroot]; ring
    nlinarith
  -- Somos at m = k-2 (with pe(k) = 0): c' * a * r = C * b²
  -- where c' = if Even (k-2) then 1 else sx²  = c (same parity as k)
  have hS_km2' := eval_adj_somos W x h4 (k - 2)
  have hS_km2 : c * (a * r) = C * b ^ 2 := by
    have e1 : k - 2 - 2 = k - 4 := by ring
    have e2 : k - 2 + 2 = k := by ring
    have e3 : k - 2 - 1 = k - 3 := by ring
    have e4 : k - 2 + 1 = k - 1 := by ring
    rw [e1, e2, e3, e4] at hS_km2'
    -- hS_km2': pe(k-4) * pe(k) - c' * (r * a) + C * b² = 0
    -- pe(k) = 0
    have hzero : pe W x (k - 4) * pe W x k = 0 := by rw [hroot]; ring
    -- Parity: Even (k-2) ↔ Even k, so c' = c
    have hparity : (if Even (k - 2) then (1 : K) else sx W x ^ 2) = c := by
      simp only [c]
      congr 1
      constructor
      · intro ⟨j, hj⟩; exact ⟨j + 1, by omega⟩
      · intro ⟨j, hj⟩; exact ⟨j - 1, by omega⟩
    rw [hparity] at hS_km2'
    nlinarith
  -- Now we have:
  -- hS_k:     q * b = c * (p * a)
  -- hcof_eq:  a² * q = b * p²
  -- hS_km1:   p * r = -C * a²
  -- hS_km2:   c * (a * r) = C * b²
  --
  -- From hcof_eq and hS_k, eliminate q:
  -- hS_k * a: q * b * a = c * p * a²
  -- hcof_eq * b: a² * q * b = b² * p²  ... wait, let me multiply differently
  -- Multiply hcof_eq by b: a² * q * b = b² * p²
  -- Multiply hS_k by a²: q * b * a² = c * p * a³
  -- So b² * p² = c * p * a³, giving b² * p = c * a³ (dividing by p ≠ 0)
  have hpe_k1_ne : p ≠ 0 := by
    intro h0
    apply no_adjacent_preΨ_zero W x h4 k ⟨hroot, h0⟩
  -- From the two expressions for q*b*a²:
  have hstep : b ^ 2 * p = c * a ^ 3 := by
    have h1 : a ^ 2 * q * b = b ^ 2 * p ^ 2 := by nlinarith [hcof_eq]
    have h2 : q * b * a ^ 2 = c * (p * a) * a ^ 2 := by nlinarith [hS_k]
    -- h1 and h2 have same LHS (up to commutativity)
    have h3 : b ^ 2 * p ^ 2 = c * p * a ^ 3 := by nlinarith
    -- Factor out p
    have h4' : p * (b ^ 2 * p - c * a ^ 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp h4' with hp | hd
    · exact absurd hp hpe_k1_ne
    · linarith
  -- From hS_km1 and hstep, derive c * (a * r) = -C * b²
  -- hS_km1: p * r = -C * a²
  -- hstep: b² * p = c * a³, so p = c * a³ / b²
  -- Multiply hS_km1 by b²: p * r * b² = -C * a² * b²
  -- Multiply hstep by r: b² * p * r = c * a³ * r
  -- So: -C * a² * b² = c * a³ * r
  -- -C * b² = c * a * r  (dividing by a² ≠ 0)
  have hstar : c * (a * r) = -(C * b ^ 2) := by
    have h1 : p * r * b ^ 2 = -(C * a ^ 2) * b ^ 2 := by nlinarith [hS_km1]
    have h2 : b ^ 2 * p * r = c * a ^ 3 * r := by nlinarith [hstep]
    -- h1 and h2 have same LHS: p * r * b² = b² * p * r
    have h3 : c * a ^ 3 * r = -(C * a ^ 2 * b ^ 2) := by nlinarith
    -- Factor out a²
    have hkm1_sq : a ^ 2 ≠ 0 := pow_ne_zero 2 hkm1
    have h4' : a ^ 2 * (c * a * r + C * b ^ 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp h4' with ha | hd
    · exact absurd ha hkm1_sq
    · linarith
  -- Now: hS_km2 says c*(a*r) = C*b² and hstar says c*(a*r) = -C*b²
  -- So: C*b² = -C*b², i.e., 2*C*b² = 0
  have h_2Cb2 : 2 * (C * b ^ 2) = 0 := by linarith
  -- Contradiction: 2 ≠ 0, C ≠ 0, b² ≠ 0
  have hCb2_ne : C * b ^ 2 ≠ 0 := mul_ne_zero hΨ₃ (pow_ne_zero 2 hkm2)
  exact hCb2_ne (or_iff_not_imp_left.mp (mul_eq_zero.mp h_2Cb2) h2)

end WeierstrassCurve.SeparabilityCofactor
