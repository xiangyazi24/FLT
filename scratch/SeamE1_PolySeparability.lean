module

public import scratch.KeystoneCoprimality
public import scratch.KeystoneSeparability
public import scratch.Bridge1Even
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Cofactor nonvanishing for even EDS descent -/

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

@[expose] public section

open Polynomial WeierstrassCurve FLT.EDS

namespace WeierstrassCurve.PolySep

variable {K : Type*} [Field K]

/-- Evaluated Somos (replicate from KeystoneCoprimality since it's private there). -/
private lemma eval_somos
    (W : WeierstrassCurve K) (x : K) (h4 : (4 : K) ≠ 0) (r : ℤ) :
    pe W x (r - 2) * pe W x (r + 2)
      - (if Even r then 1 else (sx W x) ^ 2) * (pe W x (r - 1) * pe W x (r + 1))
      + c3x W x * (pe W x r) ^ 2 = 0 := by
  have h := preΨ_adjacent_somos W h4 r
  have := congrArg (fun p : K[X] => p.eval x) h
  simp only [pe, sx, c3x, eval_mul, eval_sub, eval_add, eval_pow,
    apply_ite (fun p : K[X] => p.eval x), eval_one] at this ⊢
  linear_combination this

/-- At a root of preΨ(r), the Somos simplifies. -/
private lemma somos_at_root
    (W : WeierstrassCurve K) [W.IsElliptic] (x : K) (h4 : (4 : K) ≠ 0) (r : ℤ)
    (hroot : pe W x r = 0) :
    pe W x (r - 2) * pe W x (r + 2) =
      (if Even r then 1 else (sx W x) ^ 2) * (pe W x (r - 1) * pe W x (r + 1)) := by
  have h := eval_somos W x h4 r
  rw [hroot, zero_pow (two_ne_zero), mul_zero, add_zero] at h; linear_combination h

/-- Cofactor nonvanishing (Ψ₃ ≠ 0 stratum).

At a root of preΨ(k) where Ψ₃(x) ≠ 0, using three Somos relations we prove:
  α² · γ = -P · β³
which gives: cofactor · α = 2Pβ³γ ≠ 0. -/
public theorem evenCofactor_ne_zero_Psi3_ne
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h4 : (4 : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    {k : ℤ} (hk : 4 ≤ k) {x : K}
    (hroot : pe W x k = 0)
    (hΨ₂Sq : sx W x ≠ 0)
    (hΨ₃ : c3x W x ≠ 0) :
    pe W x (k - 1) ^ 2 * pe W x (k + 2) -
     pe W x (k - 2) * pe W x (k + 1) ^ 2 ≠ 0 := by
  set α := pe W x (k - 2)
  set β := pe W x (k - 1)
  set γ := pe W x (k + 1)
  set δ := pe W x (k + 2)
  set P := if Even k then (1 : K) else (sx W x) ^ 2
  set Ψ₃x := c3x W x
  -- Adjacent coprimality
  have hβ : β ≠ 0 := by
    intro h; apply no_adjacent_preΨ_zero W x h4 (k - 1)
    exact ⟨h, by rw [show k - 1 + 1 = k by ring]; exact hroot⟩
  have hγ : γ ≠ 0 := by
    intro h; apply no_adjacent_preΨ_zero W x h4 k
    exact ⟨hroot, h⟩
  have hP : P ≠ 0 := by
    simp only [P]; split_ifs with hp <;> simp_all [one_ne_zero, pow_ne_zero 2 hΨ₂Sq]
  -- Somos at r = k: δ·α = P·γ·β
  have hSk : δ * α = P * (γ * β) := by
    have h := somos_at_root W x h4 k hroot; linear_combination h
  have hα : α ≠ 0 := by
    intro h; rw [h, mul_zero] at hSk; exact absurd hSk.symm (mul_ne_zero hP (mul_ne_zero hγ hβ))
  -- Somos at r = k-1: γ·pe(k-3) + Ψ₃x·β² = P'·0·α = 0
  -- ⟹ γ·pe(k-3) = -Ψ₃x·β²
  have hSkm1 : γ * pe W x (k - 3) = -Ψ₃x * β ^ 2 := by
    have h := eval_somos W x h4 (k - 1)
    rw [show k - 1 - 2 = k - 3 by ring, show k - 1 + 2 = k + 1 by ring,
        show k - 1 - 1 = k - 2 by ring, show k - 1 + 1 = k by ring] at h
    rw [hroot] at h
    -- h has pe(k) = 0, clean up
    simp only [mul_zero, sub_zero] at h
    -- h : pe(k-3) * γ + Ψ₃x * β² = 0
    -- goal: γ * pe(k-3) = -Ψ₃x * β²
    linear_combination h
  -- Somos at r = k-2: pe(k)·pe(k-4) - P''·pe(k-1)·pe(k-3) + Ψ₃x·α² = 0
  -- with pe(k) = 0: Ψ₃x·α² = P''·β·pe(k-3)
  -- P'' = parity(k-2) = parity(k) = P (since Even(k-2) ↔ Even(k))
  have hSkm2 : Ψ₃x * α ^ 2 = P * (β * pe W x (k - 3)) := by
    have h := eval_somos W x h4 (k - 2)
    rw [show k - 2 - 2 = k - 4 by ring, show k - 2 + 2 = k by ring,
        show k - 2 - 1 = k - 3 by ring, show k - 2 + 1 = k - 1 by ring] at h
    simp only [hroot, mul_zero, zero_mul, zero_sub] at h
    -- h : -P''·(pe(k-3)·pe(k-1)) + Ψ₃x·α² = 0
    -- Even(k-2) ↔ Even(k), so P'' = P
    have hep : Even (k - 2) ↔ Even k := by
      rw [show k - 2 = k + (-2) by ring, Int.even_add]; simp
    simp only [hep, P] at h
    linear_combination h
  -- pe(k-3) ≠ 0
  have hk3_ne : pe W x (k - 3) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hSkm1
    exact (mul_ne_zero hΨ₃ (pow_ne_zero 2 hβ)) (by linear_combination hSkm1)
  -- KEY: α²·γ = -(P·β³)
  have hkey : α ^ 2 * γ = -(P * β ^ 3) :=
    mul_left_cancel₀ hΨ₃ (calc
      Ψ₃x * (α ^ 2 * γ)
          = (Ψ₃x * α ^ 2) * γ := by ring
        _ = P * (β * pe W x (k - 3)) * γ := by rw [hSkm2]
        _ = P * β * (γ * pe W x (k - 3)) := by ring
        _ = P * β * (-Ψ₃x * β ^ 2) := by rw [hSkm1]
        _ = Ψ₃x * (-(P * β ^ 3)) := by ring)
  -- CONCLUDE: α·(β²δ - αγ²) = 2Pβ³γ ≠ 0
  suffices h : α * (β ^ 2 * δ - α * γ ^ 2) ≠ 0 from right_ne_zero_of_mul h
  have hcalc : α * (β ^ 2 * δ - α * γ ^ 2) = 2 * P * β ^ 3 * γ := calc
    α * (β ^ 2 * δ - α * γ ^ 2)
        = β ^ 2 * (α * δ) - (α ^ 2 * γ) * γ := by ring
      _ = β ^ 2 * (P * γ * β) - (-(P * β ^ 3)) * γ := by
          rw [show α * δ = P * γ * β from by linear_combination hSk, hkey]
      _ = 2 * P * β ^ 3 * γ := by ring
  rw [hcalc]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hP) (pow_ne_zero 3 hβ)) hγ

end WeierstrassCurve.PolySep
