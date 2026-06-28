# Q1619 (dm1): even-`B` descent after the `M*N = 5*B₁^4` split

The clean even-`B` chain is to introduce the half-factors and then reuse the odd-case fourth-power split on those half-factors.

The important Lean point is: once you define

```lean
H = a ^ 2 - b ^ 2
u = (r - H) / 2
v = (r + H) / 2
```

prove and keep these four facts named:

```lean
h2u      : 2 * u = r - H
h2v      : 2 * v = r + H
huv_prod : u * v = b ^ 4
huv_sum  : u + v = r
```

Then `coprime_rh` should be applied to `u,v`, not to the raw factors `r-H,r+H`.

Below is the pasteable body. I am writing it with the following local facts already available from the preceding `M,N` split and parity branch:

```lean
hsq_even  : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
hr_pos    : 0 < r
hb_pos    : 0 < b
hr_odd    : Odd r
hH_odd0   : Odd (a ^ 2 - b ^ 2)
hcop_rb   : Int.gcd r b = 1
ha_pos    : 0 < a
hB_eq     : B = 2 * B₁
hB₁_pos   : 0 < B₁
hB₁_eq_ab : B₁ = a * b
```

If your local names differ, only rename these hypotheses. The actual even-branch wiring is the block below.

```lean
import Mathlib

-- Inside the even-`B` branch, after the `M,N` split has produced
--   hsq_even : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
-- and after you have the primitive/coprime fact
--   hcop_rb : Int.gcd r b = 1

let H : ℤ := a ^ 2 - b ^ 2

have hsq_H : r ^ 2 = H ^ 2 + 4 * b ^ 4 := by
  simpa [H] using hsq_even

have hH_odd : Odd H := by
  simpa [H] using hH_odd0

-- Since r and H are odd, both r-H and r+H are divisible by 2.
have h2u_dvd : (2 : ℤ) ∣ r - H := by
  rcases hr_odd with ⟨r0, hr0⟩
  rcases hH_odd with ⟨h0, hh0⟩
  refine ⟨r0 - h0, ?_⟩
  nlinarith

have h2v_dvd : (2 : ℤ) ∣ r + H := by
  rcases hr_odd with ⟨r0, hr0⟩
  rcases hH_odd with ⟨h0, hh0⟩
  refine ⟨r0 + h0 + 1, ?_⟩
  nlinarith

let u : ℤ := (r - H) / 2
let v : ℤ := (r + H) / 2

have h2u : 2 * u = r - H := by
  dsimp [u]
  exact Int.mul_ediv_cancel' h2u_dvd

have h2v : 2 * v = r + H := by
  dsimp [v]
  exact Int.mul_ediv_cancel' h2v_dvd

have hprod_rH : (r - H) * (r + H) = 4 * b ^ 4 := by
  nlinarith [hsq_H]

have hprod_pos : 0 < (r - H) * (r + H) := by
  have hb4_pos : 0 < b ^ 4 := pow_pos hb_pos 4
  nlinarith [hprod_rH, hb4_pos]

have hRH_pos : 0 < r - H ∧ 0 < r + H := by
  rcases (mul_pos_iff.mp hprod_pos) with hpos | hneg
  · exact hpos
  · rcases hneg with ⟨hrH_neg, hrpH_neg⟩
    have hsum_neg : (r - H) + (r + H) < 0 := add_neg hrH_neg hrpH_neg
    have hsum_pos : 0 < (r - H) + (r + H) := by
      nlinarith [hr_pos]
    linarith

have hu_pos : 0 < u := by
  nlinarith [h2u, hRH_pos.1]

have hv_pos : 0 < v := by
  nlinarith [h2v, hRH_pos.2]

have huv_sum : u + v = r := by
  have h2 : 2 * (u + v) = 2 * r := by
    nlinarith [h2u, h2v]
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

have huv_diff : v - u = H := by
  have h2 : 2 * (v - u) = 2 * H := by
    nlinarith [h2u, h2v]
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

have huv_prod : u * v = b ^ 4 := by
  have hprod2 : (2 * u) * (2 * v) = 4 * b ^ 4 := by
    calc
      (2 * u) * (2 * v) = (r - H) * (r + H) := by
        rw [h2u, h2v]
      _ = 4 * b ^ 4 := hprod_rH
  have hprod4 : 4 * (u * v) = 4 * b ^ 4 := by
    nlinarith [hprod2]
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hprod4

-- This is the adapted gcd lemma for the half-factors.
-- Its proof is the prime-divisor argument:
--   p ∣ u,v ⇒ p ∣ u+v = r and p ∣ u*v = b^4 ⇒ p ∣ b,
-- contradicting gcd(r,b)=1.
have huv_cop : Int.gcd u v = 1 := by
  exact coprime_rh hu_pos hv_pos hcop_rb huv_sum huv_prod

-- Reuse the odd-case fourth-power split on u*v=b^4.
-- If your helper returns the equations in the opposite orientation, replace
-- `hu_fourth`/`hv_fourth` below by their `.symm` in the two `rw` calls.
obtain ⟨α, β, hα_pos, hβ_pos, hu_fourth, hv_fourth⟩ :=
  pos_fourth_of_coprime_mul_fourth hu_pos hv_pos huv_cop huv_prod

have hb_fourth_eq : b ^ 4 = (α * β) ^ 4 := by
  calc
    b ^ 4 = u * v := by
      simpa using huv_prod.symm
    _ = α ^ 4 * β ^ 4 := by
      rw [hu_fourth, hv_fourth]
    _ = (α * β) ^ 4 := by
      ring

have hb_eq : b = α * β := by
  exact eq_of_pos_fourth_eq hb_pos (mul_pos hα_pos hβ_pos) hb_fourth_eq

-- The new solution is (r', B', s') = (β, α, a):
--   a^2 = β^4 + β^2 α^2 - α^4.
have hnew_eq_alpha_beta :
    a ^ 2 = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
  calc
    a ^ 2 = H + b ^ 2 := by
      dsimp [H]
      ring
    _ = (v - u) + (α * β) ^ 2 := by
      rw [← huv_diff, hb_eq]
    _ = (β ^ 4 - α ^ 4) + (α * β) ^ 2 := by
      rw [hu_fourth, hv_fourth]
    _ = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
      ring

have hnew_eq :
    a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using hnew_eq_alpha_beta

-- If your induction hypothesis requires the new pair to be primitive, derive
-- this from huv_cop and hu_fourth/hv_fourth.  In many files this is already
-- bundled into the fourth-power split helper.  If so, use the returned field.
-- Otherwise the standard local lemma has this shape:
--
--   have hβα_cop : Int.gcd β α = 1 := by
--     exact coprime_fourth_roots_of_coprime huv_cop hu_fourth hv_fourth
--
-- or, if the helper gives hαβ_cop : Int.gcd α β = 1:
--
--   have hβα_cop : Int.gcd β α = 1 := by
--     simpa [Int.gcd_comm] using hαβ_cop

-- Descent bound.  The robust Lean close only needs α ≤ b and B₁ < B.
-- Do not spend effort proving strict α < b unless you already have β > 1;
-- α ≤ b is enough because B = 2*B₁.
have hα_le_b : α ≤ b := by
  have hβ_ge_one : (1 : ℤ) ≤ β := by
    omega
  calc
    α = α * 1 := by ring
    _ ≤ α * β := by
      exact mul_le_mul_of_nonneg_left hβ_ge_one (le_of_lt hα_pos)
    _ = b := hb_eq.symm

have hb_le_B₁ : b ≤ B₁ := by
  have ha_ge_one : (1 : ℤ) ≤ a := by
    omega
  rw [hB₁_eq_ab]
  calc
    b = 1 * b := by ring
    _ ≤ a * b := by
      exact mul_le_mul_of_nonneg_right ha_ge_one (le_of_lt hb_pos)

have hB₁_lt_B : B₁ < B := by
  rw [hB_eq]
  nlinarith [hB₁_pos]

have hBprime_lt_B : α < B := by
  exact lt_of_le_of_lt (le_trans hα_le_b hb_le_B₁) hB₁_lt_B

-- Optional strengthening, only if you already have hβ_gt_one : 1 < β.
have hα_lt_b_of_hβ_gt_one : 1 < β → α < b := by
  intro hβ_gt_one
  calc
    α = α * 1 := by ring
    _ < α * β := by
      exact mul_lt_mul_of_pos_left hβ_gt_one hα_pos
    _ = b := hb_eq.symm

-- At this point the descent package is:
--   B' = α, r' = β, s' = a
--   hα_pos       : 0 < α
--   hβ_pos       : 0 < β
--   hnew_eq      : a^2 = β^4 + β^2*α^2 - α^4
--   hBprime_lt_B : α < B
-- plus the primitive fact hβα_cop if your induction hypothesis requires it.
--
-- So the final call has the schematic form:
--
--   exact ih α hBprime_lt_B β a hα_pos hβ_pos hβα_cop hnew_eq
```

## Why this is the right even-branch mirror of the odd branch

The odd branch applies the fourth-power split directly to raw factors.

The even branch must not do that: the raw factors satisfy

```lean
(r - H) * (r + H) = 4 * b ^ 4
```

and both factors are even.  After dividing by `2`, the half-factors satisfy the exact odd-branch product shape:

```lean
u * v = b ^ 4
Int.gcd u v = 1
```

So the rest is literally the odd-case split, with the only extra work being the `h2u/h2v` layer and the derivation of `huv_sum`, `huv_diff`, and `huv_prod`.

The new equation comes from

```text
v - u = H = a^2 - b^2,
u = α^4,
v = β^4,
b = αβ.
```

Therefore

```text
a^2 = H + b^2
    = (β^4 - α^4) + (αβ)^2
    = β^4 + α^2β^2 - α^4.
```

For the descent inequality, the robust close is

```text
α ≤ b ≤ B₁ < B.
```

This is enough for the strong-induction/minimal-counterexample contradiction.  The stricter `α < b` requires an additional non-unit proof for `β`; it is not the part that should carry the descent.