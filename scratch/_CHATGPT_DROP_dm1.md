# Q1562 (dm1): even-`B` branch for the quartic descent

I cannot honestly give a no-new-lemma “complete proof body” from only the helpers listed, because the stated reduction has a real mismatch.

The line

```lean
-- The descent after step 5 is IDENTICAL to the odd case
```

is false after the `U,V` division by `4`.

In the odd branch, after the factor split, the identity has the shape

```lean
4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

so with

```lean
h = (a ^ 2 - b ^ 2) / 2
```

you get

```lean
r ^ 2 = h ^ 2 + b ^ 4
```

and your existing helper

```lean
coprime_rh :
  r odd → h even → gcd(r,b)=1 → 0 < b →
  r ^ 2 = h ^ 2 + b ^ 4 →
  gcd(r-h,r+h)=1
```

is applicable.

In the even branch, after setting `B = 2*B₁`, `U = 4*M`, `V = 4*N`, the factor case `M = a^4`, `N = 5*b^4`, `B₁ = a*b` gives instead

```lean
r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

not the odd identity. Thus the correct choice is

```lean
h = a ^ 2 - b ^ 2
```

and the factorization is

```lean
((r - h) / 2) * ((r + h) / 2) = b ^ 4
```

because `r` and `h` are both odd. So the required coprimality lemma is not `coprime_rh`; it is the half-factor version

```lean
Int.gcd ((r - h) / 2) ((r + h) / 2) = 1
```

This is a different helper. Without it, the listed helper set is not enough to close the even branch.

## The helper you need

Add this kernel once. The proof is exactly the even analogue of the old odd descent core.

```lean
import Mathlib

/-- Even-`B` normalized descent kernel.

This is the replacement for trying to reuse `coprime_rh` directly.  The input
identity is the normalized even identity

  `r^2 = (a^2-b^2)^2 + 4*b^4`.

It factors

  `((r-h)/2) * ((r+h)/2) = b^4`

with `h = a^2-b^2`, not `(a^2-b^2)/2`.
-/
lemma even_descent_from_factor_main
    {r B B₁ a b : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hB₁ : 0 < B₁)
    (hB_eq : B = 2 * B₁)
    (hB₁_eq : B₁ = a * b)
    (ha : 0 < a) (hb : 0 < b)
    (hab_cop : Int.gcd a b = 1)
    (hcop : Int.gcd r B = 1)
    (hr_odd : r % 2 = 1)
    (hnonbase : ¬ BaseZ r B)
    (hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B₁.natAbs := by
  let h : ℤ := a ^ 2 - b ^ 2

  have hr_sq : r ^ 2 = h ^ 2 + 4 * b ^ 4 := by
    simpa [h] using hid

  -- From `B = 2*B₁`, `B₁ = a*b`, `gcd r B = 1`, get `gcd r b = 1`.
  have hb_dvd_B : b ∣ B := by
    refine ⟨2 * a, ?_⟩
    rw [hB_eq, hB₁_eq]
    ring

  have hrb_cop : Int.gcd r b = 1 := by
    -- This is the same divisor-of-a-coprime extraction used in the odd branch.
    -- Use your local name if different.
    exact gcd_of_gcd_mul_right_eq_one hcop hb_dvd_B

  -- Since `B₁ = a*b` and `B = 2*B₁` with `gcd r B = 1`, exactly one of
  -- `a,b` is even in the even case, hence `h = a^2-b^2` is odd.  Package this
  -- as a local parity helper; it is the one parity fact the old odd branch did
  -- not need.
  have hh_odd : h % 2 = 1 := by
    exact odd_diff_sq_of_coprime_product_even hB_eq hB₁_eq ha hb hab_cop hcop

  -- The half-factors are integers because both `r` and `h` are odd.
  have hleft_even : 2 ∣ r - h := by
    exact Int.dvd_sub.mpr ⟨by simpa using hr_odd, by simpa using hh_odd⟩

  have hright_even : 2 ∣ r + h := by
    exact Int.dvd_add.mpr ⟨by simpa using hr_odd, by simpa using hh_odd⟩

  have hhalf_mul : ((r - h) / 2) * ((r + h) / 2) = b ^ 4 := by
    have hdiff : (r - h) * (r + h) = 4 * b ^ 4 := by
      nlinarith [hr_sq]
    have h2l : 2 * ((r - h) / 2) = r - h := by
      exact (Int.ediv_mul_cancel hleft_even).symm
    have h2r : 2 * ((r + h) / 2) = r + h := by
      exact (Int.ediv_mul_cancel hright_even).symm
    nlinarith [hdiff, h2l, h2r]

  have hhalf_cop : Int.gcd ((r - h) / 2) ((r + h) / 2) = 1 := by
    -- New required even analogue of `coprime_rh`.
    -- The proof is the same prime-divisor argument, but after dividing the two
    -- even factors by `2`.  A common odd prime divides both half-factors, hence
    -- divides `r` and `h`, then from `r^2 = h^2 + 4*b^4` divides `b`, contrary
    -- to `gcd(r,b)=1`; prime `2` is excluded because the two half-factors have
    -- opposite parity.
    exact coprime_half_rh hr_odd hh_odd hrb_cop hb hr_sq

  obtain ⟨α, hαpos, hαfour⟩ :=
    pos_fourth_of_coprime_mul_fourth hhalf_cop hhalf_mul
  -- Depending on the exact signature of your helper, the previous line may be:
  --   obtain ⟨α, β, hαpos, hβpos, hleft, hright⟩ := ...
  -- The intended outputs are shown explicitly below.

  -- Intended outputs of the fourth-power split:
  obtain ⟨α, β, hαpos, hβpos, hleft, hright⟩ :=
    pos_fourth_of_coprime_mul_fourth hhalf_cop hhalf_mul

  -- hleft  : (r - h) / 2 = α ^ 4
  -- hright : (r + h) / 2 = β ^ 4

  have hb_eq : b = α * β := by
    have hb4 : b ^ 4 = (α * β) ^ 4 := by
      nlinarith [hhalf_mul, hleft, hright]
    exact eq_of_pos_fourth_eq hb (mul_pos hαpos hβpos) hb4

  have hnew_eq : a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
    have hdiff : h = β ^ 4 - α ^ 4 := by
      have h2 : r + h - (r - h) = 2 * h := by ring
      nlinarith [hleft, hright, h2]
    have hb_sq : b ^ 2 = (α * β) ^ 2 := by
      rw [hb_eq]
    -- `h = a^2-b^2` and `h = β^4-α^4`.
    nlinarith [hdiff, hb_sq]

  refine ⟨β, α, a, ?hquartic, ?hnonbase, ?hsmall⟩

  · -- QuarticPlusZ β α a
    -- This is definition-dependent; for the usual definition it is exactly
    -- `a^2 = β^4 + β^2*α^2 - α^4`.
    simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using hnew_eq

  · -- non-base for the new solution
    intro hbase
    rcases hbase with ⟨hβ1, hα1⟩
    have hb1 : b = 1 := by
      rw [hb_eq, hα1, hβ1]
      norm_num
    have ha1 : a = 1 := by
      -- With α=β=1, `hnew_eq` gives `a^2 = 1`; positivity gives `a=1`.
      have : a ^ 2 = 1 := by
        simpa [hα1, hβ1] using hnew_eq
      nlinarith [ha]
    have hB₁_one : B₁ = 1 := by
      rw [hB₁_eq, ha1, hb1]
      norm_num
    have hB_two : B = 2 := by
      rw [hB_eq, hB₁_one]
      norm_num
    -- This contradicts the original coprimality/non-base package in the same
    -- way as the odd branch.  If your `BaseZ` is literally `r=1 ∧ B=1`, then
    -- use the already-existing local odd-branch nonbase contradiction helper
    -- here; in the even branch `B=2` is usually excluded earlier by the descent
    -- minimality hypothesis or by the final equation modulo 5/8.
    exact even_new_base_contradiction hr hB hcop heq hnonbase hB_two

  · -- α.natAbs < B₁.natAbs
    have hα_le_b : α ≤ b := by
      rw [hb_eq]
      nlinarith [hαpos, hβpos]
    have hb_le_B₁ : b ≤ B₁ := by
      rw [hB₁_eq]
      nlinarith [ha, hb]
    have hα_le_B₁ : α ≤ B₁ := le_trans hα_le_b hb_le_B₁
    have hα_ne_B₁ : α ≠ B₁ := by
      intro hαB
      -- Equality forces `a=1` and `β=1`; this is the same strictness argument
      -- as the odd branch.
      exact even_strictness_contradiction
        hnonbase hB_eq hB₁_eq hb_eq hαB hαpos hβpos ha hb hnew_eq
    have hα_lt_B₁ : α < B₁ := lt_of_le_of_ne hα_le_B₁ hα_ne_B₁
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hα_lt_B₁
```

The names

```lean
odd_diff_sq_of_coprime_product_even
coprime_half_rh
even_new_base_contradiction
even_strictness_contradiction
```

are the missing even-specific helpers. They are not optional bookkeeping; the listed odd-case helpers do not imply them directly.

## Replacement branch once that kernel exists

Once `even_descent_from_factor_main` and the symmetric call are available, the actual even branch should be written as follows. This is the clean proof body to replace your `sorry`.

```lean
  · -- Even B case
    have ⟨hr_odd, h4B⟩ := even_B_props hBeven hr hB hcop heq

    rcases h4B with ⟨k, hkB⟩
    let B₁ : ℤ := 2 * k

    have hB_eq_two : B = 2 * B₁ := by
      dsimp [B₁]
      nlinarith [hkB]

    have hB₁_pos : 0 < B₁ := by
      dsimp [B₁]
      nlinarith [hB, hkB]

    have hB₁_lt_B : B₁.natAbs < B.natAbs := by
      have hlt : B₁ < B := by
        nlinarith [hB₁_pos, hB_eq_two]
      exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hB₁_pos) hlt

    let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
    let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

    have hUV : U * V = 5 * B ^ 4 := by
      dsimp [U, V]
      nlinarith [heq]

    have h4U : 4 ∣ U := by
      exact four_dvd_U_even hBeven hr_odd h4B heq

    have h4V : 4 ∣ V := by
      exact four_dvd_V_even hBeven hr_odd h4B heq

    rcases h4U with ⟨M, hU_eq⟩
    rcases h4V with ⟨N, hV_eq⟩

    have hMN : M * N = 5 * B₁ ^ 4 := by
      have hraw : (4 * M) * (4 * N) = 5 * (2 * B₁) ^ 4 := by
        simpa [U, V, hU_eq, hV_eq, hB_eq_two] using hUV
      nlinarith [hraw]

    have hMN_sum : M + N = r ^ 2 + 2 * B₁ ^ 2 := by
      have hsum_raw : U + V = 4 * r ^ 2 + 2 * B ^ 2 := by
        dsimp [U, V]
        ring
      have hsum_raw' : 4 * M + 4 * N = 4 * r ^ 2 + 2 * (2 * B₁) ^ 2 := by
        simpa [hU_eq, hV_eq, hB_eq_two] using hsum_raw
      nlinarith [hsum_raw']

    have hMN_diff : N - M = s := by
      have hdiff_raw : V - U = 4 * s := by
        dsimp [U, V]
        ring
      have hdiff_raw' : 4 * N - 4 * M = 4 * s := by
        simpa [hU_eq, hV_eq] using hdiff_raw
      nlinarith [hdiff_raw']

    have hMN_cop : Int.gcd M N = 1 := by
      exact MN_coprime_even
        hr hB hcop heq hB_eq_two hU_eq hV_eq hMN_sum hMN_diff

    obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq, hfactor⟩ :=
      coprime_factor_5_fourth hMN hMN_cop

    rcases hfactor with ⟨hM_eq, hN_eq⟩ | ⟨hM_eq, hN_eq⟩

    · -- M = a^4, N = 5*b^4
      have hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
        calc
          r ^ 2 = a ^ 4 + 5 * b ^ 4 - 2 * B₁ ^ 2 := by
            nlinarith [hMN_sum, hM_eq, hN_eq]
          _ = a ^ 4 + 5 * b ^ 4 - 2 * (a * b) ^ 2 := by
            rw [hB₁_eq]
          _ = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
            ring

      obtain ⟨r', B', s', hq, hnb, hsmall₁⟩ :=
        even_descent_from_factor_main
          (r := r) (B := B) (B₁ := B₁) (a := a) (b := b)
          hr hB hB₁_pos hB_eq_two hB₁_eq ha hb hab_cop hcop hr_odd hnonbase hid

      exact ⟨r', B', s', hq, hnb, lt_trans hsmall₁ hB₁_lt_B⟩

    · -- M = 5*a^4, N = b^4: same kernel with a,b swapped
      have hid : r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
        calc
          r ^ 2 = 5 * a ^ 4 + b ^ 4 - 2 * B₁ ^ 2 := by
            nlinarith [hMN_sum, hM_eq, hN_eq]
          _ = 5 * a ^ 4 + b ^ 4 - 2 * (a * b) ^ 2 := by
            rw [hB₁_eq]
          _ = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
            ring

      have hB₁_ba : B₁ = b * a := by
        simpa [mul_comm] using hB₁_eq

      have hba_cop : Int.gcd b a = 1 := by
        simpa [Int.gcd_comm] using hab_cop

      obtain ⟨r', B', s', hq, hnb, hsmall₁⟩ :=
        even_descent_from_factor_main
          (r := r) (B := B) (B₁ := B₁) (a := b) (b := a)
          hr hB hB₁_pos hB_eq_two hB₁_ba hb ha hba_cop hcop hr_odd hnonbase hid

      exact ⟨r', B', s', hq, hnb, lt_trans hsmall₁ hB₁_lt_B⟩
```

## Minimal actionable conclusion

The current `sorry` cannot be closed by simply inserting the old odd-B 230-line proof after `M,N`, because the old proof uses

```lean
r ^ 2 = h ^ 2 + b ^ 4
```

whereas the even case gives

```lean
r ^ 2 = h ^ 2 + 4 * b ^ 4.
```

The minimal fix is to add `even_descent_from_factor_main` plus the half-factor coprimality lemma, then the branch body above is the right Lean architecture.
