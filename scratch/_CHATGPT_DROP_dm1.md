# Q1811 (dm1): post-`u*v=b^4` descent tail

Paste this after you have

```lean
huv_cop  : Int.gcd u v = 1
huv_prod : u * v = b ^ 4
hu_pos   : 0 < u
hv_pos   : 0 < v
huv_sum  : u + v = 2 * j + 1
huv_diff : v - u = h
```

and `h` is the local abbreviation/definition `a^2-b^2`.

The block constructs the new witness `(r',B',s') = (β, α, a)`.

```lean
by
  classical

  ---------------------------------------------------------------------------
  -- 1. Split the coprime positive product u*v=b^4 into fourth powers.
  ---------------------------------------------------------------------------
  obtain ⟨α, β, hα_pos, hβ_pos, hu_eq, hv_eq⟩ :=
    pos_fourth_of_coprime_mul_fourth
      hu_pos hv_pos huv_cop huv_prod

  ---------------------------------------------------------------------------
  -- 2. Recover b = αβ from equality of fourth powers and positivity.
  ---------------------------------------------------------------------------
  have hαβ_pos : 0 < α * β := by
    nlinarith [hα_pos, hβ_pos]

  have hb_fourth : b ^ 4 = (α * β) ^ 4 := by
    calc
      b ^ 4 = u * v := by
        nlinarith [huv_prod]
      _ = α ^ 4 * β ^ 4 := by
        rw [hu_eq, hv_eq]
      _ = (α * β) ^ 4 := by
        ring

  have hb_eq : b = α * β :=
    eq_of_pos_fourth_eq hb hαβ_pos hb_fourth

  ---------------------------------------------------------------------------
  -- 3. New equation: a^2 = β^4 + α^2β^2 - α^4.
  ---------------------------------------------------------------------------
  have hdiff_ab : v - u = a ^ 2 - b ^ 2 := by
    simpa [h] using huv_diff

  have h_vu : a ^ 2 - b ^ 2 = β ^ 4 - α ^ 4 := by
    nlinarith [hdiff_ab, hu_eq, hv_eq]

  have hb_sq : b ^ 2 = α ^ 2 * β ^ 2 := by
    rw [hb_eq]
    ring

  have ha_sq : a ^ 2 = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
    calc
      a ^ 2 = (a ^ 2 - b ^ 2) + b ^ 2 := by
        ring
      _ = (β ^ 4 - α ^ 4) + b ^ 2 := by
        rw [h_vu]
      _ = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
        rw [hb_sq]
        ring

  ---------------------------------------------------------------------------
  -- 4. Construct the new QuarticPlusZ solution.
  ---------------------------------------------------------------------------
  have hQ : QuarticPlusZ β α a := by
    simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using ha_sq

  ---------------------------------------------------------------------------
  -- 5. Non-base.  If α=β=1, then u=v=1, hence 2*j+1=2, impossible.
  -- This is even shorter than routing through the old non-base hypothesis.
  ---------------------------------------------------------------------------
  have hnonbase_new : ¬ BaseZ β α := by
    intro hbase

    have hβ_one : β = 1 := by
      simpa [BaseZ] using hbase.1

    have hα_one : α = 1 := by
      simpa [BaseZ] using hbase.2

    have hu_one : u = 1 := by
      rw [hu_eq, hα_one]
      norm_num

    have hv_one : v = 1 := by
      rw [hv_eq, hβ_one]
      norm_num

    have hr_two : 2 * j + 1 = 2 := by
      nlinarith [huv_sum, hu_one, hv_one]

    omega

  ---------------------------------------------------------------------------
  -- 6. Size drop: α ≤ αβ=b ≤ ab=B₁ < B.
  -- Uses the even-branch facts B₁=2*k and B=4*k.
  ---------------------------------------------------------------------------
  have hk_pos : 0 < k := by
    -- Replace `hB₁_val` by the local name for `B₁ = 2*k`.
    nlinarith [hB₁_val, hB₁_eq, ha, hb]

  have hα_le_b : α ≤ b := by
    rw [hb_eq]
    have hβ_ge_one : 1 ≤ β := by omega
    nlinarith [hα_pos, hβ_ge_one]

  have hb_le_B₁ : b ≤ B₁ := by
    rw [hB₁_eq]
    have ha_ge_one : 1 ≤ a := by omega
    nlinarith [ha_ge_one, hb]

  have hB₁_lt_B : B₁ < B := by
    rw [hB₁_val, hBk]
    nlinarith [hk_pos]

  have hα_lt_B : α < B :=
    lt_of_le_of_lt (le_trans hα_le_b hb_le_B₁) hB₁_lt_B

  have hdrop : α.natAbs < B.natAbs := by
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hB_nonneg : 0 ≤ B := by
      rw [hBk]
      nlinarith [hk_pos]
    rw [Int.natAbs_of_nonneg hα_nonneg, Int.natAbs_of_nonneg hB_nonneg]
    exact_mod_cast hα_lt_B

  exact ⟨β, α, a, hQ, hnonbase_new, hdrop⟩
```

If your local `pos_fourth_of_coprime_mul_fourth` also returns `b = α*β`, use this destructuring instead and delete the `eq_of_pos_fourth_eq` block:

```lean
obtain ⟨α, β, hα_pos, hβ_pos, hu_eq, hv_eq, hb_eq⟩ :=
  pos_fourth_of_coprime_mul_fourth hu_pos hv_pos huv_cop huv_prod
```

If `BaseZ` is not a pair-like proposition with fields `.1` and `.2`, replace the two extraction lines with the destructor used in the odd case.  The contradiction after `α=β=1` only needs `huv_sum`, `hu_eq`, and `hv_eq`.