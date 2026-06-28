# Q1653 (dm1): even-`B` branch after `M * N = 5 * B₁ ^ 4`

I could not get the connector code search to locate the actual line-498 file, so the proof below is written against the exact local API in your handoff. The only expected edits are local hypothesis names and the tuple order returned by `coprime_factor_5_fourth` / `pos_fourth_of_coprime_mul_fourth` if your file uses a different order.

The main point is that the branch should close by producing the smaller solution

```lean
⟨β, α, a⟩
```

where `M = a^4`, `N = 5*b^4`, `B₁ = a*b`, and the half-factor split gives `u = α^4`, `v = β^4`, `b = α*β`.

## Replacement proof body

Paste this at the even-`B` sorry. I have used the following names from your handoff:

```lean
hMN_prod : M * N = 5 * B₁ ^ 4
hM_pos   : 0 < M
hN_pos   : 0 < N
hM_val   : 4 * M = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s
hN_val   : 4 * N = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s
hB₁_def  : B₁ = 2 * k
hcop     : Int.gcd (2 * j + 1) (4 * k) = 1
```

If the actual positivity names are different, rename only the first two lines.

```lean
by
  -- Rename these two aliases if the local names differ.
  have hMpos : 0 < M := hM_pos
  have hNpos : 0 < N := hN_pos

  ---------------------------------------------------------------------------
  -- The two linear identities for the half-cleared factors.
  ---------------------------------------------------------------------------
  have hMN_sum : M + N = (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
    have h4 :
        4 * (M + N) = 4 * ((2 * j + 1) ^ 2 + 2 * B₁ ^ 2) := by
      rw [hB₁_def]
      nlinarith [hM_val, hN_val]
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

  have hNM_diff : N - M = s := by
    have h4 : 4 * (N - M) = 4 * s := by
      nlinarith [hM_val, hN_val]
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

  ---------------------------------------------------------------------------
  -- gcd(M,N)=1.
  -- This is the same prime-divisor spine as UV_coprime, except that because
  -- the product is 5*B₁^4 we use p^2 | M*N to force p | B₁ even for p=5.
  ---------------------------------------------------------------------------
  have hMN_cop : Int.gcd M N = 1 := by
    by_contra hbad

    have hgpos : 0 < Int.gcd M N := by
      exact Int.gcd_pos_of_pos_left N hMpos

    have hg_gt_one : 1 < Int.gcd M N := by
      omega

    obtain ⟨p, hp_prime, hp_dvd_g⟩ :=
      Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)

    have hpZ_prime : Prime (p : ℤ) := by
      exact_mod_cast hp_prime

    have hp_dvd_g_int : (p : ℤ) ∣ (Int.gcd M N : ℤ) := by
      exact_mod_cast hp_dvd_g

    have hpM : (p : ℤ) ∣ M := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_left M N)

    have hpN : (p : ℤ) ∣ N := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_right M N)

    have hp2_MN : (p : ℤ) ^ 2 ∣ M * N := by
      rcases hpM with ⟨m, hm⟩
      rcases hpN with ⟨n, hn⟩
      refine ⟨m * n, ?_⟩
      rw [hm, hn]
      ring

    have hp2_rhs : (p : ℤ) ^ 2 ∣ 5 * B₁ ^ 4 := by
      simpa [hMN_prod] using hp2_MN

    have hpB₁ : (p : ℤ) ∣ B₁ := by
      by_cases hp5 : p = 5
      · subst p
        have h25 : (25 : ℤ) ∣ 5 * B₁ ^ 4 := by
          simpa using hp2_rhs
        have h5B4 : (5 : ℤ) ∣ B₁ ^ 4 := by
          rcases h25 with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          nlinarith
        exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5B4
      · have hp_rhs : (p : ℤ) ∣ 5 * B₁ ^ 4 := by
          exact dvd_trans (by exact dvd_mul_right (p : ℤ) (p : ℤ)) hp2_rhs
        rcases hpZ_prime.dvd_or_dvd hp_rhs with hp_dvd_5 | hp_dvd_B4
        · exfalso
          have hp_nat_dvd_5 : p ∣ 5 := by
            exact_mod_cast hp_dvd_5
          have hp_le_five : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp_nat_dvd_5
          interval_cases p <;> simp at hp_prime hp5 hp_nat_dvd_5
        · exact hpZ_prime.dvd_of_dvd_pow hp_dvd_B4

    have hp_sum : (p : ℤ) ∣ M + N := dvd_add hpM hpN

    have hp_sum_expr :
        (p : ℤ) ∣ (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
      simpa [hMN_sum] using hp_sum

    have hp_B₁_sq : (p : ℤ) ∣ B₁ ^ 2 := by
      exact pow_dvd_pow_of_dvd hpB₁ 2

    have hp_two_B₁_sq : (p : ℤ) ∣ 2 * B₁ ^ 2 := by
      exact dvd_mul_of_dvd_right hp_B₁_sq 2

    have hp_r_sq : (p : ℤ) ∣ (2 * j + 1) ^ 2 := by
      convert dvd_sub hp_sum_expr hp_two_B₁_sq using 1 <;> ring

    have hp_r : (p : ℤ) ∣ 2 * j + 1 := by
      exact hpZ_prime.dvd_of_dvd_pow hp_r_sq

    have hp_2k : (p : ℤ) ∣ 2 * k := by
      simpa [hB₁_def] using hpB₁

    have hp_4k : (p : ℤ) ∣ 4 * k := by
      have htmp : (p : ℤ) ∣ 2 * (2 * k) := by
        exact dvd_mul_of_dvd_right hp_2k 2
      convert htmp using 1 <;> ring

    have hp_gcd : (p : ℤ) ∣ (Int.gcd (2 * j + 1) (4 * k) : ℤ) := by
      exact Int.dvd_gcd hp_r hp_4k

    have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcop] using hp_gcd

    have hp_one_nat : p ∣ (1 : ℕ) := by
      exact_mod_cast hp_one

    exact hp_prime.not_dvd_one hp_one_nat

  ---------------------------------------------------------------------------
  -- Split M*N = 5*B₁^4 with gcd(M,N)=1.
  -- Expected orientation:
  --   M = a^4, N = 5*b^4, B₁ = a*b.
  -- If your helper returns these equations in a different order, only adjust
  -- the obtain pattern and the names used below.
  ---------------------------------------------------------------------------
  obtain ⟨a, b, ha_pos, hb_pos, hB₁_eq_ab, hM_eq_a4, hN_eq_5b4⟩ :=
    coprime_factor_5_fourth hMpos hNpos hMN_cop hMN_prod

  have hB₁_pos : 0 < B₁ := by
    rw [hB₁_eq_ab]
    exact mul_pos ha_pos hb_pos

  ---------------------------------------------------------------------------
  -- From M+N = r^2 + 2B₁^2 and the split, derive
  --   r^2 = (a^2-b^2)^2 + 4b^4.
  ---------------------------------------------------------------------------
  have hr_sq_ab :
      (2 * j + 1) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
    calc
      (2 * j + 1) ^ 2 = M + N - 2 * B₁ ^ 2 := by
        nlinarith [hMN_sum]
      _ = a ^ 4 + 5 * b ^ 4 - 2 * (a * b) ^ 2 := by
        rw [hM_eq_a4, hN_eq_5b4, hB₁_eq_ab]
        ring
      _ = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
        ring

  ---------------------------------------------------------------------------
  -- Half-factor descent.
  ---------------------------------------------------------------------------
  let h : ℤ := a ^ 2 - b ^ 2

  have hr_sq_h : (2 * j + 1) ^ 2 = h ^ 2 + 4 * b ^ 4 := by
    simpa [h] using hr_sq_ab

  have hr_pos_local : 0 < 2 * j + 1 := by
    -- In the surrounding branch this is usually `hr_pos` after substituting
    -- `r = 2*j+1`.
    simpa using hr_pos

  have hr_odd : Odd (2 * j + 1) := by
    refine ⟨j, ?_⟩
    ring

  -- The parity fact is the only non-arithmetic side condition in the half
  -- factor layer.  In the file this should be available from the mixed parity
  -- of a,b in the even-B split.  Common names are `h_odd_h`, `hh_odd`, or a
  -- theorem proving oddness from `hr_sq_h` and `hr_odd`.
  have hh_odd : Odd h := by
    -- Replace this line by the local mixed-parity lemma if it has a name.
    -- For example, if the factor helper returns `ha_odd : Odd a` and
    -- `hb_even : Even b`, then:
    --   simpa [h] using ha_odd.pow.sub_even (hb_even.pow 2)
    exact h_odd

  have h2u_dvd : (2 : ℤ) ∣ 2 * j + 1 - h := by
    rcases hr_odd with ⟨jr, hjr⟩
    rcases hh_odd with ⟨jh, hjh⟩
    refine ⟨jr - jh, ?_⟩
    nlinarith

  have h2v_dvd : (2 : ℤ) ∣ 2 * j + 1 + h := by
    rcases hr_odd with ⟨jr, hjr⟩
    rcases hh_odd with ⟨jh, hjh⟩
    refine ⟨jr + jh + 1, ?_⟩
    nlinarith

  let u : ℤ := (2 * j + 1 - h) / 2
  let v : ℤ := (2 * j + 1 + h) / 2

  have h2u : 2 * u = 2 * j + 1 - h := by
    dsimp [u]
    exact Int.mul_ediv_cancel' h2u_dvd

  have h2v : 2 * v = 2 * j + 1 + h := by
    dsimp [v]
    exact Int.mul_ediv_cancel' h2v_dvd

  have hprod_rh :
      (2 * j + 1 - h) * (2 * j + 1 + h) = 4 * b ^ 4 := by
    nlinarith [hr_sq_h]

  have hprod_pos : 0 < (2 * j + 1 - h) * (2 * j + 1 + h) := by
    have hb4_pos : 0 < b ^ 4 := pow_pos hb_pos 4
    nlinarith [hprod_rh, hb4_pos]

  have hRH_pos : 0 < 2 * j + 1 - h ∧ 0 < 2 * j + 1 + h := by
    rcases (mul_pos_iff.mp hprod_pos) with hpos | hneg
    · exact hpos
    · rcases hneg with ⟨hleft, hright⟩
      have hsum_neg : (2 * j + 1 - h) + (2 * j + 1 + h) < 0 := by
        exact add_neg hleft hright
      have hsum_pos : 0 < (2 * j + 1 - h) + (2 * j + 1 + h) := by
        nlinarith [hr_pos_local]
      linarith

  have hu_pos : 0 < u := by
    nlinarith [h2u, hRH_pos.1]

  have hv_pos : 0 < v := by
    nlinarith [h2v, hRH_pos.2]

  have huv_sum : u + v = 2 * j + 1 := by
    have h2sum : 2 * (u + v) = 2 * (2 * j + 1) := by
      nlinarith [h2u, h2v]
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2sum

  have huv_diff : v - u = h := by
    have h2diff : 2 * (v - u) = 2 * h := by
      nlinarith [h2u, h2v]
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2diff

  have huv_prod : u * v = b ^ 4 := by
    have hprod2 : (2 * u) * (2 * v) = 4 * b ^ 4 := by
      calc
        (2 * u) * (2 * v)
            = (2 * j + 1 - h) * (2 * j + 1 + h) := by
                rw [h2u, h2v]
        _   = 4 * b ^ 4 := hprod_rh
    have hprod4 : 4 * (u * v) = 4 * b ^ 4 := by
      nlinarith [hprod2]
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hprod4

  ---------------------------------------------------------------------------
  -- gcd(u,v)=1, then split u*v=b^4.
  ---------------------------------------------------------------------------
  have huv_cop : Int.gcd u v = 1 := by
    -- This is your adapted half-factor gcd lemma:
    -- p|u,v -> p|u+v=r and p|u*v=b^4 -> p|b, contradicting gcd(r,b)=1.
    exact coprime_rh hu_pos hv_pos hb_pos hcop hB₁_eq_ab huv_sum huv_prod

  obtain ⟨α, β, hα_pos, hβ_pos, hu_eq_α4, hv_eq_β4, hb_eq_αβ⟩ :=
    pos_fourth_of_coprime_mul_fourth hu_pos hv_pos hb_pos huv_cop huv_prod

  have hαβ_cop : Int.gcd α β = 1 := by
    by_contra hbad
    have hgpos : 0 < Int.gcd α β := by
      exact Int.gcd_pos_of_pos_left β hα_pos
    have hg_gt_one : 1 < Int.gcd α β := by
      omega
    obtain ⟨p, hp_prime, hp_dvd_g⟩ :=
      Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)
    have hpZ_prime : Prime (p : ℤ) := by
      exact_mod_cast hp_prime
    have hp_dvd_g_int : (p : ℤ) ∣ (Int.gcd α β : ℤ) := by
      exact_mod_cast hp_dvd_g
    have hpα : (p : ℤ) ∣ α := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_left α β)
    have hpβ : (p : ℤ) ∣ β := by
      exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_right α β)
    have hpu : (p : ℤ) ∣ u := by
      rw [hu_eq_α4]
      exact pow_dvd_pow_of_dvd hpα 4
    have hpv : (p : ℤ) ∣ v := by
      rw [hv_eq_β4]
      exact pow_dvd_pow_of_dvd hpβ 4
    have hp_gcd : (p : ℤ) ∣ (Int.gcd u v : ℤ) := by
      exact Int.dvd_gcd hpu hpv
    have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [huv_cop] using hp_gcd
    have hp_one_nat : p ∣ (1 : ℕ) := by
      exact_mod_cast hp_one
    exact hp_prime.not_dvd_one hp_one_nat

  have hβα_cop : Int.gcd β α = 1 := by
    simpa [Int.gcd_comm] using hαβ_cop

  ---------------------------------------------------------------------------
  -- New equation: a^2 = β^4 + α^2β^2 - α^4.
  ---------------------------------------------------------------------------
  have hnew_eq_alpha_beta :
      a ^ 2 = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
    calc
      a ^ 2 = h + b ^ 2 := by
        dsimp [h]
        ring
      _ = (v - u) + (α * β) ^ 2 := by
        rw [← huv_diff, hb_eq_αβ]
      _ = (β ^ 4 - α ^ 4) + (α * β) ^ 2 := by
        rw [hu_eq_α4, hv_eq_β4]
      _ = β ^ 4 + α ^ 2 * β ^ 2 - α ^ 4 := by
        ring

  have hnew_eq :
      a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnew_eq_alpha_beta

  ---------------------------------------------------------------------------
  -- Descent bound: α ≤ b ≤ B₁ < B = 4*k.
  ---------------------------------------------------------------------------
  have hα_le_b : α ≤ b := by
    have hβ_ge_one : (1 : ℤ) ≤ β := by
      omega
    calc
      α = α * 1 := by ring
      _ ≤ α * β := by
        exact mul_le_mul_of_nonneg_left hβ_ge_one (le_of_lt hα_pos)
      _ = b := hb_eq_αβ.symm

  have hb_le_B₁ : b ≤ B₁ := by
    have ha_ge_one : (1 : ℤ) ≤ a := by
      omega
    rw [hB₁_eq_ab]
    calc
      b = 1 * b := by ring
      _ ≤ a * b := by
        exact mul_le_mul_of_nonneg_right ha_ge_one (le_of_lt hb_pos)

  have hB₁_lt_B : B₁ < 4 * k := by
    rw [hB₁_def]
    nlinarith [hB₁_pos]

  have hα_lt_B : α < 4 * k := by
    exact lt_of_le_of_lt (le_trans hα_le_b hb_le_B₁) hB₁_lt_B

  have hα_natAbs_lt_B_natAbs : α.natAbs < (4 * k).natAbs := by
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hB_pos : 0 < 4 * k := by
      nlinarith [hB₁_pos, hB₁_def]
    rw [Int.natAbs_of_nonneg hα_nonneg, Int.natAbs_of_nonneg (le_of_lt hB_pos)]
    exact_mod_cast hα_lt_B

  ---------------------------------------------------------------------------
  -- New solution is not base.  If BaseZ is defined as `r = 1 ∧ B = 1`, this
  -- block compiles as-is.  If it is defined using natAbs, keep the same proof
  -- idea and replace the two `simp [BaseZ]` projections by the natAbs-to-1
  -- conversions.
  ---------------------------------------------------------------------------
  have hnew_nonbase : ¬ BaseZ β α := by
    intro hbase
    have hβ_one : β = 1 := by
      simpa [BaseZ] using hbase.1
    have hα_one : α = 1 := by
      simpa [BaseZ] using hbase.2
    have hb_one : b = 1 := by
      rw [hb_eq_αβ, hα_one, hβ_one]
      norm_num
    have ha_sq_one : a ^ 2 = 1 := by
      simpa [hα_one, hβ_one] using hnew_eq
    have ha_one : a = 1 := by
      nlinarith [ha_pos, ha_sq_one]
    have hB₁_one : B₁ = 1 := by
      rw [hB₁_eq_ab, ha_one, hb_one]
      norm_num
    have htwo_k_one : 2 * k = 1 := by
      simpa [hB₁_def] using hB₁_one
    omega

  ---------------------------------------------------------------------------
  -- Package the new QuarticPlusZ solution and return the existential.
  ---------------------------------------------------------------------------
  have hnew_quartic : QuarticPlusZ β α a := by
    -- If `QuarticPlusZ` is a structure/def with fields in the standard order
    --   0<r, 0<B, gcd r B=1, s^2 = r^4 + r^2*B^2 - B^4,
    -- this constructor closes directly.
    refine ⟨hβ_pos, hα_pos, hβα_cop, ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnew_eq

  exact ⟨β, α, a, hnew_quartic, hnew_nonbase, hα_natAbs_lt_B_natAbs⟩
```

## Two likely local adjustments

1. **The parity line.** In the proof above I wrote

```lean
exact h_odd
```

inside `hh_odd : Odd h`. Replace `h_odd` by the local mixed-parity fact for `a^2-b^2`. If your `coprime_factor_5_fourth` helper already returns parity fields, the intended proof is one of these:

```lean
-- a odd, b even
simpa [h] using ha_odd.pow.sub_even (hb_even.pow 2)

-- a even, b odd
simpa [h, sub_eq_add_neg] using (hb_odd.pow 2).neg_add_even (ha_even.pow 2)
```

If your parity API names differ, the mathematical fact needed is just `Odd (a^2-b^2)`.

2. **The helper tuple order.** If `coprime_factor_5_fourth` returns

```lean
M = 5 * b^4, N = a^4
```

instead of

```lean
M = a^4, N = 5*b^4
```

then swap the names at the `obtain` line. The subsequent equation must use the orientation producing

```lean
M + N = a^4 + 5*b^4
```

because that is what gives

```lean
r^2 = (a^2-b^2)^2 + 4*b^4.
```

## Why the proof closes

The branch has two independent gcd arguments.

First, for `gcd(M,N)=1`, a prime dividing both `M` and `N` has square dividing `M*N = 5B₁^4`. This forces the prime to divide `B₁`, including the special case `p=5`. Since the same prime divides `M+N = r^2+2B₁^2`, it divides `r`; and since `B₁=2k`, it divides `4k`, contradicting `Int.gcd (2*j+1) (4*k)=1`.

Second, for `gcd(u,v)=1`, the adapted `coprime_rh` gives the standard half-factor argument: a prime dividing both `u` and `v` divides `u+v=r` and `u*v=b^4`, hence divides `b`; this contradicts the inherited primitive condition.

The descent inequality does not need the stronger `α < b`; it is enough that

```lean
α ≤ b ≤ B₁ < 4*k = B.
```

The nonbase proof rules out `β=α=1`: then `b=1`, the new equation gives `a=1`, so `B₁=a*b=1`, contradicting `B₁=2*k`.