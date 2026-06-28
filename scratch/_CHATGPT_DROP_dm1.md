# Q1724 (dm1): `gcd(M,N)=1` proof for the even-`B` branch

Paste this as the replacement for the local goal:

```lean
Int.gcd M N = 1
```

It keeps `M,N` opaque and uses only `hM_val`, `hN_val`, `hMN_prod`, `hB₁_val`, positivity, and `hcop`.

```lean
by
  ---------------------------------------------------------------------------
  -- First extract the two linear identities from hM_val/hN_val.
  -- M,N are opaque after clear_value; do not unfold them.
  ---------------------------------------------------------------------------
  have hMN_sum : M + N = (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
    have h_sum :
        4 * (M + N) = 4 * ((2 * j + 1) ^ 2 + 2 * B₁ ^ 2) := by
      nlinarith [hM_val, hN_val, hB₁_val]
    omega

  have hNM_diff : N - M = s := by
    have h_diff : 4 * (N - M) = 4 * s := by
      nlinarith [hM_val, hN_val]
    omega

  ---------------------------------------------------------------------------
  -- Prime-divisor contradiction.
  ---------------------------------------------------------------------------
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

  have hp_sum_MN : (p : ℤ) ∣ M + N := by
    exact dvd_add hpM hpN

  have hp_diff_NM : (p : ℤ) ∣ N - M := by
    exact dvd_sub hpN hpM

  have hp_sum_expr :
      (p : ℤ) ∣ (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
    simpa [hMN_sum] using hp_sum_MN

  -- This follows from the outline.  The contradiction below does not need heq.
  have hp_s : (p : ℤ) ∣ s := by
    simpa [hNM_diff] using hp_diff_NM

  -- Since p divides both M and N, p^2 divides M*N.
  have hp2_MN : (p : ℤ) ^ 2 ∣ M * N := by
    rcases hpM with ⟨m, hm⟩
    rcases hpN with ⟨n, hn⟩
    refine ⟨m * n, ?_⟩
    rw [hm, hn]
    ring

  have hp2_rhs : (p : ℤ) ^ 2 ∣ 5 * B₁ ^ 4 := by
    simpa [hMN_prod] using hp2_MN

  by_cases hpB₁ : (p : ℤ) ∣ B₁
  · -------------------------------------------------------------------------
    -- Case 1: p | B₁.  Then p | 2k, hence p | 4k.  Also
    -- p | r^2 + 2B₁^2 and p | 2B₁^2, so p | r^2, hence p | r.
    -- This contradicts gcd(r,4k)=1.
    -------------------------------------------------------------------------
    have hp_B₁_sq : (p : ℤ) ∣ B₁ ^ 2 := by
      exact pow_dvd_pow_of_dvd hpB₁ 2

    have hp_two_B₁_sq : (p : ℤ) ∣ 2 * B₁ ^ 2 := by
      exact dvd_mul_of_dvd_right hp_B₁_sq 2

    have hp_r_sq : (p : ℤ) ∣ (2 * j + 1) ^ 2 := by
      have hsub :
          (p : ℤ) ∣
            ((2 * j + 1) ^ 2 + 2 * B₁ ^ 2) - 2 * B₁ ^ 2 := by
        exact dvd_sub hp_sum_expr hp_two_B₁_sq
      convert hsub using 1 <;> ring

    have hp_r : (p : ℤ) ∣ 2 * j + 1 := by
      exact hpZ_prime.dvd_of_dvd_pow hp_r_sq

    have hp_2k : (p : ℤ) ∣ 2 * k := by
      simpa [hB₁_val] using hpB₁

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

  · -------------------------------------------------------------------------
    -- Case 2: p ∤ B₁.  From p^2 | 5*B₁^4, first get p | 5*B₁^4.
    -- Since p ∤ B₁, the prime divisor must be p | 5, hence p = 5.
    -- Then 25 | 5*B₁^4 implies 5 | B₁^4, hence 5 | B₁, contradiction.
    -------------------------------------------------------------------------
    have hp_rhs : (p : ℤ) ∣ 5 * B₁ ^ 4 := by
      have hp_dvd_p2 : (p : ℤ) ∣ (p : ℤ) ^ 2 := by
        refine ⟨(p : ℤ), ?_⟩
        ring
      exact dvd_trans hp_dvd_p2 hp2_rhs

    rcases hpZ_prime.dvd_or_dvd hp_rhs with hp_dvd_5 | hp_dvd_B₁4
    · have hp_nat_dvd_5 : p ∣ (5 : ℕ) := by
        exact_mod_cast hp_dvd_5

      have hp_eq_5 : p = 5 := by
        have hp_le_five : p ≤ 5 :=
          Nat.le_of_dvd (by norm_num : 0 < (5 : ℕ)) hp_nat_dvd_5
        interval_cases p <;> simp at hp_prime hp_nat_dvd_5 ⊢

      subst p

      have h25 : (25 : ℤ) ∣ 5 * B₁ ^ 4 := by
        simpa using hp2_rhs

      have h5_B₁4 : (5 : ℤ) ∣ B₁ ^ 4 := by
        rcases h25 with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        nlinarith

      have h5_B₁ : (5 : ℤ) ∣ B₁ := by
        exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5_B₁4

      exact hpB₁ h5_B₁

    · have hp_B₁ : (p : ℤ) ∣ B₁ := by
        exact hpZ_prime.dvd_of_dvd_pow hp_dvd_B₁4

      exact hpB₁ hp_B₁
```

Notes:

* `hp_s` is derived exactly as in your outline, but the final contradiction does not need `heq`.
* The proof deliberately avoids unfolding `M` and `N`; all arithmetic involving them goes through `hM_val`, `hN_val`, `hMN_prod`, and positivity.
* If your local Mathlib snapshot has a different signature for `Nat.exists_prime_and_dvd`, replace only the `obtain` line with the one already used in your compiling `UV_coprime` proof. The divisor spine after that is the important part.