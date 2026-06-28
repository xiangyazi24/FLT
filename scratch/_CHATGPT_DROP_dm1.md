# Q1571 (dm1): `gcd(M,N)=1` in the even-`B` quartic descent

There is a small but important correction to the requested prime-divisor outline.

From

```lean
hpM : (p : ℤ) ∣ M
hpN : (p : ℤ) ∣ N
hMN_prod : M * N = 5 * B₁ ^ 4
hnpB₁ : ¬ (p : ℤ) ∣ B₁
```

you do **not** get a contradiction from only `p ∣ M*N`; you must use `p^2 ∣ M*N`. Then `p^2 ∣ 5*B₁^4`; if `p ∤ B₁`, this forces `p = 5`, and the second copy of `p` then forces `5 ∣ B₁`, contradiction.

Below is the Lean body I would use. It deliberately proves the two linear identities first, then does the prime-divisor contradiction.

```lean
import Mathlib

-- Context variables assumed in the branch:
--   M N B₁ j k s : ℤ
--   hMN_prod : M * N = 5 * B₁ ^ 4
--   hMpos    : 0 < M
--   hNpos    : 0 < N
--   hM_val   : 4 * M = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s
--   hN_val   : 4 * N = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s
--   hB₁_val  : B₁ = 2 * k
--   hcop     : Int.gcd (2 * j + 1) (4 * k) = 1
--   heq      : s ^ 2 = (2 * j + 1) ^ 4
--                  + (2 * j + 1) ^ 2 * (4 * k) ^ 2
--                  - (4 * k) ^ 4

have hMN_sum : M + N = (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
  have h4sum : 4 * (M + N) = 4 * ((2 * j + 1) ^ 2 + 2 * B₁ ^ 2) := by
    rw [hB₁_val]
    nlinarith [hM_val, hN_val]
  nlinarith [h4sum]

have hMN_diff : N - M = s := by
  have h4diff : 4 * (N - M) = 4 * s := by
    nlinarith [hM_val, hN_val]
  nlinarith [h4diff]

have hMN_cop : Int.gcd M N = 1 := by
  by_contra hbad

  -- `Int.gcd M N` is a natural number. Since `M,N > 0`, it is positive;
  -- if it is not `1`, it has a prime divisor.
  have hgpos : 0 < Int.gcd M N := by
    exact Int.gcd_pos_of_pos_left N hMpos
  have hg_ne_zero : Int.gcd M N ≠ 0 := by omega
  have hg_gt_one : 1 < Int.gcd M N := by omega
  obtain ⟨p, hp_prime, hp_dvd_g⟩ :=
    Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)

  have hp_pos_nat : 0 < p := hp_prime.pos
  have hpz_ne_zero : (p : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hp_pos_nat)

  have hpz_not_unit : ¬ (p : ℤ) ∣ (1 : ℤ) := by
    intro hp1
    have hp1_nat : p ∣ (1 : ℕ) := by
      exact_mod_cast hp1
    exact hp_prime.not_dvd_one hp1_nat

  have hp_dvd_g_int : (p : ℤ) ∣ (Int.gcd M N : ℤ) := by
    exact_mod_cast hp_dvd_g

  have hpM : (p : ℤ) ∣ M := by
    exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_left M N)

  have hpN : (p : ℤ) ∣ N := by
    exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_right M N)

  have hp_sum : (p : ℤ) ∣ (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
    have hs : (p : ℤ) ∣ M + N := dvd_add hpM hpN
    simpa [hMN_sum] using hs

  have hp_s : (p : ℤ) ∣ s := by
    have hd : (p : ℤ) ∣ N - M := dvd_sub hpN hpM
    simpa [hMN_diff] using hd

  -- Because p divides both M and N, p^2 divides M*N.
  have hp2_MN : ((p : ℤ) ^ 2) ∣ M * N := by
    simpa [pow_two] using mul_dvd_mul hpM hpN

  have hp2_rhs : ((p : ℤ) ^ 2) ∣ 5 * B₁ ^ 4 := by
    simpa [hMN_prod] using hp2_MN

  by_cases hpB₁ : (p : ℤ) ∣ B₁

  · -- If p divides B₁, then p divides r², hence p divides r; also p divides 4k.
    have hp_B₁_sq : (p : ℤ) ∣ B₁ ^ 2 := by
      exact pow_dvd_pow_of_dvd hpB₁ 2

    have hp_2B₁_sq : (p : ℤ) ∣ 2 * B₁ ^ 2 := by
      exact dvd_mul_of_dvd_right hp_B₁_sq 2

    have hp_r_sq : (p : ℤ) ∣ (2 * j + 1) ^ 2 := by
      have h := dvd_sub hp_sum hp_2B₁_sq
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

    have hpz_prime : Prime (p : ℤ) := by
      -- If this exact bridge fails in your Mathlib snapshot, use the same
      -- Nat-prime-to-Int-prime bridge from your old `UV_coprime` proof.
      exact_mod_cast hp_prime

    have hp_r : (p : ℤ) ∣ 2 * j + 1 := by
      exact hpz_prime.dvd_of_dvd_pow hp_r_sq

    have hp_4k : (p : ℤ) ∣ 4 * k := by
      have h2B₁ : (p : ℤ) ∣ 2 * B₁ := dvd_mul_of_dvd_right hpB₁ 2
      rw [hB₁_val] at h2B₁
      simpa [mul_assoc, mul_comm, mul_left_comm] using h2B₁

    have hp_gcd : (p : ℤ) ∣ (Int.gcd (2 * j + 1) (4 * k) : ℤ) := by
      exact Int.dvd_gcd hp_r hp_4k

    have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcop] using hp_gcd

    exact hpz_not_unit hp_one

  · -- If p does not divide B₁, the square divisibility in `5 * B₁^4` is impossible.
    have hpz_prime : Prime (p : ℤ) := by
      -- Same bridge as above.
      exact_mod_cast hp_prime

    -- First copy of p: from p² | 5*B₁⁴, p | 5*B₁⁴, hence p | 5 or p | B₁.
    have hp_rhs_once : (p : ℤ) ∣ 5 * B₁ ^ 4 := by
      exact dvd_trans (by exact ⟨(p : ℤ), by ring⟩) hp2_rhs

    have hp_dvd_five_or_B₁ : (p : ℤ) ∣ (5 : ℤ) ∨ (p : ℤ) ∣ B₁ := by
      have h_or : (p : ℤ) ∣ (5 : ℤ) ∨ (p : ℤ) ∣ B₁ ^ 4 := by
        exact hpz_prime.dvd_mul.mp hp_rhs_once
      rcases h_or with h5 | hB4
      · exact Or.inl h5
      · exact Or.inr (hpz_prime.dvd_of_dvd_pow hB4)

    have hp_dvd_five : (p : ℤ) ∣ (5 : ℤ) := by
      rcases hp_dvd_five_or_B₁ with h5 | hB
      · exact h5
      · exact False.elim (hpB₁ hB)

    have hp_eq_five : p = 5 := by
      -- `p` is a positive natural prime and its integer cast divides 5.
      have hp_nat_dvd_five : p ∣ 5 := by
        exact_mod_cast hp_dvd_five
      exact (Nat.dvd_prime Nat.prime_five).1 hp_nat_dvd_five hp_prime

    -- Second copy of 5: 25 | 5*B₁⁴ implies 5 | B₁⁴, hence 5 | B₁.
    have h25_rhs : (25 : ℤ) ∣ 5 * B₁ ^ 4 := by
      simpa [hp_eq_five, pow_two] using hp2_rhs

    have h5_dvd_B₁4 : (5 : ℤ) ∣ B₁ ^ 4 := by
      rcases h25_rhs with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      nlinarith

    have h5_prime_int : Prime (5 : ℤ) := by norm_num

    have h5_dvd_B₁ : (5 : ℤ) ∣ B₁ := by
      exact h5_prime_int.dvd_of_dvd_pow h5_dvd_B₁4

    have hp_dvd_B₁ : (p : ℤ) ∣ B₁ := by
      simpa [hp_eq_five] using h5_dvd_B₁

    exact hpB₁ hp_dvd_B₁
```

Two practical notes:

1. The two identities `hMN_sum` and `hMN_diff` are the right place to use `nlinarith`; after that, the gcd proof should be divisibility-only.
2. If your Mathlib build does not accept the bridge

```lean
have hpz_prime : Prime (p : ℤ) := by
  exact_mod_cast hp_prime
```

replace the two occurrences with the local lemma you likely already used in `UV_coprime` to turn a `Nat.Prime p` into `Prime (p : ℤ)`. The rest of the proof is independent of the name of that bridge lemma.
