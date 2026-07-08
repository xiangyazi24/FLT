import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Arithmetic antichain for the cyclic order reduction
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def minimalBadComposites : Finset ℕ :=
  {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}

def smallPrimes : Finset ℕ := {2, 3, 5, 7}

def IsSmooth (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ smallPrimes

private theorem smooth_of_dvd {n m : ℕ} (hsmooth : IsSmooth n) (hm : m ∣ n) :
    IsSmooth m := fun p hp hpm => hsmooth p hp (dvd_trans hpm hm)

private theorem eq_one_of_smooth_no_small_prime {m : ℕ} (hm : 0 < m)
    (hsmooth : IsSmooth m)
    (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) (h5 : ¬ 5 ∣ m) (h7 : ¬ 7 ∣ m) : m = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have := hsmooth p hp hpm
  simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl <;> contradiction

theorem exists_minimalBadComposite_dvd {n : ℕ}
    (hn : 12 < n) (hsmooth : IsSmooth n) :
    ∃ d ∈ minimalBadComposites, d ∣ n := by
  by_contra hall
  push_neg at hall
  have hndvd : ∀ d ∈ minimalBadComposites, ¬ d ∣ n := hall
  have h14 : ¬ 14 ∣ n := hndvd 14 (by decide)
  have h15 : ¬ 15 ∣ n := hndvd 15 (by decide)
  have h16 : ¬ 16 ∣ n := hndvd 16 (by decide)
  have h18 : ¬ 18 ∣ n := hndvd 18 (by decide)
  have h20 : ¬ 20 ∣ n := hndvd 20 (by decide)
  have h21 : ¬ 21 ∣ n := hndvd 21 (by decide)
  have h24 : ¬ 24 ∣ n := hndvd 24 (by decide)
  have h25 : ¬ 25 ∣ n := hndvd 25 (by decide)
  have h27 : ¬ 27 ∣ n := hndvd 27 (by decide)
  have h35 : ¬ 35 ∣ n := hndvd 35 (by decide)
  have h49 : ¬ 49 ∣ n := hndvd 49 (by decide)
  -- Key: if a and b are coprime and both divide n, then ab divides n.
  -- 7 ∣ n ∧ 2 ∣ n → 14 ∣ n (contradiction). So 7 ∣ n → 2 ∤ n. Etc.
  -- Step 1: 7 ∣ n → contradiction (n ≤ 7 < 13)
  have h7n : ¬ 7 ∣ n := by
    intro ⟨m, hm⟩
    have h2m : ¬ 2 ∣ m := by
      intro ⟨k, hk⟩; exact h14 ⟨k, by omega⟩
    have h3m : ¬ 3 ∣ m := by
      intro ⟨k, hk⟩; exact h21 ⟨k, by omega⟩
    have h5m : ¬ 5 ∣ m := by
      intro ⟨k, hk⟩; exact h35 ⟨k, by omega⟩
    have h7m : ¬ 7 ∣ m := by
      intro ⟨k, hk⟩; exact h49 ⟨k, by omega⟩
    have hm_pos : 0 < m := by omega
    have hm_smooth : IsSmooth m := smooth_of_dvd hsmooth ⟨7, by omega⟩
    have := eq_one_of_smooth_no_small_prime hm_pos hm_smooth h2m h3m h5m h7m
    omega
  -- Step 2: 5 ∣ n → contradiction (n ≤ 10 < 13)
  have h5n : ¬ 5 ∣ n := by
    intro ⟨m, hm⟩
    have h3m : ¬ 3 ∣ m := by
      intro ⟨k, hk⟩; exact h15 ⟨k, by omega⟩
    have h5m : ¬ 5 ∣ m := by
      intro ⟨k, hk⟩; exact h25 ⟨k, by omega⟩
    have h7m : ¬ 7 ∣ m := by
      intro ⟨k, hk⟩; exact h7n ⟨5 * k, by omega⟩
    -- m has only prime factor 2. m = 2^a with a ≤ 1 (since 4|m → 20|n).
    have h4m : ¬ 4 ∣ m := by
      intro ⟨k, hk⟩; exact h20 ⟨k, by omega⟩
    -- m ≤ 2: if m ≥ 3, m has a prime factor which must be 2 (smooth, no 3,5,7),
    -- so 2|m. Then m/2 ≥ 2 has a prime factor which must be 2, so 4|m. Contradiction.
    have hm_le : m ≤ 2 := by
      by_contra hm_big
      push_neg at hm_big
      have hm_smooth : IsSmooth m := smooth_of_dvd hsmooth ⟨5, by omega⟩
      have h2m : 2 ∣ m := by
        obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
        have := hm_smooth p hp hpm
        simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact hpm
        · exact absurd hpm h3m
        · exact absurd hpm h5m
        · exact absurd hpm h7m
      -- 2|m and m ≥ 3. m = 2k with k ≥ 2.
      rcases h2m with ⟨k, hk_eq⟩
      -- k ≥ 2
      have hk_ge : k ≥ 2 := by omega
      -- k has a prime factor (k ≥ 2), which must be 2
      have hk_smooth : IsSmooth k := by
        intro p hp hpk
        exact hm_smooth p hp (dvd_trans hpk ⟨2, by omega⟩)
      obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
      have := hk_smooth q hq hqk
      simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · -- q = 2, so 4 | m
        exact h4m ⟨k / 2, by omega⟩
      · exact h3m (dvd_trans hqk ⟨2, by omega⟩)
      · exact h5m (dvd_trans hqk ⟨2, by omega⟩)
      · exact h7m (dvd_trans hqk ⟨2, by omega⟩)
    omega
  -- Step 3: 5 ∤ n, 7 ∤ n → only {2,3} factors → n ≤ 12 → contradiction
  -- Sub-case 3a: 3 ∤ n → n = 2^a, 16 ∤ n → a ≤ 3 → n ≤ 8
  -- Sub-case 3b: 3 ∣ n, 9 ∣ n → from 18 ∤ n: 2 ∤ n. So n = 3^b, 27 ∤ n → b ≤ 2 → n ≤ 9
  -- Sub-case 3c: 3 ∣ n, 9 ∤ n → n = 3k, 3 ∤ k, k = 2^a, 24 ∤ n → 8 ∤ k → a ≤ 2 → n ≤ 12
  by_cases h3n : 3 ∣ n
  · -- 3 | n
    rcases h3n with ⟨m, hm⟩
    by_cases h3m : 3 ∣ m
    · -- 9 | n. From 18 ∤ n: 2 ∤ n.
      have h2n : ¬ 2 ∣ n := by
        intro ⟨k, hk⟩; exact h18 ⟨k, by omega⟩
      -- n has only prime factor 3 (smooth, no 2, 5, 7). 27 ∤ n → 3^3 ∤ n.
      -- n = 3^b with b ≤ 2 → n ≤ 9.
      rcases h3m with ⟨k, hk_eq⟩
      -- n = 9k. 27 ∤ n → 3 ∤ k.
      have h3k : ¬ 3 ∣ k := by
        intro ⟨j, hj⟩; exact h27 ⟨j, by omega⟩
      have h2k : ¬ 2 ∣ k := by
        intro ⟨j, hj⟩; exact h2n ⟨9 * j / 2, by omega⟩
      have h5k : ¬ 5 ∣ k := by
        intro ⟨j, hj⟩; exact h5n ⟨9 * j / 5, by omega⟩
      have h7k : ¬ 7 ∣ k := by
        intro ⟨j, hj⟩; exact h7n ⟨9 * j / 7, by omega⟩
      have hk_smooth : IsSmooth k := by
        intro p hp hpk
        exact hsmooth p hp (dvd_trans hpk ⟨9, by omega⟩)
      have hk_pos : 0 < k := by omega
      have := eq_one_of_smooth_no_small_prime hk_pos hk_smooth h2k h3k h5k h7k
      omega
    · -- 3 | n but 9 ∤ n. n = 3m, 3 ∤ m.
      -- m has only prime factor 2 (smooth, no 3, 5, 7).
      have h5m : ¬ 5 ∣ m := by
        intro ⟨k, hk⟩; exact h5n ⟨3 * k / 5, by omega⟩
      have h7m : ¬ 7 ∣ m := by
        intro ⟨k, hk⟩; exact h7n ⟨3 * k / 7, by omega⟩
      -- 24 ∤ n → 8 ∤ m (since 3 * 8 = 24)
      have h8m : ¬ 8 ∣ m := by
        intro ⟨k, hk⟩; exact h24 ⟨k, by omega⟩
      -- m = 2^a with a ≤ 2 (since 8 ∤ m). So m ≤ 4. n = 3m ≤ 12.
      have hm_le : m ≤ 4 := by
        by_contra hm_big
        push_neg at hm_big
        have hm_smooth : IsSmooth m := smooth_of_dvd hsmooth ⟨3, by omega⟩
        -- m has only factor 2 (no 3, 5, 7).
        -- m ≥ 5 with only factor 2 → m ≥ 8 → 8 | m. Contradiction.
        -- Actually m could be e.g. 5 (not smooth) or 6 = 2*3 (but 3 ∤ m).
        -- So m = 2^a. m ≥ 5 → a ≥ 3 → 8 | m. Contradiction.
        have h2m : 2 ∣ m := by
          obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
          have := hm_smooth p hp hpm
          simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl | rfl | rfl
          · exact hpm
          · exact absurd hpm h3m
          · exact absurd hpm h5m
          · exact absurd hpm h7m
        rcases h2m with ⟨k, hk_eq⟩
        have hk_ge : k ≥ 3 := by omega
        have hk_smooth : IsSmooth k :=
          smooth_of_dvd hm_smooth ⟨2, by omega⟩
        have h3k : ¬ 3 ∣ k := fun ⟨j, hj⟩ => h3m ⟨2 * j, by omega⟩
        have h5k : ¬ 5 ∣ k := fun ⟨j, hj⟩ => h5m ⟨2 * j, by omega⟩
        have h7k : ¬ 7 ∣ k := fun ⟨j, hj⟩ => h7m ⟨2 * j, by omega⟩
        obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
        have := hk_smooth q hq hqk
        simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · -- q = 2, so 4|m. k ≥ 3, 2|k → k ≥ 4 → k/2 ≥ 2.
          rcases hqk with ⟨j, hj⟩
          -- m = 2 * k = 2 * (2 * j) = 4j. j ≥ 2 since k ≥ 3.
          have hj_ge : j ≥ 2 := by omega
          -- j has a prime factor which must be 2.
          have hj_smooth : IsSmooth j := smooth_of_dvd hk_smooth ⟨2, by omega⟩
          have h3j : ¬ 3 ∣ j := fun ⟨i, hi⟩ => h3k ⟨2 * i, by omega⟩
          have h5j : ¬ 5 ∣ j := fun ⟨i, hi⟩ => h5k ⟨2 * i, by omega⟩
          have h7j : ¬ 7 ∣ j := fun ⟨i, hi⟩ => h7k ⟨2 * i, by omega⟩
          obtain ⟨r, hr, hrj⟩ := Nat.exists_prime_and_dvd (by omega : j ≠ 1)
          have := hj_smooth r hr hrj
          simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl | rfl | rfl
          · -- r = 2, so 8 | m = 4j and 2|j → 8|m
            exact h8m ⟨j / 2, by omega⟩
          · exact h3j hrj
          · exact h5j hrj
          · exact h7j hrj
        · exact h3k hqk
        · exact h5k hqk
        · exact h7k hqk
      omega
  · -- 3 ∤ n. Then n has only prime factor 2 (smooth, no 3, 5, 7).
    -- 16 ∤ n → 2^4 ∤ n. So n = 2^a with a ≤ 3 → n ≤ 8.
    -- Same pattern: show m ≤ 8 using the chain.
    -- Actually: n only has factor 2. 16 ∤ n. We show n ≤ 8.
    have h2n : 2 ∣ n := by
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have := hsmooth p hp hpn
      simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact hpn
      · exact absurd hpn h3n
      · exact absurd hpn h5n
      · exact absurd hpn h7n
    rcases h2n with ⟨m, hm_eq⟩
    -- n = 2m. 16 ∤ n → 8 ∤ m.
    have h8m : ¬ 8 ∣ m := by
      intro ⟨k, hk⟩; exact h16 ⟨k, by omega⟩
    have hm_smooth : IsSmooth m := smooth_of_dvd hsmooth ⟨2, by omega⟩
    have h3m : ¬ 3 ∣ m := fun ⟨k, hk⟩ => h3n ⟨2 * k, by omega⟩
    have h5m : ¬ 5 ∣ m := fun ⟨k, hk⟩ => h5n ⟨2 * k, by omega⟩
    have h7m : ¬ 7 ∣ m := fun ⟨k, hk⟩ => h7n ⟨2 * k, by omega⟩
    -- m has only factor 2 and 8 ∤ m → m ≤ 4
    have hm_le : m ≤ 4 := by
      by_contra hm_big
      push_neg at hm_big
      have h2m : 2 ∣ m := by
        obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
        have := hm_smooth p hp hpm
        simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact hpm
        · exact absurd hpm h3m
        · exact absurd hpm h5m
        · exact absurd hpm h7m
      rcases h2m with ⟨k, hk_eq⟩
      have hk_ge : k ≥ 3 := by omega
      have hk_smooth : IsSmooth k := smooth_of_dvd hm_smooth ⟨2, by omega⟩
      have h3k : ¬ 3 ∣ k := fun ⟨j, hj⟩ => h3m ⟨2 * j, by omega⟩
      have h5k : ¬ 5 ∣ k := fun ⟨j, hj⟩ => h5m ⟨2 * j, by omega⟩
      have h7k : ¬ 7 ∣ k := fun ⟨j, hj⟩ => h7m ⟨2 * j, by omega⟩
      obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
      have := hk_smooth q hq hqk
      simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · rcases hqk with ⟨j, hj⟩
        have hj_ge : j ≥ 2 := by omega
        have hj_smooth : IsSmooth j := smooth_of_dvd hk_smooth ⟨2, by omega⟩
        have h3j : ¬ 3 ∣ j := fun ⟨i, hi⟩ => h3k ⟨2 * i, by omega⟩
        have h5j : ¬ 5 ∣ j := fun ⟨i, hi⟩ => h5k ⟨2 * i, by omega⟩
        have h7j : ¬ 7 ∣ j := fun ⟨i, hi⟩ => h7k ⟨2 * i, by omega⟩
        obtain ⟨r, hr, hrj⟩ := Nat.exists_prime_and_dvd (by omega : j ≠ 1)
        have := hj_smooth r hr hrj
        simp [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact h8m ⟨j / 2, by omega⟩
        · exact h3j hrj
        · exact h5j hrj
        · exact h7j hrj
      · exact h3k hqk
      · exact h5k hqk
      · exact h7k hqk
    omega

theorem hasRationalPointOfOrder_of_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n d : ℕ}
    (hn : n ≠ 0) (hdn : d ∣ n)
    (hord : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E d := by
  rcases hord with ⟨P, hP⟩
  have hd : d ≠ 0 := by
    intro h; rw [h] at hdn; exact hn (Nat.eq_zero_of_zero_dvd hdn)
  refine ⟨(n / d) • P, ?_⟩
  have hnd_ne : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn)
    (Nat.pos_of_ne_zero hd)).ne'
  rw [addOrderOf_nsmul' P hnd_ne, hP]
  rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdn)]
  exact Nat.div_div_self hdn hn

end MazurProof
