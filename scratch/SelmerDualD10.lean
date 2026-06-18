import Mathlib

private lemma ip2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

private lemma dvd2_of_dvd2_mul5 {x : ℤ} (h : (2 : ℤ) ∣ 5 * x) : (2 : ℤ) ∣ x := by
  rcases ip2.dvd_or_dvd h with h | h
  · exfalso; revert h; decide
  · exact h

theorem dual_selmer_d10_trivial : ∀ S T W : ℤ,
    10 * W ^ 2 = 100 * T ^ 4 - 20 * T ^ 2 * S ^ 2 + 5 * S ^ 4 → S = 0 ∧ T = 0 ∧ W = 0 := by
  suffices ∀ n : ℕ, ∀ S T W : ℤ, S.natAbs + T.natAbs + W.natAbs ≤ n →
      10 * W ^ 2 = 100 * T ^ 4 - 20 * T ^ 2 * S ^ 2 + 5 * S ^ 4 →
      S = 0 ∧ T = 0 ∧ W = 0 by intro S T W h; exact this _ S T W le_rfl h
  intro n; induction n with
  | zero => intro S T W hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro S T W hle h
    -- 2|S⁴ (from 2W²=20T⁴-4T²S²+S⁴, S⁴ = 2(W²-10T⁴+2T²S²))
    have h2S4 : (2 : ℤ) ∣ S ^ 4 :=
      ⟨W ^ 2 - 10 * T ^ 4 + 2 * T ^ 2 * S ^ 2, by linarith⟩
    obtain ⟨S', rfl⟩ := (ip2.dvd_of_dvd_pow h2S4)
    -- 2|W² (W² = 2(5T⁴-4T²S'²+4S'⁴))
    have h2W2 : (2 : ℤ) ∣ W ^ 2 :=
      ⟨5 * T ^ 4 - 4 * T ^ 2 * S' ^ 2 + 4 * S' ^ 4, by nlinarith⟩
    obtain ⟨W₁, rfl⟩ := (ip2.dvd_of_dvd_pow h2W2)
    -- 2|T⁴ (from 5T⁴ = 2(W₁²+2T²S'²-2S'⁴), so 2|5T⁴, gcd(2,5)=1 → 2|T⁴)
    have h2T4 : (2 : ℤ) ∣ T ^ 4 := by
      apply dvd2_of_dvd2_mul5
      exact ⟨W₁ ^ 2 + 2 * T ^ 2 * S' ^ 2 - 2 * S' ^ 4, by nlinarith⟩
    obtain ⟨T', rfl⟩ := (ip2.dvd_of_dvd_pow h2T4)
    -- 2|W₁² (W₁² = 2(20T'⁴-4T'²S'²+S'⁴))
    have h2W12 : (2 : ℤ) ∣ W₁ ^ 2 :=
      ⟨20 * T' ^ 4 - 4 * T' ^ 2 * S' ^ 2 + S' ^ 4, by nlinarith⟩
    obtain ⟨W', rfl⟩ := (ip2.dvd_of_dvd_pow h2W12)
    have h' : 10 * W' ^ 2 = 100 * T' ^ 4 - 20 * T' ^ 2 * S' ^ 2 + 5 * S' ^ 4 := by nlinarith
    have hle' : S'.natAbs + T'.natAbs + W'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl] at hle; omega
    obtain ⟨hS', hT', hW'⟩ := ih S' T' W' hle' h'
    exact ⟨by simp [hS'], by simp [hT'], by simp [hW']⟩

