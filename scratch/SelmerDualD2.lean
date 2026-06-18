import Mathlib

private lemma ip2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

-- C'_2 for φ̂: 2W²=4T⁴-4T²S²+5S⁴. 2-adic descent.
theorem dual_selmer_d2_trivial : ∀ S T W : ℤ,
    2 * W ^ 2 = 4 * T ^ 4 - 4 * T ^ 2 * S ^ 2 + 5 * S ^ 4 → S = 0 ∧ T = 0 ∧ W = 0 := by
  suffices ∀ n : ℕ, ∀ S T W : ℤ, S.natAbs + T.natAbs + W.natAbs ≤ n →
      2 * W ^ 2 = 4 * T ^ 4 - 4 * T ^ 2 * S ^ 2 + 5 * S ^ 4 →
      S = 0 ∧ T = 0 ∧ W = 0 by intro S T W h; exact this _ S T W le_rfl h
  intro n; induction n with
  | zero => intro S T W hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro S T W hle h
    -- 2|S⁴ (S⁴ = 4T⁴-4T²S²+5S⁴-2W²+S⁴-5S⁴... let me get the right witness)
    -- From h: 2W² = 4T⁴-4T²S²+5S⁴. So 5S⁴ = 2W²-4T⁴+4T²S².
    -- S⁴ = (2W²-4T⁴+4T²S²)/5... not integer necessarily.
    -- Better: mod 2: 0 = 0-0+S⁴ mod 2 (since 4T⁴ ≡ 0, 4T²S² ≡ 0, 5S⁴ ≡ S⁴)
    -- So S⁴ ≡ 0 mod 2, hence 2|S⁴.
    have h2S4 : (2 : ℤ) ∣ S ^ 4 :=
      ⟨W ^ 2 - 2 * T ^ 4 + 2 * T ^ 2 * S ^ 2 - 2 * S ^ 4, by linarith⟩
    obtain ⟨S', rfl⟩ := (ip2.dvd_of_dvd_pow h2S4)
    -- W² = 2(T⁴-4T²S'²+20S'⁴)
    have h2W2 : (2 : ℤ) ∣ W ^ 2 :=
      ⟨T ^ 4 - 4 * T ^ 2 * S' ^ 2 + 20 * S' ^ 4, by nlinarith⟩
    obtain ⟨W₁, rfl⟩ := (ip2.dvd_of_dvd_pow h2W2)
    -- T⁴ = 2(W₁²+2T²S'²-10S'⁴)... let me compute:
    -- 2W₁² = T⁴-4T²S'²+20S'⁴. So T⁴ = 2W₁²+4T²S'²-20S'⁴ = 2(W₁²+2T²S'²-10S'⁴)
    have h2T4 : (2 : ℤ) ∣ T ^ 4 :=
      ⟨W₁ ^ 2 + 2 * T ^ 2 * S' ^ 2 - 10 * S' ^ 4, by nlinarith⟩
    obtain ⟨T', rfl⟩ := (ip2.dvd_of_dvd_pow h2T4)
    -- W₁² = 2(4T'⁴-4T'²S'²+5S'⁴)... compute:
    -- After T=2T': 2W₁² = 16T'⁴-16T'²S'²+20S'⁴. W₁² = 8T'⁴-8T'²S'²+10S'⁴ = 2(4T'⁴-4T'²S'²+5S'⁴)
    have h2W12 : (2 : ℤ) ∣ W₁ ^ 2 :=
      ⟨4 * T' ^ 4 - 4 * T' ^ 2 * S' ^ 2 + 5 * S' ^ 4, by nlinarith⟩
    obtain ⟨W', rfl⟩ := (ip2.dvd_of_dvd_pow h2W12)
    have h' : 2 * W' ^ 2 = 4 * T' ^ 4 - 4 * T' ^ 2 * S' ^ 2 + 5 * S' ^ 4 := by nlinarith
    have hle' : S'.natAbs + T'.natAbs + W'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl] at hle; omega
    obtain ⟨hS', hT', hW'⟩ := ih S' T' W' hle' h'
    exact ⟨by simp [hS'], by simp [hT'], by simp [hW']⟩

