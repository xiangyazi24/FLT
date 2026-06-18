import Mathlib

private lemma ip2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

-- C_2: 2w² = 4t⁴+2t²s²-s⁴. Descent: (s,t,w) → (s/2, t/2, w/4).
theorem selmer_d2_trivial : ∀ s t w : ℤ,
    2 * w ^ 2 = 4 * t ^ 4 + 2 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      2 * w ^ 2 = 4 * t ^ 4 + 2 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by
    intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero =>
    intro s t w hle _
    exact ⟨Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega),
           Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    -- 2|s
    have h2s4 : (2 : ℤ) ∣ s ^ 4 :=
      ⟨2 * t ^ 4 + t ^ 2 * s ^ 2 - w ^ 2, by linarith⟩
    have h2s := ip2.dvd_of_dvd_pow h2s4
    obtain ⟨s', rfl⟩ := h2s
    -- 2|w
    have h2w2 : (2 : ℤ) ∣ w ^ 2 :=
      ⟨t ^ 4 + 2 * t ^ 2 * s' ^ 2 - 4 * s' ^ 4, by nlinarith⟩
    have h2w := ip2.dvd_of_dvd_pow h2w2
    obtain ⟨w₁, rfl⟩ := h2w
    -- 2|t
    have h2t4 : (2 : ℤ) ∣ t ^ 4 :=
      ⟨w₁ ^ 2 - t ^ 2 * s' ^ 2 + 2 * s' ^ 4, by nlinarith⟩
    have h2t := ip2.dvd_of_dvd_pow h2t4
    obtain ⟨t', rfl⟩ := h2t
    -- 2|w₁
    have h2w12 : (2 : ℤ) ∣ w₁ ^ 2 :=
      ⟨4 * t' ^ 4 + 2 * t' ^ 2 * s' ^ 2 - s' ^ 4, by nlinarith⟩
    have h2w1 := ip2.dvd_of_dvd_pow h2w12
    obtain ⟨w', rfl⟩ := h2w1
    -- Same equation
    have h' : 2 * w' ^ 2 = 4 * t' ^ 4 + 2 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl] at hle
      omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

