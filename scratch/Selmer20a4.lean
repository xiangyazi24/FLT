import Mathlib

private lemma ip5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

theorem selmer_d5_trivial : ∀ s t w : ℤ,
    5 * w ^ 2 = 25 * t ^ 4 + 5 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      5 * w ^ 2 = 25 * t ^ 4 + 5 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by
    intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero =>
    intro s t w hle _
    exact ⟨Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega),
           Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    -- Step 1: 5|s
    have h5s4 : (5 : ℤ) ∣ s ^ 4 :=
      ⟨5 * t ^ 4 + t ^ 2 * s ^ 2 - w ^ 2, by linarith⟩
    have h5s := ip5.dvd_of_dvd_pow h5s4
    obtain ⟨s', rfl⟩ := h5s
    -- Step 2: 5|w
    have h5w2 : (5 : ℤ) ∣ w ^ 2 :=
      ⟨t ^ 4 + 5 * t ^ 2 * s' ^ 2 - 25 * s' ^ 4, by nlinarith⟩
    have h5w := ip5.dvd_of_dvd_pow h5w2
    obtain ⟨w₁, rfl⟩ := h5w
    -- Step 3: 5|t
    have h5t4 : (5 : ℤ) ∣ t ^ 4 :=
      ⟨w₁ ^ 2 - t ^ 2 * s' ^ 2 + 5 * s' ^ 4, by nlinarith⟩
    have h5t := ip5.dvd_of_dvd_pow h5t4
    obtain ⟨t', rfl⟩ := h5t
    -- Step 4: 5|w₁
    have h5w12 : (5 : ℤ) ∣ w₁ ^ 2 :=
      ⟨25 * t' ^ 4 + 5 * t' ^ 2 * s' ^ 2 - s' ^ 4, by nlinarith⟩
    have h5w1 := ip5.dvd_of_dvd_pow h5w12
    obtain ⟨w', rfl⟩ := h5w1
    -- Same equation for (s', t', w')
    have h' : 5 * w' ^ 2 = 25 * t' ^ 4 + 5 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    -- Measure decreases
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (5 : ℤ).natAbs = 5 from rfl] at hle
      omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

