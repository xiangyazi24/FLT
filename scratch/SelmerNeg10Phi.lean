import Mathlib

private lemma ip5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

private lemma dvd5_of_dvd5_mul2 {x : ℤ} (h : (5 : ℤ) ∣ 2 * x) : (5 : ℤ) ∣ x := by
  rcases ip5.dvd_or_dvd h with h | h
  · exfalso; revert h; decide
  · exact h

private lemma dvd5_of_dvd5_mul4 {x : ℤ} (h : (5 : ℤ) ∣ 4 * x) : (5 : ℤ) ∣ x := by
  rcases ip5.dvd_or_dvd h with h | h
  · exfalso; revert h; decide
  · exact h

theorem selmer_neg10_phi_trivial : ∀ s t w : ℤ,
    -(10 * w ^ 2) = 100 * t ^ 4 - 10 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      -(10 * w ^ 2) = 100 * t ^ 4 - 10 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero => intro s t w hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    have h5s4 : (5 : ℤ) ∣ s ^ 4 :=
      ⟨20 * t ^ 4 - 2 * t ^ 2 * s ^ 2 + 2 * w ^ 2, by linarith⟩
    obtain ⟨s', rfl⟩ := (ip5.dvd_of_dvd_pow h5s4)
    have h5w2 : (5 : ℤ) ∣ w ^ 2 := by
      apply dvd5_of_dvd5_mul2
      exact ⟨-4 * t ^ 4 + 10 * t ^ 2 * s' ^ 2 + 25 * s' ^ 4, by nlinarith⟩
    obtain ⟨w₁, rfl⟩ := (ip5.dvd_of_dvd_pow h5w2)
    have h5t4 : (5 : ℤ) ∣ t ^ 4 := by
      apply dvd5_of_dvd5_mul4
      exact ⟨-2 * w₁ ^ 2 + 2 * t ^ 2 * s' ^ 2 + 5 * s' ^ 4, by nlinarith⟩
    obtain ⟨t', rfl⟩ := (ip5.dvd_of_dvd_pow h5t4)
    have h5w12 : (5 : ℤ) ∣ w₁ ^ 2 := by
      apply dvd5_of_dvd5_mul2
      exact ⟨-100 * t' ^ 4 + 10 * t' ^ 2 * s' ^ 2 + s' ^ 4, by nlinarith⟩
    obtain ⟨w', rfl⟩ := (ip5.dvd_of_dvd_pow h5w12)
    have h' : -(10 * w' ^ 2) = 100 * t' ^ 4 - 10 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (5 : ℤ).natAbs = 5 from rfl] at hle; omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

