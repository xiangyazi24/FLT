import Mathlib

private lemma ip2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
private lemma ip5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

theorem selmer_neg2_trivial : ∀ s t w : ℤ,
    -(2 * w ^ 2) = 4 * t ^ 4 - 2 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      -(2 * w ^ 2) = 4 * t ^ 4 - 2 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero => intro s t w hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    -- s⁴ = 2(2t⁴-t²s²+w²)
    have h2s4 : (2 : ℤ) ∣ s ^ 4 := ⟨2 * t ^ 4 - t ^ 2 * s ^ 2 + w ^ 2, by linarith⟩
    obtain ⟨s', rfl⟩ := (ip2.dvd_of_dvd_pow h2s4)
    -- w² = 2(-t⁴+2t²s'²+4s'⁴)
    have h2w2 : (2 : ℤ) ∣ w ^ 2 :=
      ⟨-t ^ 4 + 2 * t ^ 2 * s' ^ 2 + 4 * s' ^ 4, by nlinarith⟩
    obtain ⟨w₁, rfl⟩ := (ip2.dvd_of_dvd_pow h2w2)
    -- t⁴ = 2(t²s'²+2s'⁴-w₁²)
    have h2t4 : (2 : ℤ) ∣ t ^ 4 :=
      ⟨t ^ 2 * s' ^ 2 + 2 * s' ^ 4 - w₁ ^ 2, by nlinarith⟩
    obtain ⟨t', rfl⟩ := (ip2.dvd_of_dvd_pow h2t4)
    -- w₁² = 2(-4t'⁴+2t'²s'²+s'⁴)
    have h2w12 : (2 : ℤ) ∣ w₁ ^ 2 :=
      ⟨-4 * t' ^ 4 + 2 * t' ^ 2 * s' ^ 2 + s' ^ 4, by nlinarith⟩
    obtain ⟨w', rfl⟩ := (ip2.dvd_of_dvd_pow h2w12)
    have h' : -(2 * w' ^ 2) = 4 * t' ^ 4 - 2 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl] at hle; omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

theorem selmer_neg5_trivial : ∀ s t w : ℤ,
    -(5 * w ^ 2) = 25 * t ^ 4 - 5 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      -(5 * w ^ 2) = 25 * t ^ 4 - 5 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero => intro s t w hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    -- s⁴ = 5(5t⁴-t²s²+w²)
    have h5s4 : (5 : ℤ) ∣ s ^ 4 := ⟨5 * t ^ 4 - t ^ 2 * s ^ 2 + w ^ 2, by linarith⟩
    obtain ⟨s', rfl⟩ := (ip5.dvd_of_dvd_pow h5s4)
    -- w² = 5(-t⁴+5t²s'²+25s'⁴)
    have h5w2 : (5 : ℤ) ∣ w ^ 2 :=
      ⟨-t ^ 4 + 5 * t ^ 2 * s' ^ 2 + 25 * s' ^ 4, by nlinarith⟩
    obtain ⟨w₁, rfl⟩ := (ip5.dvd_of_dvd_pow h5w2)
    -- t⁴ = 5(t²s'²+5s'⁴-w₁²)
    have h5t4 : (5 : ℤ) ∣ t ^ 4 :=
      ⟨t ^ 2 * s' ^ 2 + 5 * s' ^ 4 - w₁ ^ 2, by nlinarith⟩
    obtain ⟨t', rfl⟩ := (ip5.dvd_of_dvd_pow h5t4)
    -- w₁² = 5(-25t'⁴+5t'²s'²+s'⁴)
    have h5w12 : (5 : ℤ) ∣ w₁ ^ 2 :=
      ⟨-25 * t' ^ 4 + 5 * t' ^ 2 * s' ^ 2 + s' ^ 4, by nlinarith⟩
    obtain ⟨w', rfl⟩ := (ip5.dvd_of_dvd_pow h5w12)
    have h' : -(5 * w' ^ 2) = 25 * t' ^ 4 - 5 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (5 : ℤ).natAbs = 5 from rfl] at hle; omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

