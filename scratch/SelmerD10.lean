import Mathlib

private lemma ip5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)

-- C_{10}: 10w² = 100t⁴+10t²s²-s⁴. 5-adic descent.
theorem selmer_d10_trivial : ∀ s t w : ℤ,
    10 * w ^ 2 = 100 * t ^ 4 + 10 * t ^ 2 * s ^ 2 - s ^ 4 → s = 0 ∧ t = 0 ∧ w = 0 := by
  suffices ∀ n : ℕ, ∀ s t w : ℤ, s.natAbs + t.natAbs + w.natAbs ≤ n →
      10 * w ^ 2 = 100 * t ^ 4 + 10 * t ^ 2 * s ^ 2 - s ^ 4 →
      s = 0 ∧ t = 0 ∧ w = 0 by intro s t w h; exact this _ s t w le_rfl h
  intro n; induction n with
  | zero => intro s t w hle _; exact ⟨Int.natAbs_eq_zero.mp (by omega),
      Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
  | succ n ih =>
    intro s t w hle h
    -- s⁴ = 100t⁴+10t²s²-10w² = 5(20t⁴+2t²s²-2w²)... hmm, need 5|s⁴
    -- Actually: s⁴ = 100t⁴+10t²s²-10w². Is this divisible by 5?
    -- 100t⁴ ≡ 0, 10t²s² ≡ 0, 10w² ≡ 0 mod 5. So s⁴ ≡ 0 mod 5. ✓
    have h5s4 : (5 : ℤ) ∣ s ^ 4 := ⟨20 * t ^ 4 + 2 * t ^ 2 * s ^ 2 - 2 * w ^ 2, by linarith⟩
    obtain ⟨s', rfl⟩ := (ip5.dvd_of_dvd_pow h5s4)
    -- After s=5s': 10w² = 100t⁴+250t²s'²-625s'⁴. w² = 5(2t⁴+5t²s'²-... let me compute)
    -- 10w² = 100t⁴+250t²s'²-625s'⁴
    -- 2w² = 20t⁴+50t²s'²-125s'⁴ = 5(4t⁴+10t²s'²-25s'⁴)
    -- w² = 5(4t⁴+10t²s'²-25s'⁴)/2... hmm this doesn't give integer.
    -- Wait: 2w² = 5(4t⁴+10t²s'²-25s'⁴), so 5|2w². Since gcd(2,5)=1, 5|w².
    have h5w2 : (5 : ℤ) ∣ w ^ 2 := by
      have h2w2 : 2 * w ^ 2 = 5 * (4 * t ^ 4 + 10 * t ^ 2 * s' ^ 2 - 25 * s' ^ 4) := by nlinarith
      have : (5 : ℤ) ∣ 2 * w ^ 2 := ⟨4 * t ^ 4 + 10 * t ^ 2 * s' ^ 2 - 25 * s' ^ 4, by linarith [h2w2]⟩
      exact (ip5.dvd_or_dvd this).resolve_left (by norm_num)
    obtain ⟨w₁, rfl⟩ := (ip5.dvd_of_dvd_pow h5w2)
    -- After w=5w₁: 10·25w₁² = 100t⁴+250t²s'²-625s'⁴
    -- 250w₁² = 100t⁴+250t²s'²-625s'⁴
    -- 10w₁² = 4t⁴+10t²s'²-25s'⁴
    -- t⁴ = (10w₁²-10t²s'²+25s'⁴)/4... need 5|t⁴ differently
    -- Actually: 4t⁴ = 10w₁²-10t²s'²+25s'⁴ = 5(2w₁²-2t²s'²+5s'⁴)
    -- 5|4t⁴. Since gcd(4,5)=1, 5|t⁴.
    have h5t4 : (5 : ℤ) ∣ t ^ 4 := by
      have h4t4 : 4 * t ^ 4 = 5 * (2 * w₁ ^ 2 - 2 * t ^ 2 * s' ^ 2 + 5 * s' ^ 4) := by nlinarith
      have : (5 : ℤ) ∣ 4 * t ^ 4 := ⟨2 * w₁ ^ 2 - 2 * t ^ 2 * s' ^ 2 + 5 * s' ^ 4, by linarith [h4t4]⟩
      exact (ip5.dvd_or_dvd this).resolve_left (by norm_num)
    obtain ⟨t', rfl⟩ := (ip5.dvd_of_dvd_pow h5t4)
    -- After t=5t': 10w₁² = 4·625t'⁴+10·25t'²s'²-25s'⁴ = 2500t'⁴+250t'²s'²-25s'⁴
    -- 2w₁² = 500t'⁴+50t'²s'²-5s'⁴ = 5(100t'⁴+10t'²s'²-s'⁴)
    -- 5|2w₁². Since gcd(2,5)=1, 5|w₁².
    have h5w12 : (5 : ℤ) ∣ w₁ ^ 2 := by
      have h2w12 : 2 * w₁ ^ 2 = 5 * (100 * t' ^ 4 + 10 * t' ^ 2 * s' ^ 2 - s' ^ 4) := by nlinarith
      have : (5 : ℤ) ∣ 2 * w₁ ^ 2 := ⟨100 * t' ^ 4 + 10 * t' ^ 2 * s' ^ 2 - s' ^ 4, by linarith [h2w12]⟩
      exact (ip5.dvd_or_dvd this).resolve_left (by norm_num)
    obtain ⟨w', rfl⟩ := (ip5.dvd_of_dvd_pow h5w12)
    have h' : 10 * w' ^ 2 = 100 * t' ^ 4 + 10 * t' ^ 2 * s' ^ 2 - s' ^ 4 := by nlinarith
    have hle' : s'.natAbs + t'.natAbs + w'.natAbs ≤ n := by
      simp only [Int.natAbs_mul, show (5 : ℤ).natAbs = 5 from rfl] at hle; omega
    obtain ⟨hs', ht', hw'⟩ := ih s' t' w' hle' h'
    exact ⟨by simp [hs'], by simp [ht'], by simp [hw']⟩

