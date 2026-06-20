import scratch.Ljunggren14

set_option maxHeartbeats 1200000

theorem no_sq_at_0_1_4 (A B C D : ℤ)
    (h1 : B ^ 2 = A ^ 2 + D ^ 2)
    (h2 : C ^ 2 = A ^ 2 + 4 * D ^ 2) :
    A * D = 0 := by
  by_contra hAD
  have hA : A ≠ 0 := by
    intro hA0
    apply hAD
    rw [hA0]
    ring
  have hD : D ≠ 0 := by
    intro hD0
    apply hAD
    rw [hD0]
    ring
  have htrip : PythagoreanTriple A D B := by
    unfold PythagoreanTriple
    nlinarith [h1]
  obtain ⟨k, r, s, hcase, _hB⟩ := PythagoreanTriple.classification.mp htrip
  rcases hcase with hcase | hcase
  · rcases hcase with ⟨hAkr, hDkrs⟩
    have hk : k ≠ 0 := by
      intro hk0
      apply hA
      rw [hAkr, hk0]
      ring
    have hr : r ≠ 0 := by
      intro hr0
      apply hD
      rw [hDkrs, hr0]
      ring
    have hs : s ≠ 0 := by
      intro hs0
      apply hD
      rw [hDkrs, hs0]
      ring
    have hrsq : r ^ 2 ≠ s ^ 2 := by
      intro hrs
      apply hA
      rw [hAkr]
      rw [hrs]
      ring
    have hCeq : C ^ 2 = k ^ 2 * (r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4) := by
      rw [h2, hAkr, hDkrs]
      ring
    have hk_dvd_C : k ∣ C := by
      have hpow : k ^ 2 ∣ C ^ 2 := by
        rw [hCeq]
        exact dvd_mul_right (k ^ 2) (r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4)
      exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
    rcases hk_dvd_C with ⟨Z, hCZ⟩
    have hZeq : r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4 = Z ^ 2 := by
      rw [hCZ] at hCeq
      have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
      have hcancel :
          Z ^ 2 * k ^ 2 =
            (r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4) * k ^ 2 := by
        calc
          Z ^ 2 * k ^ 2 = (k * Z) ^ 2 := by ring
          _ = k ^ 2 * (r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4) := hCeq
          _ = (r ^ 4 + 14 * r ^ 2 * s ^ 2 + s ^ 4) * k ^ 2 := by ring
      exact ((mul_left_inj' hk2).mp hcancel).symm
    exact not_ljunggren_14 (x := r) (y := s) (z := Z) hr hs hrsq hZeq
  · rcases hcase with ⟨hAkrs, hDkr⟩
    have hk : k ≠ 0 := by
      intro hk0
      apply hD
      rw [hDkr, hk0]
      ring
    have hr : r ≠ 0 := by
      intro hr0
      apply hA
      rw [hAkrs, hr0]
      ring
    have hs : s ≠ 0 := by
      intro hs0
      apply hA
      rw [hAkrs, hs0]
      ring
    have hrsq : r ^ 2 ≠ s ^ 2 := by
      intro hrs
      apply hD
      rw [hDkr]
      rw [hrs]
      ring
    have hCeq : C ^ 2 = (2 * k) ^ 2 * (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) := by
      rw [h2, hAkrs, hDkr]
      ring
    have h2k_ne : 2 * k ≠ 0 := mul_ne_zero (by norm_num) hk
    have h2k_dvd_C : 2 * k ∣ C := by
      have hpow : (2 * k) ^ 2 ∣ C ^ 2 := by
        rw [hCeq]
        exact dvd_mul_right ((2 * k) ^ 2) (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4)
      exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
    rcases h2k_dvd_C with ⟨H, hCH⟩
    have hHeq : H ^ 2 = r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4 := by
      rw [hCH] at hCeq
      have h2k2 : (2 * k) ^ 2 ≠ 0 := pow_ne_zero 2 h2k_ne
      have hcancel :
          H ^ 2 * (2 * k) ^ 2 =
            (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) * (2 * k) ^ 2 := by
        calc
          H ^ 2 * (2 * k) ^ 2 = (2 * k * H) ^ 2 := by ring
          _ = (2 * k) ^ 2 * (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) := hCeq
          _ = (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) * (2 * k) ^ 2 := by ring
      exact (mul_left_inj' h2k2).mp hcancel
    let X : ℤ := r + s
    let Y : ℤ := r - s
    have hX : X ≠ 0 := by
      intro hX0
      apply hrsq
      dsimp [X] at hX0
      have hr_eq : r = -s := by omega
      rw [hr_eq]
      ring
    have hY : Y ≠ 0 := by
      intro hY0
      apply hrsq
      dsimp [Y] at hY0
      have hr_eq : r = s := by omega
      rw [hr_eq]
    have hXY : X ^ 2 ≠ Y ^ 2 := by
      intro hsq
      dsimp [X, Y] at hsq
      have hrs0 : r * s = 0 := by nlinarith
      exact mul_ne_zero hr hs hrs0
    have hLQ : X ^ 4 + 14 * X ^ 2 * Y ^ 2 + Y ^ 4 = (4 * H) ^ 2 := by
      dsimp [X, Y]
      nlinarith [hHeq, show
        (r + s) ^ 4 + 14 * (r + s) ^ 2 * (r - s) ^ 2 + (r - s) ^ 4 =
          16 * (r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) by ring]
    exact not_ljunggren_14 (x := X) (y := Y) (z := 4 * H) hX hY hXY hLQ
