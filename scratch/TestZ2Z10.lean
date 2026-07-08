import Mathlib

set_option maxHeartbeats 800000

noncomputable section

open Function

variable {H : Type*} [AddCommGroup H]

theorem eq_five_nsmul_of_order_two_in_zmultiples
    {η Q : H}
    (hη : addOrderOf η = 2)
    (hQ : addOrderOf Q = 10)
    (hmem : η ∈ AddSubgroup.zmultiples Q) :
    η = 5 • Q := by
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨z, hz⟩ := hmem
  have h2η_nat : (2 : ℕ) • η = 0 := by simpa [hη] using addOrderOf_nsmul_eq_zero η
  have h2η : (2 : ℤ) • η = 0 := by exact_mod_cast h2η_nat
  have h2zQ : (2 * z) • Q = 0 := by
    calc (2 * z) • Q = (2 : ℤ) • (z • Q) := by rw [mul_zsmul]
      _ = (2 : ℤ) • η := by rw [hz]
      _ = 0 := h2η
  have hdvd : (10 : ℤ) ∣ (2 * z) := by
    have h10Q_nat : (10 : ℕ) • Q = 0 := by simpa [hQ] using addOrderOf_nsmul_eq_zero Q
    have h10Q : (10 : ℤ) • Q = 0 := by exact_mod_cast h10Q_nat
    rwa [← addOrderOf_dvd_iff_zsmul_eq_zero, hQ] at h2zQ
  have h5dvz : (5 : ℤ) ∣ z := by omega
  obtain ⟨k, rfl⟩ := h5dvz
  have hη_ne : η ≠ 0 := by intro h; rw [h] at hη; simp at hη
  have h10Q : (10 : ℤ) • Q = 0 := by
    exact_mod_cast (by simpa [hQ] using addOrderOf_nsmul_eq_zero Q : (10 : ℕ) • Q = 0)
  have hk_odd : ¬ (2 : ℤ) ∣ k := by
    intro ⟨m, hm⟩
    apply hη_ne
    calc η = (5 * k) • Q := hz.symm
      _ = (5 * (2 * m)) • Q := by rw [hm]
      _ = (10 * m) • Q := by ring_nf
      _ = (10 : ℤ) • (m • Q) := by rw [mul_zsmul]
      _ = m • ((10 : ℤ) • Q) := by rw [zsmul_comm]
      _ = m • (0 : H) := by rw [h10Q]
      _ = 0 := smul_zero m
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = 2 * m + 1 := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exfalso; exact hk_odd ⟨m, by linarith⟩
    · exact ⟨m, by linarith⟩
  have key : (5 * (2 * m + 1) : ℤ) • Q = (5 : ℕ) • Q := by
    rw [show (5 : ℤ) * (2 * m + 1) = 10 * m + 5 from by ring, add_zsmul, mul_zsmul]
    rw [show (10 : ℤ) • (m • Q) = m • ((10 : ℤ) • Q) from by rw [zsmul_comm]]
    rw [h10Q, smul_zero, zero_add]
    exact_mod_cast (rfl : (5 : ℕ) • Q = (5 : ℕ) • Q)
  exact hz.symm.trans key
