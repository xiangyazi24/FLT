import Mathlib

theorem rat_sq_int_implies_den_one (r : ℚ) (N : ℤ) (h : (r : ℚ) ^ 2 = (N : ℚ)) : r.den = 1 := by
  have h2 : r.num ^ 2 = N * (r.den : ℤ) ^ 2 := by
    have : (r.num : ℚ) ^ 2 = N * (r.den : ℚ) ^ 2 := by
      rw [← Rat.num_div_den r] at h; field_simp at h; linarith
    exact_mod_cast this
  have hcop : IsCoprime r.num (r.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr r.reduced
  have hcop2 : IsCoprime (r.num ^ 2) ((r.den : ℤ) ^ 2) :=
    (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mpr hcop
  have hdvd : (r.den : ℤ) ^ 2 ∣ r.num ^ 2 := ⟨N, by linarith⟩
  have h1 : (r.den : ℤ) ^ 2 ∣ 1 := hcop2.symm.dvd_of_dvd_mul_left (by simpa using hdvd)
  have h3 : (r.den : ℤ) ^ 2 ≤ 1 := Int.le_of_dvd one_pos h1
  have h4 : (r.den : ℤ) ≥ 1 := by exact_mod_cast r.pos
  nlinarith
