import Mathlib

/-!
# Integer solutions of w² = u³ + u² - 2u (N=14 obstruction curve)
-/

private lemma not_sq_two (w : ℤ) (h : w ^ 2 = 2) : False := by
  have : -1 ≤ w ∧ w ≤ 1 := ⟨by nlinarith [sq_nonneg (w+1)], by nlinarith [sq_nonneg (w-1)]⟩
  have : w = -1 ∨ w = 0 ∨ w = 1 := by omega
  rcases this with rfl | rfl | rfl <;> simp_all

private lemma not_sq_eight (w : ℤ) (h : w ^ 2 = 8) : False := by
  have : -2 ≤ w ∧ w ≤ 2 := ⟨by nlinarith [sq_nonneg (w+2)], by nlinarith [sq_nonneg (w-2)]⟩
  have : w = -2 ∨ w = -1 ∨ w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp_all

private lemma coprime_u_poly_odd (u : ℤ) (hodd : ¬ 2 ∣ u) :
    IsCoprime u (u ^ 2 + u - 2) := by
  rw [show u ^ 2 + u - 2 = (u + 1) * u + (-2) from by ring]
  have h2 : IsCoprime u (-2 : ℤ) := by
    rw [IsCoprime.neg_right_iff]
    exact isCoprime_comm.mpr
      ((Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2:ℤ)).coprime_iff_not_dvd.mpr hodd)
  exact h2.mul_add_right_right (u + 1)

private lemma no_sol_2a4_a2_m1 (a b : ℤ) (h : b ^ 2 = 2 * a ^ 4 + a ^ 2 - 1)
    (ha : a ^ 2 ≥ 2) : False := by
  rcases Int.even_or_odd a with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
  rcases Int.even_or_odd b with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have : 4*d^2 = 32*c^4+4*c^2-1 := by nlinarith
    omega
  · have : 4*d^2+4*d+1 = 32*c^4+4*c^2-1 := by nlinarith
    omega
  · have : 4*d^2 = 2*(16*c^4+32*c^3+24*c^2+8*c+1)+(4*c^2+4*c+1)-1 := by nlinarith
    omega
  · have : 4*d^2+4*d+1 = 2*(16*c^4+32*c^3+24*c^2+8*c+1)+(4*c^2+4*c+1)-1 := by nlinarith
    omega

private lemma n14_odd_case (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u)
    (hu : 3 ≤ u) (hodd : ¬ 2 ∣ u) : False := by
  have hfact : u * (u ^ 2 + u - 2) = w ^ 2 := by nlinarith
  have hu0 : (0 : ℤ) < u := by linarith
  have hv0 : (0 : ℤ) < u ^ 2 + u - 2 := by nlinarith
  have hcop := coprime_u_poly_odd u hodd
  obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
  · have haa : a ^ 2 ≥ 3 := by linarith
    obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop.symm (show (u ^ 2 + u - 2) * u = w ^ 2 by nlinarith)
    · have hkey : b ^ 2 = a ^ 4 + a ^ 2 - 2 := by nlinarith
      have hbpos : 0 < b ^ 2 := by nlinarith
      have hbne : b ≠ 0 := by intro h0; simp [h0] at hbpos
      rcases lt_or_gt_of_ne hbne with hbn | hbp
      · have : a ^ 2 - 1 < -b := by nlinarith [sq_nonneg (b + a ^ 2 - 1)]
        have : -b < a ^ 2 + 1 := by nlinarith [sq_nonneg (b + a ^ 2 + 1)]
        have : -b = a ^ 2 := by omega
        nlinarith
      · have : a ^ 2 - 1 < b := by nlinarith [sq_nonneg (b - a ^ 2 + 1)]
        have : b < a ^ 2 + 1 := by nlinarith [sq_nonneg (b - a ^ 2 - 1)]
        have : b = a ^ 2 := by omega
        nlinarith
    · nlinarith [sq_nonneg b]
  · nlinarith [sq_nonneg a]

private lemma n14_even_case (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u)
    (hu : 4 ≤ u) (heven : 2 ∣ u) : False := by
  obtain ⟨m, rfl⟩ := heven
  have hm : 2 ≤ m := by omega
  -- w² = 2m(4m²+2m-2) = 4m(2m²+m-1). w even.
  have h2w : (2 : ℤ) ∣ w := by
    have : (2 : ℤ) ∣ w ^ 2 := ⟨2 * m * (2 * m ^ 2 + m - 1), by nlinarith⟩
    exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (2:ℤ)).dvd_of_dvd_pow this
  obtain ⟨k, rfl⟩ := h2w
  -- k² = m(2m²+m-1). IsCoprime m (2m²+m-1) via witness (2m+1, -1).
  have hkfact : m * (2 * m ^ 2 + m - 1) = k ^ 2 := by nlinarith
  have hm0 : (0 : ℤ) < m := by linarith
  have hv0 : (0 : ℤ) < 2 * m ^ 2 + m - 1 := by nlinarith
  have hcop_m : IsCoprime m (2 * m ^ 2 + m - 1) := ⟨2 * m + 1, -1, by ring⟩
  obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop_m hkfact
  · -- m = a², 2m²+m-1 = b² = 2a⁴+a²-1
    have haa : a ^ 2 ≥ 2 := by linarith
    obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop_m.symm (show (2 * m ^ 2 + m - 1) * m = k ^ 2 by nlinarith)
    · exact no_sol_2a4_a2_m1 a b (by nlinarith) haa
    · nlinarith [sq_nonneg b]
  · nlinarith [sq_nonneg a]

theorem int_solutions_N14 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u) :
    u = -2 ∨ u = 0 ∨ u = 1 := by
  by_cases hu_neg : u ≤ -3
  · exfalso; have := sq_nonneg w; nlinarith
  · by_cases hu_pos : 3 ≤ u
    · exfalso
      by_cases hodd : ¬ (2 ∣ u)
      · exact n14_odd_case u w h hu_pos hodd
      · push Not at hodd
        exact n14_even_case u w h (by omega) hodd
    · have : u = -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · left; rfl
      · exfalso; exact not_sq_two w (by linarith)
      · right; left; rfl
      · right; right; rfl
      · exfalso; exact not_sq_eight w (by linarith)

