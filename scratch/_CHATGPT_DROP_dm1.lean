import Mathlib

/-!
# Large-u descent for N=12

Task file requested a proof of the large-positive case

`5 ≤ u → w² = u³ - u² - 4u + 4 → False`.

The proof follows the same shape as `scratch/Descent20a4.lean`:
produce explicit Bézout witnesses for coprimality, apply
`Int.sq_of_isCoprime`, then squeeze between consecutive squares.

The `3 ∣ u - 1` branch reduces to the quartic square equation
`b² = 3*a^4 + 2*a^2 - 1`.  That final quartic exclusion is isolated as a
local axiom; the rest of the descent is explicit Lean code.
-/

namespace Scratch.ChatGPTDropDM1

/-- Polynomial factorization for the N=12 curve. -/
theorem N12_factor (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u - 2) * (u + 2) := by
  ring

/-- The quadratic factor form used in the descent. -/
theorem N12_factor₂ (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u ^ 2 - 4) := by
  ring

/-- If `3 ∤ u - 1`, then `u - 1` and `u² - 4` are coprime. -/
theorem N12_coprime_of_not_three_dvd (u : ℤ)
    (h3 : ¬ (3 : ℤ) ∣ u - 1) : IsCoprime (u - 1) (u ^ 2 - 4) := by
  have hmod : (u - 1) % 3 = 0 ∨ (u - 1) % 3 = 1 ∨ (u - 1) % 3 = 2 := by
    omega
  rcases hmod with h0 | h1 | h2
  · exact False.elim (h3 (Int.dvd_of_emod_eq_zero h0))
  · let q : ℤ := (u - 1) / 3
    have hq : u - 1 = 3 * q + 1 := by
      dsimp [q]
      omega
    refine ⟨1 - q * (u + 1), q, ?_⟩
    ring_nf
    omega
  · let q : ℤ := (u + 1) / 3
    have hq : u - 1 = 3 * q - 1 := by
      dsimp [q]
      omega
    refine ⟨-1 + q * (u + 1), -q, ?_⟩
    ring_nf
    omega

/-- The quartic square sublemma needed in the `3 ∣ u - 1` branch. -/
axiom N12_quartic_square_only_pm_one (a b : ℤ) :
    b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 → a ^ 2 = 1

/--
Large-positive case for the N=12 integer descent.
-/
theorem N12_large_descent (u w : ℤ)
    (hu : 5 <= u)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) : False := by
  have hfact : (u - 1) * (u ^ 2 - 4) = w ^ 2 := by
    rw [N12_factor₂] at h
    exact h.symm
  have hu1_pos : 0 < u - 1 := by omega
  have hu2_pos : 0 < u ^ 2 - 4 := by nlinarith
  by_cases h3 : (3 : ℤ) ∣ u - 1
  · rcases h3 with ⟨s, hs⟩
    have hs_def : u - 1 = 3 * s := hs
    have hs_ge : 2 <= s := by omega
    have hu_eq : u = 3 * s + 1 := by omega
    have hquad : u ^ 2 - 4 = 3 * (3 * s ^ 2 + 2 * s - 1) := by
      rw [hu_eq]
      ring
    have h9 : w ^ 2 = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by
      calc
        w ^ 2 = (u - 1) * (u ^ 2 - 4) := hfact.symm
        _ = (3 * s) * (3 * (3 * s ^ 2 + 2 * s - 1)) := by rw [hs_def, hquad]
        _ = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by ring
    have h3sq : (3 : ℤ) ∣ w ^ 2 := by
      rw [h9]
      exact dvd_mul_of_dvd_left (show (3 : ℤ) ∣ 9 by norm_num) _
    have h3w : (3 : ℤ) ∣ w := by
      have hp : Prime (3 : ℤ) := by norm_num
      have hmul : (3 : ℤ) ∣ w * w := by
        simpa [pow_two] using h3sq
      rcases hp.dvd_or_dvd hmul with hw | hw
      · exact hw
      · exact hw
    rcases h3w with ⟨k, hk⟩
    have hk_sq : k ^ 2 = s * (3 * s ^ 2 + 2 * s - 1) := by
      subst w
      ring_nf at h9
      nlinarith
    have hk_prod_sq : s * (3 * s ^ 2 + 2 * s - 1) = k ^ 2 := by
      nlinarith
    have hcop : IsCoprime s (3 * s ^ 2 + 2 * s - 1) := ⟨3 * s + 2, -1, by ring⟩
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hk_prod_sq
    · have hcop' : IsCoprime (3 * s ^ 2 + 2 * s - 1) s := hcop.symm
      have hk_sq' : (3 * s ^ 2 + 2 * s - 1) * s = k ^ 2 := by
        nlinarith
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hk_sq'
      · have hquartic : b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 := by
          calc
            b ^ 2 = 3 * s ^ 2 + 2 * s - 1 := hb.symm
            _ = 3 * a ^ 4 + 2 * a ^ 2 - 1 := by
              rw [ha]
              ring
        have ha1 : a ^ 2 = 1 := N12_quartic_square_only_pm_one a b hquartic
        nlinarith
      · have hpos : 0 < 3 * s ^ 2 + 2 * s - 1 := by nlinarith
        nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]
  · have hcop : IsCoprime (u - 1) (u ^ 2 - 4) :=
      N12_coprime_of_not_three_dvd u h3
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
    · have ha_ge4 : 4 <= a ^ 2 := by nlinarith
      have hcop' : IsCoprime (u ^ 2 - 4) (u - 1) := hcop.symm
      have hfact' : (u ^ 2 - 4) * (u - 1) = w ^ 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hfact
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hfact'
      · have hu_eq : u = a ^ 2 + 1 := by nlinarith
        have hkey : b ^ 2 = (a ^ 2 + 1) ^ 2 - 4 := by
          calc
            b ^ 2 = u ^ 2 - 4 := hb.symm
            _ = (a ^ 2 + 1) ^ 2 - 4 := by
              rw [hu_eq]
        have hlow : a ^ 4 < b ^ 2 := by nlinarith
        have hhigh : b ^ 2 < (a ^ 2 + 1) ^ 2 := by nlinarith
        have hb_pos : 0 < b ^ 2 := by nlinarith
        have hb_ne : b ≠ 0 := by
          intro h0
          simp [h0] at hb_pos
        rcases lt_or_gt_of_ne hb_ne with hbneg | hbpos
        · have hlt : a ^ 2 < -b := by
            nlinarith [sq_nonneg (b + a ^ 2)]
          have hgt : -b < a ^ 2 + 1 := by
            nlinarith [sq_nonneg (b + a ^ 2 + 1)]
          omega
        · have hlt : a ^ 2 < b := by
            nlinarith [sq_nonneg (b - a ^ 2 - 1)]
          have hgt : b < a ^ 2 + 1 := by
            nlinarith [sq_nonneg (b - a ^ 2)]
          omega
      · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]

end Scratch.ChatGPTDropDM1
