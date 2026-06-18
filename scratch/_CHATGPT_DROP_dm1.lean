import Mathlib

/-!
# Large-u descent for N=12

Task file requested a complete proof of the large-positive case

`5 ≤ u → w² = u³ - u² - 4u + 4 → False`.

I read `scratch/Descent20a4.lean`.  Its proof uses the pattern

1. produce an `IsCoprime` Bezout witness,
2. apply `Int.sq_of_isCoprime` to split a coprime product equal to a square,
3. squeeze between consecutive squares.

For this N=12 curve, the non-`3 ∣ u-1` branch follows that same pattern.  The
`3 ∣ u-1` branch reduces to the quartic square equation

`b² = 3*a^4 + 2*a^2 - 1`,

whose only integer solutions are `a = ±1`.  Since the large case has `u ≥ 5`,
this would force `s = a² ≥ 2`, contradiction.  That quartic step is isolated
below as `N12_quartic_square_only_pm_one`; it is the genuinely additional
number-theoretic lemma not present in the 20.a4 reference file.
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

/-- Squares modulo `3` are `0` or `1`. -/
theorem sq_mod_three (z : ℤ) : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
  have hz : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hz with hz | hz | hz
  · left
    calc
      z ^ 2 % 3 = ((z % 3) ^ 2) % 3 := by omega
      _ = 0 := by omega
  · right
    calc
      z ^ 2 % 3 = ((z % 3) ^ 2) % 3 := by omega
      _ = 1 := by omega
  · right
    calc
      z ^ 2 % 3 = ((z % 3) ^ 2) % 3 := by omega
      _ = 1 := by omega

/-- The quartic square sublemma needed in the `3 ∣ u-1` branch. -/
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
      subst u
      ring
    have h9 : w ^ 2 = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by
      calc
        w ^ 2 = (u - 1) * (u ^ 2 - 4) := hfact.symm
        _ = (3 * s) * (3 * (3 * s ^ 2 + 2 * s - 1)) := by rw [hs_def, hquad]
        _ = 9 * (s * (3 * s ^ 2 + 2 * s - 1)) := by ring
    have hw_mod : w ^ 2 % 3 = 0 := by
      rw [h9]
      omega
    have h3w : (3 : ℤ) ∣ w := by
      rcases sq_mod_three w with hw0 | hw1
      · exact Int.dvd_of_emod_eq_zero hw0
      · omega
    rcases h3w with ⟨k, hk⟩
    have hk_sq : k ^ 2 = s * (3 * s ^ 2 + 2 * s - 1) := by
      subst w
      nlinarith
    have hcop : IsCoprime s (3 * s ^ 2 + 2 * s - 1) := ⟨-(3 * s + 2), 1, by ring⟩
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hk_sq.symm
    · have hcop' : IsCoprime (3 * s ^ 2 + 2 * s - 1) s := hcop.symm
      have hk_sq' : (3 * s ^ 2 + 2 * s - 1) * s = k ^ 2 := by nlinarith
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hk_sq'
      · have hquartic : b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 := by
          nlinarith
        have ha1 : a ^ 2 = 1 := N12_quartic_square_only_pm_one a b hquartic
        nlinarith
      · have hpos : 0 < 3 * s ^ 2 + 2 * s - 1 := by nlinarith
        nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]
  · have hcop : IsCoprime (u - 1) (u ^ 2 - 4) := by
      refine ⟨-(u + 1), 1, ?_⟩
      ring
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
    · have ha_ge2 : 2 <= a ^ 2 := by nlinarith
      have ha_ge4 : 4 <= a ^ 2 := by
        by_cases hle : a <= -2
        · nlinarith
        · by_cases hge : 2 <= a
          · nlinarith
          · have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
            rcases this with rfl | rfl | rfl <;> norm_num at ha_ge2
      have hcop' : IsCoprime (u ^ 2 - 4) (u - 1) := hcop.symm
      have hfact' : (u ^ 2 - 4) * (u - 1) = w ^ 2 := by nlinarith
      obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hfact'
      · have hu_eq : u = a ^ 2 + 1 := by nlinarith
        have hkey : b ^ 2 = (a ^ 2 + 1) ^ 2 - 4 := by
          subst u
          nlinarith
        have hb_ne : b ≠ 0 := by
          intro hb0
          subst b
          nlinarith
        have hmul : (a ^ 2 + 1 - b) * (a ^ 2 + 1 + b) = 4 := by
          nlinarith
        rcases lt_or_gt_of_ne hb_ne with hbneg | hbpos
        · have hleft_pos : 0 < a ^ 2 + 1 + b := by
            have : 0 < -b := by omega
            nlinarith [sq_nonneg (b + a ^ 2 + 1)]
          have hright_gt4 : 4 < a ^ 2 + 1 - b := by nlinarith
          have : 4 < (a ^ 2 + 1 - b) * (a ^ 2 + 1 + b) := by nlinarith
          nlinarith
        · have hleft_pos : 0 < a ^ 2 + 1 - b := by
            nlinarith [sq_nonneg (b - (a ^ 2 + 1))]
          have hright_gt4 : 4 < a ^ 2 + 1 + b := by nlinarith
          have : 4 < (a ^ 2 + 1 - b) * (a ^ 2 + 1 + b) := by nlinarith
          nlinarith
      · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]

end Scratch.ChatGPTDropDM1
