import Mathlib

/-!
# Integer solutions of w^2 = u^3 + u^2 - u

We prove: for u w : Z, w^2 = u^3 + u^2 - u implies u in {-1, 0, 1}.
This discharges the integer case of obstruction_curve_20a4_points_degenerate.
-/

theorem int_solutions_20a4 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  by_cases hu_neg : u ≤ -2
  · exfalso; have := sq_nonneg w; nlinarith
  · by_cases hu_pos : 2 ≤ u
    · exfalso
      have hfact : u * (u ^ 2 + u - 1) = w ^ 2 := by nlinarith
      have hu0 : (0 : ℤ) < u := by linarith
      have hv0 : (0 : ℤ) < u ^ 2 + u - 1 := by nlinarith
      have hcop : IsCoprime u (u ^ 2 + u - 1) := ⟨u + 1, -1, by ring⟩
      -- Coprime product is a square => each factor is +/- square
      obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
      · -- u = a^2. Since u >= 2, a^2 >= 2, so |a| >= 2, a^2 >= 4.
        have haa : a ^ 2 ≥ 2 := by linarith
        have haa4 : a ^ 2 ≥ 4 := by
          by_cases h1 : a ≤ -2
          · nlinarith
          · by_cases h2 : a ≥ 2
            · nlinarith
            · have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
              rcases this with rfl | rfl | rfl <;> norm_num at haa
        -- v := u^2+u-1 = a^4+a^2-1 is also coprime-square factor
        have hcop' : IsCoprime (u ^ 2 + u - 1) u := hcop.symm
        have hfact' : (u ^ 2 + u - 1) * u = w ^ 2 := by nlinarith
        obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hfact'
        · -- u^2+u-1 = b^2. Substituting u = a^2:
          -- b^2 = a^4 + a^2 - 1
          have hkey : b ^ 2 = a ^ 4 + a ^ 2 - 1 := by nlinarith
          -- Squeeze: a^4 < b^2 < (a^2+1)^2
          have : a ^ 4 < b ^ 2 := by nlinarith
          have : b ^ 2 < (a ^ 2 + 1) ^ 2 := by nlinarith
          -- b^2 > 0, so b != 0
          have hb_pos : 0 < b ^ 2 := by nlinarith
          have hb_ne : b ≠ 0 := by intro h0; simp [h0] at hb_pos
          -- |b| > |a^2| = a^2 and |b| < a^2+1, so a^2 < |b| < a^2+1
          rcases lt_or_gt_of_ne hb_ne with hbn | hbp
          · have : a ^ 2 < -b := by nlinarith [sq_nonneg (b + a ^ 2)]
            have : -b < a ^ 2 + 1 := by nlinarith [sq_nonneg (b + a ^ 2 + 1)]
            omega
          · have : a ^ 2 < b := by nlinarith [sq_nonneg (b - a ^ 2 - 1)]
            have : b < a ^ 2 + 1 := by nlinarith [sq_nonneg (b - a ^ 2)]
            omega
        · -- u^2+u-1 = -b^2. But u^2+u-1 > 0 (since u >= 2), contradiction.
          have : u ^ 2 + u - 1 > 0 := by nlinarith
          nlinarith [sq_nonneg b]
      · -- u = -a^2. But u >= 2 > 0, contradiction.
        nlinarith [sq_nonneg a]
    · omega
