import Mathlib

/-!
# Integer solutions of w^2 = u^3 - u^2 - u (N=16 obstruction curve)

Same method as Descent20a4: coprime factorization + squeeze.
y^2 = u(u^2-u-1), coprime since u^2-u-1 ≡ -1 mod u.
-/

theorem int_solutions_N16 (u w : ℤ) (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  by_cases hu_neg : u ≤ -2
  · exfalso; have := sq_nonneg w; nlinarith
  · by_cases hu_pos : 2 ≤ u
    · exfalso
      -- Factor: w^2 = u*(u^2-u-1)
      have hfact : u * (u ^ 2 - u - 1) = w ^ 2 := by nlinarith
      have hu0 : (0 : ℤ) < u := by linarith
      have hv0 : (0 : ℤ) < u ^ 2 - u - 1 := by nlinarith
      -- Coprimality: u*(u-1) + (u^2-u-1)*(-1) = 1
      have hcop : IsCoprime u (u ^ 2 - u - 1) := ⟨u - 1, -1, by ring⟩
      obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hcop hfact
      · -- u = a^2
        have haa : a ^ 2 ≥ 2 := by linarith
        have haa4 : a ^ 2 ≥ 4 := by
          by_cases h1 : a ≤ -2
          · nlinarith
          · by_cases h2 : a ≥ 2
            · nlinarith
            · have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
              rcases this with rfl | rfl | rfl <;> norm_num at haa
        have hcop' : IsCoprime (u ^ 2 - u - 1) u := hcop.symm
        have hfact' : (u ^ 2 - u - 1) * u = w ^ 2 := by nlinarith
        obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hcop' hfact'
        · -- u^2-u-1 = b^2, i.e. b^2 = a^4-a^2-1
          have hkey : b ^ 2 = a ^ 4 - a ^ 2 - 1 := by nlinarith
          -- Squeeze: (a^2-1)^2 < b^2 < (a^2)^2
          -- Lower: a^4-a^2-1 > a^4-2a^2+1 = (a^2-1)^2 when a^2 > 2, i.e. a^2 >= 4
          -- Upper: a^4-a^2-1 < a^4 = (a^2)^2 always
          have hb2_pos : 0 < b ^ 2 := by nlinarith
          have hb_ne : b ≠ 0 := by intro h0; simp [h0] at hb2_pos
          rcases lt_or_gt_of_ne hb_ne with hbn | hbp
          · have h1 : a ^ 2 - 1 < -b := by nlinarith [sq_nonneg (b + a ^ 2 - 1)]
            have h2 : -b < a ^ 2 := by nlinarith [sq_nonneg (b + a ^ 2)]
            omega
          · have h1 : a ^ 2 - 1 < b := by nlinarith [sq_nonneg (b - a ^ 2 + 1)]
            have h2 : b < a ^ 2 := by nlinarith [sq_nonneg (b - a ^ 2 + 1)]
            omega
        · -- u^2-u-1 = -b^2. But u^2-u-1 > 0, contradiction
          nlinarith [sq_nonneg b]
      · -- u = -a^2. But u > 0, contradiction
        nlinarith [sq_nonneg a]
    · omega
