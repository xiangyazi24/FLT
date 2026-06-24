import Mathlib

/-!
# Denominator theorem for y²=x³+x²-x

The squareclass bypass: cover_forces_unit + squarefree decomposition
directly force u.den = 1.
-/

-- From CoverPrimeDivisor.lean (already proved, 0 sorry)
private theorem cover_no_sol_prime (p d u v : ℤ) (hp : Prime p) (hpd : p ∣ d)
    (h : d * v ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1) : False := by
  rcases hpd with ⟨k, rfl⟩
  have : p ∣ (1 : ℤ) := ⟨p * k ^ 2 * u ^ 4 + k * u ^ 2 - k * v ^ 2, by nlinarith⟩
  exact hp.not_dvd_one this

-- From DescentMap.lean (already proved, 0 sorry)
private theorem descent_map_cover (x y d u : ℚ) (hu : u ≠ 0) (hd : d ≠ 0)
    (hE : y ^ 2 = x ^ 3 + x ^ 2 - x) (hdu : x = d * u ^ 2) :
    d * (y / (d * u)) ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1 := by
  have hdu_ne : d * u ≠ 0 := mul_ne_zero hd hu
  field_simp [hdu_ne]
  rw [hdu] at hE
  nlinarith [sq_nonneg y, sq_nonneg u]

-- The key: squarefree d with a prime factor → False
-- (from cover equation + cover_no_sol_prime)
private theorem squarefree_part_unit (x y : ℚ) (d : ℤ) (u : ℚ)
    (hd_ne : (d : ℚ) ≠ 0) (hu_ne : u ≠ 0)
    (hE : y ^ 2 = x ^ 3 + x ^ 2 - x) (hdu : x = (d : ℚ) * u ^ 2)
    (hsf : Squarefree d) : d = 1 ∨ d = -1 := by
  by_contra habs
  push_neg at habs
  obtain ⟨h1, hm1⟩ := habs
  have hna : d.natAbs ≠ 1 := by
    intro heq; rcases Int.natAbs_eq d with rfl | rfl <;> simp_all
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hna
  have hcover := descent_map_cover x y (d : ℚ) u hu_ne hd_ne hE hdu
  -- Cast: d as ℤ, cover equation over ℚ
  -- Need to derive integer cover equation from rational one
  sorry -- connect rational cover to integer cover_no_sol_prime

-- Main theorem
theorem rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  sorry -- uses squarefree_part_unit + denominator quartic

