import Mathlib

/-!
# Explicit 2-isogeny descent map for y² = x³ + x² - x

The descent map: if (x,y) is a rational point with x ≠ 0 and x = d*u²,
then (u, v) where v = y/(d*u) satisfies d*v² = d²*u⁴ + d*u² - 1.

This is the concrete replacement for the cohomological connecting map H¹(Q, E[φ]).
-/

theorem descent_map (x y d u : ℚ) (hx : x ≠ 0) (hu : u ≠ 0) (hd : d ≠ 0)
    (hE : y ^ 2 = x ^ 3 + x ^ 2 - x)
    (hdu : x = d * u ^ 2) :
    let v := y / (d * u)
    d * v ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1 := by
  simp only
  have hdu_ne : d * u ≠ 0 := mul_ne_zero hd hu
  field_simp [hdu_ne]
  have : y ^ 2 * 1 = (d * u ^ 2) ^ 3 + (d * u ^ 2) ^ 2 - (d * u ^ 2) := by
    rw [← hdu]; ring_nf; linarith
  nlinarith [sq_nonneg y, sq_nonneg u, sq_nonneg d]

