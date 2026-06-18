import Mathlib

/-!
# The 2-isogeny for curve 20.a4

This scratch file keeps the maps as concrete rational functions on `ℚ × ℚ`.
-/

namespace Isogeny20a4

/-- The isogeny `E : y^2 = x^3 + x^2 - x` to
`E' : Y^2 = X^3 - 2*X^2 + 5*X`, written as rational functions. -/
def phi (x y : ℚ) : ℚ × ℚ :=
  (y ^ 2 / x ^ 2, -y * (x ^ 2 + 1) / x ^ 2)

/-- The dual isogeny, written as rational functions. -/
def phi_hat (X Y : ℚ) : ℚ × ℚ :=
  (Y ^ 2 / (4 * X ^ 2), Y * (5 - X ^ 2) / (8 * X ^ 2))

/--
`norm_num` alone is not enough here: after unfolding `phi` and substituting the
curve equation, this is a symbolic rational-function identity.  The proof below
rewrites the square on the left, clears denominators, and then uses `ring`.
-/
theorem phi_maps_E_to_Eprime (x y : ℚ) (hx : x ≠ 0)
    (hE : y ^ 2 = x ^ 3 + x ^ 2 - x) :
    let (X, Y) := phi x y
    Y ^ 2 = X ^ 3 - 2 * X ^ 2 + 5 * X := by
  dsimp [phi]
  have hsq :
      (-y * (x ^ 2 + 1) / x ^ 2) ^ 2 =
        y ^ 2 * (x ^ 2 + 1) ^ 2 / x ^ 4 := by
    ring_nf
  rw [hsq, hE]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx
  field_simp [hx, hx2, hx4]
  ring

end Isogeny20a4
