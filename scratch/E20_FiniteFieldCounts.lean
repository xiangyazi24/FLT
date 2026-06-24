import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Finite-field affine point counts for `E20 : y² = x³ + x² - x`

These are brute-force affine counts over small finite fields, checked by
`native_decide`.  The projective point at infinity should be added separately,
so the total counts are affine count plus `1`.
-/

namespace Scratch.E20_FiniteFieldCounts

/-- Affine points on `y² = x³ + x² - x` over `𝔽₃`: total projective count is `6`. -/
theorem E20_F3_affine_count :
    (Finset.univ.filter (fun p : ZMod 3 × ZMod 3 =>
      p.2 ^ 2 = p.1 ^ 3 + p.1 ^ 2 - p.1)).card = 5 := by
  native_decide

/-- Affine points on `y² = x³ + x² - x` over `𝔽₅`: total projective count is `7`. -/
theorem E20_F5_affine_count :
    (Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
      p.2 ^ 2 = p.1 ^ 3 + p.1 ^ 2 - p.1)).card = 6 := by
  native_decide

/-- Affine points on `y² = x³ + x² - x` over `𝔽₇`: total projective count is `6`. -/
theorem E20_F7_affine_count :
    (Finset.univ.filter (fun p : ZMod 7 × ZMod 7 =>
      p.2 ^ 2 = p.1 ^ 3 + p.1 ^ 2 - p.1)).card = 5 := by
  native_decide

end Scratch.E20_FiniteFieldCounts
