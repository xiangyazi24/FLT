import FLT.Assumptions.MazurProof.N13ArithmeticBasics
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N13Arithmetic

/-- An integer polynomial certificate for the characteristic-two affine
Jacobian calculation. This identity itself holds in every commutative ring.
The final summand vanishes in characteristic two. -/
theorem optimized_char_two_affine_certificate
    {K : Type*} [CommRing K] (u v : K) :
    u ^ 2 =
      u ^ 4 *
          (v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v - (u ^ 2 + u)) -
        (u ^ 2 * v + 1) ^ 2 +
        (u ^ 3 + 1 - u ^ 4 * v) * (u ^ 3 + u ^ 2 + 1) +
        2 * (u ^ 2 * v - u ^ 3) := by
  ring

/-- A06: the two affine partial derivatives cannot vanish simultaneously
at a point of the optimized N13 curve in characteristic two. -/
theorem optimized_char_two_nonsingular
    {K : Type*} [Field K] [CharP K 2] (u v : K)
    (h : OptEquation13 u v) :
    u ^ 3 + u ^ 2 + 1 ≠ 0 ∨ u ^ 2 * v + 1 ≠ 0 := by
  classical
  by_cases hdu : u ^ 3 + u ^ 2 + 1 = 0
  · right
    intro hdv
    have heq :
        v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v - (u ^ 2 + u) = 0 := by
      exact sub_eq_zero.mpr h
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hu2 : u ^ 2 = 0 := by
      have hc := optimized_char_two_affine_certificate u v
      rw [heq, hdv, hdu, htwo] at hc
      simpa only [mul_zero, zero_mul,
        zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self, add_zero] using hc
    have hone : (1 : K) = 0 := by
      simpa only [hu2, zero_mul, zero_add] using hdv
    exact one_ne_zero hone
  · exact Or.inl hdu

end MazurProof.N13Arithmetic
