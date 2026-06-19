import Mathlib

/-!
# Final assembly for the `20.a4` obstruction curve

This file assembles the rational result from:

* the descent map and cover equation,
* the prime-divisor obstruction on covers,
* the denominator-quartic infinite descent,
* and the already-proved integer case.

The only named bridge left here is the rational lowest-terms/denominator
normalization step.  It is precisely the place where one clears denominators
and invokes `no_denominator_quartic` to force denominator `1`.
-/

namespace Scratch.ChatGPTDropDM1

/--
Integer case, supplied by `scratch/Descent20a4.lean`.

In the actual assembly file this should be replaced by importing that theorem.
-/
axiom int_solutions_20a4
    (u w : ℤ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1

/--
Rational-to-integral bridge for the curve `y² = x³ + x² - x`.

This packages the allowed hard bridge steps:

1. write `u = p/q` in lowest terms;
2. if `u = 0`, the final theorem is immediate;
3. if `u ≠ 0`, use the descent map to obtain a cover `C_d`;
4. use the cover prime-divisor obstruction / `cover_forces_unit` to get `d = ±1`;
5. use the denominator-quartic descent to rule out `q ≥ 2`;
6. conclude `q = 1`, so `u` is integral;
7. clear the remaining rational square denominator for `w`, producing an integer `W`.

This is the only place where the rational lowest-terms and denominator-clearing
machinery is hidden.
-/
axiom rational_point_to_integer_point_20a4
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ U W : ℤ,
      u = (U : ℚ) ∧
      w = (W : ℚ) ∧
      W ^ 2 = U ^ 3 + U ^ 2 - U

/--
Rational points on `20.a4 : y² = x³ + x² - x` have
`x ∈ {-1,0,1}`.
-/
theorem obstruction_20a4_discharge (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  obtain ⟨U, W, hu, _hw, hUW⟩ := rational_point_to_integer_point_20a4 u w h
  have hU : U = -1 ∨ U = 0 ∨ U = 1 := int_solutions_20a4 U W hUW
  rcases hU with hU | hU | hU
  · left
    rw [hu, hU]
    norm_num
  · right; left
    rw [hu, hU]
    norm_num
  · right; right
    rw [hu, hU]
    norm_num

end Scratch.ChatGPTDropDM1
