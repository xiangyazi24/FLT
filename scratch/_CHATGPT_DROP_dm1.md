# Q1427 (dm1): positivity of the quartic factors `U,V`

The clean Lean route is to isolate a general sign lemma:

```lean
0 < x*y ∧ 0 < x+y  ⟹  0 < x ∧ 0 < y.
```

This avoids explicit zero cases.  `Int.mul_pos_iff` says a positive integer product means either both factors are positive or both are negative; the positive sum rules out the second case.

I also include the requested local sublemma: from `0 < x*y` and `y < 0`, infer `x < 0`.

```lean
import Mathlib

namespace DM1

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

/-- The exact sign step requested in the prompt. -/
lemma left_neg_of_mul_pos_of_right_neg {x y : ℤ}
    (hxy : 0 < x * y) (hy : y < 0) :
    x < 0 := by
  rcases Int.mul_pos_iff.mp hxy with hpos | hneg
  · exact False.elim (by linarith [hpos.2, hy])
  · exact hneg.1

/-- Symmetric companion. -/
lemma right_neg_of_mul_pos_of_left_neg {x y : ℤ}
    (hxy : 0 < x * y) (hx : x < 0) :
    y < 0 := by
  rcases Int.mul_pos_iff.mp hxy with hpos | hneg
  · exact False.elim (by linarith [hpos.1, hx])
  · exact hneg.2

/-- If a product and the sum are both positive, then both factors are positive. -/
lemma both_pos_of_mul_pos_of_add_pos {x y : ℤ}
    (hxy : 0 < x * y) (hadd : 0 < x + y) :
    0 < x ∧ 0 < y := by
  rcases Int.mul_pos_iff.mp hxy with hpos | hneg
  · exact hpos
  · have hsum_neg : x + y < 0 := by linarith [hneg.1, hneg.2]
    exact False.elim (by linarith [hadd, hsum_neg])

lemma quartic_UV_product
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    U r B s * V r B s = 5 * B ^ 4 := by
  calc
    U r B s * V r B s = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
      dsimp [U, V]
      ring
    _ = 5 * B ^ 4 := by
      rw [hs]
      ring

lemma quartic_U_add_V (r B s : ℤ) :
    U r B s + V r B s = 4 * r ^ 2 + 2 * B ^ 2 := by
  dsimp [U, V]
  ring

lemma quartic_UV_pos
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hB : 0 < B) :
    0 < U r B s * V r B s := by
  rw [quartic_UV_product hs]
  have hB4 : 0 < B ^ 4 := pow_pos hB 4
  exact mul_pos (by norm_num : (0 : ℤ) < 5) hB4

lemma quartic_U_add_V_pos
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) :
    0 < U r B s + V r B s := by
  rw [quartic_U_add_V]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero (ne_of_gt hr)
  have hB2 : 0 < B ^ 2 := sq_pos_of_ne_zero (ne_of_gt hB)
  nlinarith

/-- Core positivity result for both factors. -/
theorem U_and_V_pos
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr : 0 < r) (hB : 0 < B) :
    0 < U r B s ∧ 0 < V r B s := by
  exact both_pos_of_mul_pos_of_add_pos
    (quartic_UV_pos hs hB)
    (quartic_U_add_V_pos hr hB)

/-- Positivity of the lower factor. -/
theorem U_pos
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr : 0 < r) (hB : 0 < B) :
    0 < 2 * r ^ 2 + B ^ 2 - 2 * s := by
  simpa [U] using (U_and_V_pos hs hr hB).1

/-- Positivity of the upper factor. -/
theorem V_pos
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr : 0 < r) (hB : 0 < B) :
    0 < 2 * r ^ 2 + B ^ 2 + 2 * s := by
  simpa [V] using (U_and_V_pos hs hr hB).2

end DM1
```

The key line is:

```lean
rcases Int.mul_pos_iff.mp hxy with hpos | hneg
```

In the `hneg` branch, `hneg.1 : x < 0` and `hneg.2 : y < 0`.  In the positive branch, a hypothesis like `y < 0` contradicts `hpos.2 : 0 < y` by `linarith`.
