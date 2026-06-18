import Mathlib

/-!
# The `d = 2` quartic obstruction

Task theorem:

```
theorem quartic_no_sol_d2 (s t : ℤ) (hcop : Int.gcd s 2 = 1) :
    s ^ 4 + s ^ 2 * 4 - 16 = t ^ 2 → False
```

For `|s| ≥ 3`, use the same squeeze pattern as `scratch/Descent20a4.lean`:

```
(s^2 + 1)^2 < t^2 < (s^2 + 2)^2.
```

Then split on the sign of `t` to get either
`s^2 + 1 < -t < s^2 + 2` or `s^2 + 1 < t < s^2 + 2`, impossible by
`omega`.  The remaining values `s ∈ {-2,-1,0,1,2}` are closed directly;
`Int.gcd s 2 = 1` excludes `s = ±2`.
-/

private lemma sq_ge_nine_of_le_neg_three (s : ℤ) (hs : s ≤ -3) :
    (9 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s + 3)]

private lemma sq_ge_nine_of_three_le (s : ℤ) (hs : 3 ≤ s) :
    (9 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s - 3)]

private lemma quartic_d2_squeeze (s t : ℤ) (hs9 : (9 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + s ^ 2 * 4 - 16 = t ^ 2) : False := by
  have hlow : (s ^ 2 + 1) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < (s ^ 2 + 2) ^ 2 := by
    nlinarith
  have ht_sq_pos : 0 < t ^ 2 := by
    nlinarith [sq_nonneg (s ^ 2 + 1)]
  have ht_ne : t ≠ 0 := by
    intro ht0
    simp [ht0] at ht_sq_pos
  rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos
  · have h1 : s ^ 2 + 1 < -t := by
      nlinarith [sq_nonneg (t + s ^ 2 + 1), sq_nonneg s]
    have h2 : -t < s ^ 2 + 2 := by
      nlinarith [sq_nonneg (t + s ^ 2 + 2), sq_nonneg s]
    omega
  · have h1 : s ^ 2 + 1 < t := by
      nlinarith [sq_nonneg (t - s ^ 2 - 2), sq_nonneg s]
    have h2 : t < s ^ 2 + 2 := by
      nlinarith [sq_nonneg (t - s ^ 2 - 1), sq_nonneg s]
    omega

theorem quartic_no_sol_d2 (s t : ℤ) (hcop : Int.gcd s 2 = 1) :
    s ^ 4 + s ^ 2 * 4 - 16 = t ^ 2 → False := by
  intro h
  by_cases hs_neg : s ≤ -3
  · exact quartic_d2_squeeze s t (sq_ge_nine_of_le_neg_three s hs_neg) h
  · by_cases hs_pos : 3 ≤ s
    · exact quartic_d2_squeeze s t (sq_ge_nine_of_three_le s hs_pos) h
    · have hs_small : s = -2 ∨ s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2 := by
        omega
      rcases hs_small with rfl | rfl | rfl | rfl | rfl
      · norm_num at hcop
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · norm_num at hcop
