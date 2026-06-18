import Mathlib

/-!
# The `d = 2` quartic obstruction

We prove that

` s^4 + 4*s^2 - 16 = t^2 `

has no integer solution when `Int.gcd s 2 = 1`.  The only use of the gcd
hypothesis is to exclude the two exceptional values `s = ±2`; for `|s| ≥ 3`
the proof is the squeeze from `scratch/Descent20a4.lean`:

`(s^2 + 1)^2 < t^2 < (s^2 + 2)^2`,

hence `s^2 + 1 < |t| < s^2 + 2`, impossible over the integers.
-/

private lemma quartic_d2_squeeze (s t : ℤ) (hs9 : (9 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + s ^ 2 * 4 - 16 = t ^ 2) : False := by
  have hlow : (s ^ 2 + 1) ^ 2 < t ^ 2 := by nlinarith
  have hhigh : t ^ 2 < (s ^ 2 + 2) ^ 2 := by nlinarith
  have ht_pos : 0 < t ^ 2 := by nlinarith [sq_nonneg (s ^ 2 + 1)]
  have ht_ne : t ≠ 0 := by
    intro ht0
    simp [ht0] at ht_pos
  rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos'
  · have h1 : s ^ 2 + 1 < -t := by
      nlinarith [sq_nonneg (t + s ^ 2 + 1)]
    have h2 : -t < s ^ 2 + 2 := by
      nlinarith [sq_nonneg (t + s ^ 2 + 2)]
    omega
  · have h1 : s ^ 2 + 1 < t := by
      nlinarith [sq_nonneg (t - s ^ 2 - 2)]
    have h2 : t < s ^ 2 + 2 := by
      nlinarith [sq_nonneg (t - s ^ 2 - 1)]
    omega

theorem quartic_no_sol_d2 (s t : ℤ) (hcop : Int.gcd s 2 = 1) :
    s ^ 4 + s ^ 2 * 4 - 16 = t ^ 2 → False := by
  intro h
  by_cases hs_neg : s ≤ -3
  · exact quartic_d2_squeeze s t (by nlinarith) h
  · by_cases hs_pos : 3 ≤ s
    · exact quartic_d2_squeeze s t (by nlinarith) h
    · have hs_small : s = -2 ∨ s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2 := by omega
      rcases hs_small with rfl | rfl | rfl | rfl | rfl
      · norm_num at hcop
      · have ht_nonneg := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg := sq_nonneg t
        norm_num at h
        nlinarith
      · norm_num at hcop
