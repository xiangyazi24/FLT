import Mathlib

/-!
# The `d = 3` quartic obstruction

Task theorem:

```
theorem quartic_no_sol_d3 (s t : ℤ) (hcop : Int.gcd s 3 = 1) :
    s ^ 4 + s ^ 2 * 9 - 81 = t ^ 2 → False
```

For `|s| ≥ 10`, use the same consecutive-squares squeeze pattern as
`scratch/Descent20a4.lean`:

```
(s^2 + 4)^2 < t^2 < (s^2 + 5)^2.
```

The remaining values `-9 ≤ s ≤ 9` are finite.  The gcd hypothesis excludes the
multiples of `3`, including the genuine `s = ±3` exceptional cases for the raw
equation; the other small values are either negative right sides or lie strictly
between consecutive squares.
-/

private lemma sq_ge_hundred_of_le_neg_ten (s : ℤ) (hs : s ≤ -10) :
    (100 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s + 10)]

private lemma sq_ge_hundred_of_ten_le (s : ℤ) (hs : 10 ≤ s) :
    (100 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s - 10)]

private lemma lt_neg_of_sq_lt_sq_of_nonneg_of_neg {a t : ℤ}
    (ha : 0 ≤ a) (ht : t < 0) (h : a ^ 2 < t ^ 2) : a < -t := by
  by_contra hnot
  have hta_nonneg : 0 ≤ t + a := by omega
  have htm_nonpos : t - a ≤ 0 := by omega
  have hprod : (t - a) * (t + a) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg htm_nonpos hta_nonneg
  have hdiff : t ^ 2 - a ^ 2 ≤ 0 := by
    calc
      t ^ 2 - a ^ 2 = (t - a) * (t + a) := by ring
      _ ≤ 0 := hprod
  nlinarith

private lemma lt_of_sq_lt_sq_of_nonneg_of_pos {a t : ℤ}
    (ha : 0 ≤ a) (ht : 0 < t) (h : a ^ 2 < t ^ 2) : a < t := by
  by_contra hnot
  have htm_nonpos : t - a ≤ 0 := by omega
  have htp_nonneg : 0 ≤ t + a := by omega
  have hprod : (t - a) * (t + a) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg htm_nonpos htp_nonneg
  have hdiff : t ^ 2 - a ^ 2 ≤ 0 := by
    calc
      t ^ 2 - a ^ 2 = (t - a) * (t + a) := by ring
      _ ≤ 0 := hprod
  nlinarith

private lemma neg_lt_of_sq_lt_sq_of_nonneg_of_neg {b t : ℤ}
    (hb : 0 ≤ b) (ht : t < 0) (h : t ^ 2 < b ^ 2) : -t < b := by
  by_contra hnot
  have htb_nonpos : t + b ≤ 0 := by omega
  have htm_nonpos : t - b ≤ 0 := by omega
  have hprod : 0 ≤ (t - b) * (t + b) :=
    mul_nonneg_of_nonpos_of_nonpos htm_nonpos htb_nonpos
  have hdiff : 0 ≤ t ^ 2 - b ^ 2 := by
    calc
      0 ≤ (t - b) * (t + b) := hprod
      _ = t ^ 2 - b ^ 2 := by ring
  nlinarith

private lemma lt_of_sq_lt_sq_of_nonneg_of_pos_upper {b t : ℤ}
    (hb : 0 ≤ b) (ht : 0 < t) (h : t ^ 2 < b ^ 2) : t < b := by
  by_contra hnot
  have htm_nonneg : 0 ≤ t - b := by omega
  have htp_nonneg : 0 ≤ t + b := by omega
  have hprod : 0 ≤ (t - b) * (t + b) :=
    mul_nonneg htm_nonneg htp_nonneg
  have hdiff : 0 ≤ t ^ 2 - b ^ 2 := by
    calc
      0 ≤ (t - b) * (t + b) := hprod
      _ = t ^ 2 - b ^ 2 := by ring
  nlinarith

private lemma no_sq_between_consecutive (t a : ℤ) (ha : 0 ≤ a)
    (hlow : a ^ 2 < t ^ 2) (hhigh : t ^ 2 < (a + 1) ^ 2) : False := by
  have ht_sq_pos : 0 < t ^ 2 := by
    nlinarith [sq_nonneg a]
  have ht_ne : t ≠ 0 := by
    intro ht0
    simp [ht0] at ht_sq_pos
  have ha1 : 0 ≤ a + 1 := by omega
  rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos
  · have h1 : a < -t := lt_neg_of_sq_lt_sq_of_nonneg_of_neg ha ht_neg hlow
    have h2 : -t < a + 1 := neg_lt_of_sq_lt_sq_of_nonneg_of_neg ha1 ht_neg hhigh
    omega
  · have h1 : a < t := lt_of_sq_lt_sq_of_nonneg_of_pos ha ht_pos hlow
    have h2 : t < a + 1 := lt_of_sq_lt_sq_of_nonneg_of_pos_upper ha1 ht_pos hhigh
    omega

private lemma not_sq_319 (t : ℤ) (h : (319 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 17 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_769 (t : ℤ) (h : (769 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 27 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_2761 (t : ℤ) (h : (2761 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 52 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_4591 (t : ℤ) (h : (4591 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 67 (by norm_num) (by nlinarith) (by nlinarith)

private lemma quartic_d3_squeeze (s t : ℤ) (hs100 : (100 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + s ^ 2 * 9 - 81 = t ^ 2) : False := by
  have hlow : (s ^ 2 + 4) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < ((s ^ 2 + 4) + 1) ^ 2 := by
    nlinarith [sq_nonneg s]
  exact no_sq_between_consecutive t (s ^ 2 + 4)
    (by nlinarith [sq_nonneg s]) hlow hhigh

theorem quartic_no_sol_d3 (s t : ℤ) (hcop : Int.gcd s 3 = 1) :
    s ^ 4 + s ^ 2 * 9 - 81 = t ^ 2 → False := by
  intro h
  by_cases hs_neg : s ≤ -10
  · exact quartic_d3_squeeze s t (sq_ge_hundred_of_le_neg_ten s hs_neg) h
  · by_cases hs_pos : 10 ≤ s
    · exact quartic_d3_squeeze s t (sq_ge_hundred_of_ten_le s hs_pos) h
    · have hs_small :
          s = -9 ∨ s = -8 ∨ s = -7 ∨ s = -6 ∨ s = -5 ∨
          s = -4 ∨ s = -3 ∨ s = -2 ∨ s = -1 ∨ s = 0 ∨
          s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
          s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 := by
        omega
      rcases hs_small with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · norm_num at hcop
      · norm_num at h
        exact not_sq_4591 t h
      · norm_num at h
        exact not_sq_2761 t h
      · norm_num at hcop
      · norm_num at h
        exact not_sq_769 t h
      · norm_num at h
        exact not_sq_319 t h
      · norm_num at hcop
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · norm_num at hcop
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
        norm_num at h
        nlinarith
      · norm_num at hcop
      · norm_num at h
        exact not_sq_319 t h
      · norm_num at h
        exact not_sq_769 t h
      · norm_num at hcop
      · norm_num at h
        exact not_sq_2761 t h
      · norm_num at h
        exact not_sq_4591 t h
      · norm_num at hcop

/-- Same result in the commuted `9 * s^2` spelling. -/
theorem quartic_no_sol_d3_left_mul (s t : ℤ) (hcop : Int.gcd s 3 = 1) :
    s ^ 4 + 9 * s ^ 2 - 81 = t ^ 2 → False := by
  intro h
  exact quartic_no_sol_d3 s t hcop (by nlinarith)
