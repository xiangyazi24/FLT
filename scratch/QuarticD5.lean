import Mathlib

/-!
# The `d = 5` quartic obstruction

We prove that `s^4 + 25*s^2 - 625 = t^2` has no integer solution when
`Int.gcd s 5 = 1`.
-/

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

private lemma not_sq_31 (t : ℤ) (h : (31 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 5 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_1571 (t : ℤ) (h : (1571 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 39 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_3001 (t : ℤ) (h : (3001 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 54 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_5071 (t : ℤ) (h : (5071 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 71 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_7961 (t : ℤ) (h : (7961 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 89 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_17041 (t : ℤ) (h : (17041 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 130 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_23711 (t : ℤ) (h : (23711 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 153 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_32161 (t : ℤ) (h : (32161 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 179 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_42691 (t : ℤ) (h : (42691 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 206 (by norm_num) (by nlinarith) (by nlinarith)

private lemma sq_ge_249_of_le_neg_sixteen (s : ℤ) (hs : s ≤ -16) :
    (249 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s + 16)]

private lemma sq_ge_249_of_sixteen_le (s : ℤ) (hs : 16 ≤ s) :
    (249 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s - 16)]

private lemma sq_lt_769_of_neg27_le_of_le_neg16 (s : ℤ)
    (hlo : -27 ≤ s) (hhi : s ≤ -16) : s ^ 2 < (769 : ℤ) := by
  have h1 : 0 ≤ s + 27 := by omega
  have h2 : s + 16 ≤ 0 := by omega
  have hprod : (s + 27) * (s + 16) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1 h2
  nlinarith

private lemma sq_lt_769_of_sixteen_le_of_le27 (s : ℤ)
    (hlo : 16 ≤ s) (hhi : s ≤ 27) : s ^ 2 < (769 : ℤ) := by
  have h1 : 0 ≤ s - 16 := by omega
  have h2 : s - 27 ≤ 0 := by omega
  have hprod : (s - 16) * (s - 27) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1 h2
  nlinarith

private lemma sq_ge_784_of_le_neg_twentyeight (s : ℤ) (hs : s ≤ -28) :
    (784 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s + 28)]

private lemma sq_ge_784_of_twentyeight_le (s : ℤ) (hs : 28 ≤ s) :
    (784 : ℤ) ≤ s ^ 2 := by
  nlinarith [sq_nonneg (s - 28)]

private lemma quartic_d5_mid_squeeze (s t : ℤ)
    (hlo : (249 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 < (769 : ℤ))
    (h : s ^ 4 + 25 * s ^ 2 - 625 = t ^ 2) : False := by
  have hlow : (s ^ 2 + 11) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < ((s ^ 2 + 11) + 1) ^ 2 := by
    nlinarith
  exact no_sq_between_consecutive t (s ^ 2 + 11)
    (by nlinarith [sq_nonneg s]) hlow hhigh

private lemma quartic_d5_large_squeeze (s t : ℤ)
    (hs784 : (784 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + 25 * s ^ 2 - 625 = t ^ 2) : False := by
  have hlow : (s ^ 2 + 12) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < ((s ^ 2 + 12) + 1) ^ 2 := by
    nlinarith [sq_nonneg s]
  exact no_sq_between_consecutive t (s ^ 2 + 12)
    (by nlinarith [sq_nonneg s]) hlow hhigh

theorem quartic_no_sol_d5 (s t : ℤ) (hcop : Int.gcd s 5 = 1) :
    s ^ 4 + 25 * s ^ 2 - 625 = t ^ 2 → False := by
  intro h
  by_cases hs_le_neg28 : s ≤ -28
  · exact quartic_d5_large_squeeze s t
      (sq_ge_784_of_le_neg_twentyeight s hs_le_neg28) h
  · by_cases hs_ge_28 : 28 ≤ s
    · exact quartic_d5_large_squeeze s t
        (sq_ge_784_of_twentyeight_le s hs_ge_28) h
    · by_cases hs_le_neg16 : s ≤ -16
      · exact quartic_d5_mid_squeeze s t
          (sq_ge_249_of_le_neg_sixteen s hs_le_neg16)
          (sq_lt_769_of_neg27_le_of_le_neg16 s (by omega) hs_le_neg16) h
      · by_cases hs_ge_16 : 16 ≤ s
        · exact quartic_d5_mid_squeeze s t
            (sq_ge_249_of_sixteen_le s hs_ge_16)
            (sq_lt_769_of_sixteen_le_of_le27 s hs_ge_16 (by omega)) h
        · have hs_small :
              s = -15 ∨ s = -14 ∨ s = -13 ∨ s = -12 ∨ s = -11 ∨
              s = -10 ∨ s = -9 ∨ s = -8 ∨ s = -7 ∨ s = -6 ∨
              s = -5 ∨ s = -4 ∨ s = -3 ∨ s = -2 ∨ s = -1 ∨
              s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨
              s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨
              s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 := by
            omega
          rcases hs_small with rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl
          · norm_num at hcop
          · norm_num at h
            exact not_sq_42691 t h
          · norm_num at h
            exact not_sq_32161 t h
          · norm_num at h
            exact not_sq_23711 t h
          · norm_num at h
            exact not_sq_17041 t h
          · norm_num at hcop
          · norm_num at h
            exact not_sq_7961 t h
          · norm_num at h
            exact not_sq_5071 t h
          · norm_num at h
            exact not_sq_3001 t h
          · norm_num at h
            exact not_sq_1571 t h
          · norm_num at hcop
          · norm_num at h
            exact not_sq_31 t h
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
          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
            norm_num at h
            nlinarith
          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
            norm_num at h
            nlinarith
          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
            norm_num at h
            nlinarith
          · norm_num at h
            exact not_sq_31 t h
          · norm_num at hcop
          · norm_num at h
            exact not_sq_1571 t h
          · norm_num at h
            exact not_sq_3001 t h
          · norm_num at h
            exact not_sq_5071 t h
          · norm_num at h
            exact not_sq_7961 t h
          · norm_num at hcop
          · norm_num at h
            exact not_sq_17041 t h
          · norm_num at h
            exact not_sq_23711 t h
          · norm_num at h
            exact not_sq_32161 t h
          · norm_num at h
            exact not_sq_42691 t h
          · norm_num at hcop
