# ChatGPT Drop File (dm2)

The target is the `d = 7` quartic obstruction:

```lean
theorem quartic_no_sol_d7 (s t : ℤ) (hcop : Int.gcd s 7 = 1) :
    s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2 → False
```

The proof follows the same consecutive-squares squeeze pattern as `scratch/Descent20a4.lean`.  Write `x = s^2`.  For large `|s|`, the expression

```text
x^2 + 49*x - 2401
```

is placed strictly between consecutive squares `(x+k)^2` and `(x+k+1)^2`.  The useful bands are:

- `|s| ≥ 55`: use `k = 24`.
- `32 ≤ |s| ≤ 54`: use `k = 23`.
- `25 ≤ |s| ≤ 31`: use `k = 22`.
- `21 ≤ |s| ≤ 24`: use `k = 21`.
- `18 ≤ |s| ≤ 20`: use `k = 20`.
- `16 ≤ |s| ≤ 17`: use `k = 19`.

The remaining range is `|s| ≤ 15`.  Values with `7 ∣ s` are excluded by `Int.gcd s 7 = 1`; values `|s| ≤ 5` make the right side negative; and the remaining cases are explicit non-squares, each again handled by a small consecutive-squares squeeze.

```lean
import Mathlib

/-!
# The `d = 7` quartic obstruction

We prove that `s^4 + 49*s^2 - 2401 = t^2` has no integer solution when
`Int.gcd s 7 = 1`.
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

private lemma sq_ge_of_le_neg (s N : ℤ) (hN : 0 ≤ N) (hs : s ≤ -N) :
    N ^ 2 ≤ s ^ 2 := by
  have h1 : s + N ≤ 0 := by omega
  have h2 : s - N ≤ 0 := by omega
  have hprod : 0 ≤ (s + N) * (s - N) :=
    mul_nonneg_of_nonpos_of_nonpos h1 h2
  nlinarith

private lemma sq_ge_of_ge (s N : ℤ) (hN : 0 ≤ N) (hs : N ≤ s) :
    N ^ 2 ≤ s ^ 2 := by
  have h1 : 0 ≤ s + N := by omega
  have h2 : 0 ≤ s - N := by omega
  have hprod : 0 ≤ (s + N) * (s - N) := mul_nonneg h1 h2
  nlinarith

private lemma sq_le_of_abs_le (s N : ℤ) (hlo : -N ≤ s) (hhi : s ≤ N) :
    s ^ 2 ≤ N ^ 2 := by
  have h1 : 0 ≤ s + N := by omega
  have h2 : s - N ≤ 0 := by omega
  have hprod : (s + N) * (s - N) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1 h2
  nlinarith

private lemma not_sq_659 (t : ℤ) (h : (659 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 25 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_4831 (t : ℤ) (h : (4831 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 69 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_8129 (t : ℤ) (h : (8129 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 90 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_12499 (t : ℤ) (h : (12499 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 111 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_18169 (t : ℤ) (h : (18169 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 134 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_25391 (t : ℤ) (h : (25391 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 159 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_34441 (t : ℤ) (h : (34441 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 185 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_59249 (t : ℤ) (h : (59249 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 243 (by norm_num) (by nlinarith) (by nlinarith)

private lemma quartic_d7_squeeze (k : ℤ) (s t : ℤ)
    (ha : 0 ≤ s ^ 2 + k)
    (hlow_coeff : 2401 + k ^ 2 < (49 - 2 * k) * s ^ 2)
    (hhigh_coeff : (49 - 2 * (k + 1)) * s ^ 2 < 2401 + (k + 1) ^ 2)
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  have hlow : (s ^ 2 + k) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < ((s ^ 2 + k) + 1) ^ 2 := by
    nlinarith
  exact no_sq_between_consecutive t (s ^ 2 + k) ha hlow hhigh

private lemma quartic_d7_squeeze_24 (s t : ℤ) (hlo : (3025 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 24 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith [sq_nonneg s])
    h

private lemma quartic_d7_squeeze_23 (s t : ℤ)
    (hlo : (1024 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (2916 : ℤ))
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 23 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d7_squeeze_22 (s t : ℤ)
    (hlo : (625 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (961 : ℤ))
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 22 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d7_squeeze_21 (s t : ℤ)
    (hlo : (441 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (576 : ℤ))
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 21 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d7_squeeze_20 (s t : ℤ)
    (hlo : (324 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (400 : ℤ))
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 20 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d7_squeeze_19 (s t : ℤ)
    (hlo : (256 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (289 : ℤ))
    (h : s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2) : False := by
  exact quartic_d7_squeeze 19 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

theorem quartic_no_sol_d7 (s t : ℤ) (hcop : Int.gcd s 7 = 1) :
    s ^ 4 + 49 * s ^ 2 - 2401 = t ^ 2 → False := by
  intro h
  by_cases hs_le_neg55 : s ≤ -55
  · exact quartic_d7_squeeze_24 s t
      (by nlinarith [sq_ge_of_le_neg s 55 (by norm_num) hs_le_neg55]) h
  · by_cases hs_ge55 : 55 ≤ s
    · exact quartic_d7_squeeze_24 s t
        (by nlinarith [sq_ge_of_ge s 55 (by norm_num) hs_ge55]) h
    · by_cases hs_le_neg32 : s ≤ -32
      · exact quartic_d7_squeeze_23 s t
          (by nlinarith [sq_ge_of_le_neg s 32 (by norm_num) hs_le_neg32])
          (by
            have hsabs := sq_le_of_abs_le s 54 (by omega) (by omega)
            nlinarith)
          h
      · by_cases hs_ge32 : 32 ≤ s
        · exact quartic_d7_squeeze_23 s t
            (by nlinarith [sq_ge_of_ge s 32 (by norm_num) hs_ge32])
            (by
              have hsabs := sq_le_of_abs_le s 54 (by omega) (by omega)
              nlinarith)
            h
        · by_cases hs_le_neg25 : s ≤ -25
          · exact quartic_d7_squeeze_22 s t
              (by nlinarith [sq_ge_of_le_neg s 25 (by norm_num) hs_le_neg25])
              (by
                have hsabs := sq_le_of_abs_le s 31 (by omega) (by omega)
                nlinarith)
              h
          · by_cases hs_ge25 : 25 ≤ s
            · exact quartic_d7_squeeze_22 s t
                (by nlinarith [sq_ge_of_ge s 25 (by norm_num) hs_ge25])
                (by
                  have hsabs := sq_le_of_abs_le s 31 (by omega) (by omega)
                  nlinarith)
                h
            · by_cases hs_le_neg21 : s ≤ -21
              · exact quartic_d7_squeeze_21 s t
                  (by nlinarith [sq_ge_of_le_neg s 21 (by norm_num) hs_le_neg21])
                  (by
                    have hsabs := sq_le_of_abs_le s 24 (by omega) (by omega)
                    nlinarith)
                  h
              · by_cases hs_ge21 : 21 ≤ s
                · exact quartic_d7_squeeze_21 s t
                    (by nlinarith [sq_ge_of_ge s 21 (by norm_num) hs_ge21])
                    (by
                      have hsabs := sq_le_of_abs_le s 24 (by omega) (by omega)
                      nlinarith)
                    h
                · by_cases hs_le_neg18 : s ≤ -18
                  · exact quartic_d7_squeeze_20 s t
                      (by nlinarith [sq_ge_of_le_neg s 18 (by norm_num) hs_le_neg18])
                      (by
                        have hsabs := sq_le_of_abs_le s 20 (by omega) (by omega)
                        nlinarith)
                      h
                  · by_cases hs_ge18 : 18 ≤ s
                    · exact quartic_d7_squeeze_20 s t
                        (by nlinarith [sq_ge_of_ge s 18 (by norm_num) hs_ge18])
                        (by
                          have hsabs := sq_le_of_abs_le s 20 (by omega) (by omega)
                          nlinarith)
                        h
                    · by_cases hs_le_neg16 : s ≤ -16
                      · exact quartic_d7_squeeze_19 s t
                          (by nlinarith [sq_ge_of_le_neg s 16 (by norm_num) hs_le_neg16])
                          (by
                            have hsabs := sq_le_of_abs_le s 17 (by omega) (by omega)
                            nlinarith)
                          h
                      · by_cases hs_ge16 : 16 ≤ s
                        · exact quartic_d7_squeeze_19 s t
                            (by nlinarith [sq_ge_of_ge s 16 (by norm_num) hs_ge16])
                            (by
                              have hsabs := sq_le_of_abs_le s 17 (by omega) (by omega)
                              nlinarith)
                            h
                        · have hs_small :
                              s = -15 ∨ s = -14 ∨ s = -13 ∨ s = -12 ∨ s = -11 ∨
                              s = -10 ∨ s = -9 ∨ s = -8 ∨ s = -7 ∨ s = -6 ∨
                              s = -5 ∨ s = -4 ∨ s = -3 ∨ s = -2 ∨ s = -1 ∨
                              s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨
                              s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨
                              s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨
                              s = 15 := by
                            omega
                          rcases hs_small with rfl | rfl | rfl | rfl | rfl |
                            rfl | rfl | rfl | rfl | rfl |
                            rfl | rfl | rfl | rfl | rfl |
                            rfl | rfl | rfl | rfl | rfl |
                            rfl | rfl | rfl | rfl | rfl |
                            rfl | rfl | rfl | rfl | rfl | rfl
                          · norm_num at h
                            exact not_sq_59249 t h
                          · norm_num at hcop
                          · norm_num at h
                            exact not_sq_34441 t h
                          · norm_num at h
                            exact not_sq_25391 t h
                          · norm_num at h
                            exact not_sq_18169 t h
                          · norm_num at h
                            exact not_sq_12499 t h
                          · norm_num at h
                            exact not_sq_8129 t h
                          · norm_num at h
                            exact not_sq_4831 t h
                          · norm_num at hcop
                          · norm_num at h
                            exact not_sq_659 t h
                          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
                            norm_num at h
                            nlinarith
                          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
                            norm_num at h
                            nlinarith
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
                          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
                            norm_num at h
                            nlinarith
                          · have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
                            norm_num at h
                            nlinarith
                          · norm_num at h
                            exact not_sq_659 t h
                          · norm_num at hcop
                          · norm_num at h
                            exact not_sq_4831 t h
                          · norm_num at h
                            exact not_sq_8129 t h
                          · norm_num at h
                            exact not_sq_12499 t h
                          · norm_num at h
                            exact not_sq_18169 t h
                          · norm_num at h
                            exact not_sq_25391 t h
                          · norm_num at h
                            exact not_sq_34441 t h
                          · norm_num at hcop
                          · norm_num at h
                            exact not_sq_59249 t h
```
