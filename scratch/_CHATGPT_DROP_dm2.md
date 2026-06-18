# ChatGPT Drop File (dm2)

The target is the `d = 9` quartic obstruction:

```lean
theorem quartic_no_sol_d9 (s t : ℤ) (hcop : Int.gcd s 9 = 1) :
    s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2 → False
```

Write `x = s^2`.  The expression is

```text
x^2 + 81*x - 6561.
```

For `|s| ≥ 10`, it is squeezed between consecutive squares `(x+k)^2` and `(x+k+1)^2`, with `k` depending on the size range.  The bands used below are:

- `|s| ≥ 91`: `k = 40`.
- `52 ≤ |s| ≤ 90`: `k = 39`.
- `41 ≤ |s| ≤ 51`: `k = 38`.
- `34 ≤ |s| ≤ 40`: `k = 37`.
- `30 ≤ |s| ≤ 33`: `k = 36`.
- `27 ≤ |s| ≤ 29`: `k = 35`.
- `25 ≤ |s| ≤ 26`: `k = 34`.
- `23 ≤ |s| ≤ 24`: `k = 33`.
- `|s| = 22`: `k = 32`.
- `20 ≤ |s| ≤ 21`: `k = 31`.
- `|s| = 19`: `k = 30`.
- `|s| = 18`: `k = 29`.
- `|s| = 17`: `k = 27`.
- `|s| = 16`: `k = 26`.
- `|s| = 15`: `k = 24`.
- `|s| = 14`: `k = 22`.
- `|s| = 13`: `k = 19`.
- `|s| = 12`: `k = 16`.
- `|s| = 11`: `k = 12`.
- `|s| = 10`: `k = 7`.

For `|s| ≤ 7`, the right side is negative.  For `s = ±8`, the value is `2719`, strictly between `52^2` and `53^2`.  For `s = ±9`, the raw equation actually has `t^2 = 81^2`, and this is exactly where `Int.gcd s 9 = 1` is used.

```lean
import Mathlib

/-!
# The `d = 9` quartic obstruction

We prove that `s^4 + 81*s^2 - 6561 = t^2` has no integer solution when
`Int.gcd s 9 = 1`, equivalently when `s` is not divisible by `3`.
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

private lemma quartic_d9_negative (s t : ℤ) (hs49 : s ^ 2 ≤ (49 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  have ht_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hneg : s ^ 4 + 81 * s ^ 2 - 6561 < 0 := by
    nlinarith [sq_nonneg s]
  nlinarith

private lemma not_sq_2719 (t : ℤ) (h : (2719 : ℤ) = t ^ 2) : False := by
  exact no_sq_between_consecutive t 52 (by norm_num) (by nlinarith) (by nlinarith)

private lemma quartic_d9_squeeze (k : ℤ) (s t : ℤ)
    (ha : 0 ≤ s ^ 2 + k)
    (hlow_coeff : 6561 + k ^ 2 < (81 - 2 * k) * s ^ 2)
    (hhigh_coeff : (81 - 2 * (k + 1)) * s ^ 2 < 6561 + (k + 1) ^ 2)
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  have hlow : (s ^ 2 + k) ^ 2 < t ^ 2 := by
    nlinarith
  have hhigh : t ^ 2 < ((s ^ 2 + k) + 1) ^ 2 := by
    nlinarith
  exact no_sq_between_consecutive t (s ^ 2 + k) ha hlow hhigh

private lemma quartic_d9_squeeze_40 (s t : ℤ) (hlo : (8281 : ℤ) ≤ s ^ 2)
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 40 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith [sq_nonneg s])
    h

private lemma quartic_d9_squeeze_39 (s t : ℤ)
    (hlo : (2704 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (8100 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 39 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_38 (s t : ℤ)
    (hlo : (1681 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (2601 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 38 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_37 (s t : ℤ)
    (hlo : (1156 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (1600 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 37 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_36 (s t : ℤ)
    (hlo : (900 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (1089 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 36 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_35 (s t : ℤ)
    (hlo : (729 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (841 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 35 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_34 (s t : ℤ)
    (hlo : (625 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (676 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 34 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_33 (s t : ℤ)
    (hlo : (529 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (576 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 33 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_32 (s t : ℤ)
    (hlo : (484 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (484 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 32 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_31 (s t : ℤ)
    (hlo : (400 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (441 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 31 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_30 (s t : ℤ)
    (hlo : (361 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (361 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 30 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_29 (s t : ℤ)
    (hlo : (324 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (324 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 29 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_27 (s t : ℤ)
    (hlo : (289 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (289 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 27 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_26 (s t : ℤ)
    (hlo : (256 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (256 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 26 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_24 (s t : ℤ)
    (hlo : (225 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (225 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 24 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_22 (s t : ℤ)
    (hlo : (196 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (196 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 22 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_19 (s t : ℤ)
    (hlo : (169 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (169 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 19 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_16 (s t : ℤ)
    (hlo : (144 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (144 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 16 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_12 (s t : ℤ)
    (hlo : (121 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (121 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 12 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

private lemma quartic_d9_squeeze_7 (s t : ℤ)
    (hlo : (100 : ℤ) ≤ s ^ 2) (hhi : s ^ 2 ≤ (100 : ℤ))
    (h : s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2) : False := by
  exact quartic_d9_squeeze 7 s t
    (by nlinarith [sq_nonneg s])
    (by nlinarith)
    (by nlinarith)
    h

theorem quartic_no_sol_d9 (s t : ℤ) (hcop : Int.gcd s 9 = 1) :
    s ^ 4 + 81 * s ^ 2 - 6561 = t ^ 2 → False := by
  intro h
  by_cases hs_le_neg91 : s ≤ -91
  · exact quartic_d9_squeeze_40 s t
      (by nlinarith [sq_ge_of_le_neg s 91 (by norm_num) hs_le_neg91]) h
  · by_cases hs_ge91 : 91 ≤ s
    · exact quartic_d9_squeeze_40 s t
        (by nlinarith [sq_ge_of_ge s 91 (by norm_num) hs_ge91]) h
    · by_cases hs_le_neg52 : s ≤ -52
      · exact quartic_d9_squeeze_39 s t
          (by nlinarith [sq_ge_of_le_neg s 52 (by norm_num) hs_le_neg52])
          (by
            have hsabs := sq_le_of_abs_le s 90 (by omega) (by omega)
            nlinarith)
          h
      · by_cases hs_ge52 : 52 ≤ s
        · exact quartic_d9_squeeze_39 s t
            (by nlinarith [sq_ge_of_ge s 52 (by norm_num) hs_ge52])
            (by
              have hsabs := sq_le_of_abs_le s 90 (by omega) (by omega)
              nlinarith)
            h
        · by_cases hs_le_neg41 : s ≤ -41
          · exact quartic_d9_squeeze_38 s t
              (by nlinarith [sq_ge_of_le_neg s 41 (by norm_num) hs_le_neg41])
              (by
                have hsabs := sq_le_of_abs_le s 51 (by omega) (by omega)
                nlinarith)
              h
          · by_cases hs_ge41 : 41 ≤ s
            · exact quartic_d9_squeeze_38 s t
                (by nlinarith [sq_ge_of_ge s 41 (by norm_num) hs_ge41])
                (by
                  have hsabs := sq_le_of_abs_le s 51 (by omega) (by omega)
                  nlinarith)
                h
            · by_cases hs_le_neg34 : s ≤ -34
              · exact quartic_d9_squeeze_37 s t
                  (by nlinarith [sq_ge_of_le_neg s 34 (by norm_num) hs_le_neg34])
                  (by
                    have hsabs := sq_le_of_abs_le s 40 (by omega) (by omega)
                    nlinarith)
                  h
              · by_cases hs_ge34 : 34 ≤ s
                · exact quartic_d9_squeeze_37 s t
                    (by nlinarith [sq_ge_of_ge s 34 (by norm_num) hs_ge34])
                    (by
                      have hsabs := sq_le_of_abs_le s 40 (by omega) (by omega)
                      nlinarith)
                    h
                · by_cases hs_le_neg30 : s ≤ -30
                  · exact quartic_d9_squeeze_36 s t
                      (by nlinarith [sq_ge_of_le_neg s 30 (by norm_num) hs_le_neg30])
                      (by
                        have hsabs := sq_le_of_abs_le s 33 (by omega) (by omega)
                        nlinarith)
                      h
                  · by_cases hs_ge30 : 30 ≤ s
                    · exact quartic_d9_squeeze_36 s t
                        (by nlinarith [sq_ge_of_ge s 30 (by norm_num) hs_ge30])
                        (by
                          have hsabs := sq_le_of_abs_le s 33 (by omega) (by omega)
                          nlinarith)
                        h
                    · by_cases hs_le_neg27 : s ≤ -27
                      · exact quartic_d9_squeeze_35 s t
                          (by nlinarith [sq_ge_of_le_neg s 27 (by norm_num) hs_le_neg27])
                          (by
                            have hsabs := sq_le_of_abs_le s 29 (by omega) (by omega)
                            nlinarith)
                          h
                      · by_cases hs_ge27 : 27 ≤ s
                        · exact quartic_d9_squeeze_35 s t
                            (by nlinarith [sq_ge_of_ge s 27 (by norm_num) hs_ge27])
                            (by
                              have hsabs := sq_le_of_abs_le s 29 (by omega) (by omega)
                              nlinarith)
                            h
                        · by_cases hs_le_neg25 : s ≤ -25
                          · exact quartic_d9_squeeze_34 s t
                              (by nlinarith [sq_ge_of_le_neg s 25 (by norm_num) hs_le_neg25])
                              (by
                                have hsabs := sq_le_of_abs_le s 26 (by omega) (by omega)
                                nlinarith)
                              h
                          · by_cases hs_ge25 : 25 ≤ s
                            · exact quartic_d9_squeeze_34 s t
                                (by nlinarith [sq_ge_of_ge s 25 (by norm_num) hs_ge25])
                                (by
                                  have hsabs := sq_le_of_abs_le s 26 (by omega) (by omega)
                                  nlinarith)
                                h
                            · by_cases hs_le_neg23 : s ≤ -23
                              · exact quartic_d9_squeeze_33 s t
                                  (by nlinarith [sq_ge_of_le_neg s 23 (by norm_num) hs_le_neg23])
                                  (by
                                    have hsabs := sq_le_of_abs_le s 24 (by omega) (by omega)
                                    nlinarith)
                                  h
                              · by_cases hs_ge23 : 23 ≤ s
                                · exact quartic_d9_squeeze_33 s t
                                    (by nlinarith [sq_ge_of_ge s 23 (by norm_num) hs_ge23])
                                    (by
                                      have hsabs := sq_le_of_abs_le s 24 (by omega) (by omega)
                                      nlinarith)
                                    h
                                · by_cases hs_le_neg22 : s ≤ -22
                                  · exact quartic_d9_squeeze_32 s t
                                      (by nlinarith [sq_ge_of_le_neg s 22 (by norm_num) hs_le_neg22])
                                      (by
                                        have hsabs := sq_le_of_abs_le s 22 (by omega) (by omega)
                                        nlinarith)
                                      h
                                  · by_cases hs_ge22 : 22 ≤ s
                                    · exact quartic_d9_squeeze_32 s t
                                        (by nlinarith [sq_ge_of_ge s 22 (by norm_num) hs_ge22])
                                        (by
                                          have hsabs := sq_le_of_abs_le s 22 (by omega) (by omega)
                                          nlinarith)
                                        h
                                    · by_cases hs_le_neg20 : s ≤ -20
                                      · exact quartic_d9_squeeze_31 s t
                                          (by nlinarith [sq_ge_of_le_neg s 20 (by norm_num) hs_le_neg20])
                                          (by
                                            have hsabs := sq_le_of_abs_le s 21 (by omega) (by omega)
                                            nlinarith)
                                          h
                                      · by_cases hs_ge20 : 20 ≤ s
                                        · exact quartic_d9_squeeze_31 s t
                                            (by nlinarith [sq_ge_of_ge s 20 (by norm_num) hs_ge20])
                                            (by
                                              have hsabs := sq_le_of_abs_le s 21 (by omega) (by omega)
                                              nlinarith)
                                            h
                                        · by_cases hs_le_neg19 : s ≤ -19
                                          · exact quartic_d9_squeeze_30 s t
                                              (by nlinarith [sq_ge_of_le_neg s 19 (by norm_num) hs_le_neg19])
                                              (by
                                                have hsabs := sq_le_of_abs_le s 19 (by omega) (by omega)
                                                nlinarith)
                                              h
                                          · by_cases hs_ge19 : 19 ≤ s
                                            · exact quartic_d9_squeeze_30 s t
                                                (by nlinarith [sq_ge_of_ge s 19 (by norm_num) hs_ge19])
                                                (by
                                                  have hsabs := sq_le_of_abs_le s 19 (by omega) (by omega)
                                                  nlinarith)
                                                h
                                            · by_cases hs_le_neg18 : s ≤ -18
                                              · exact quartic_d9_squeeze_29 s t
                                                  (by nlinarith [sq_ge_of_le_neg s 18 (by norm_num) hs_le_neg18])
                                                  (by
                                                    have hsabs := sq_le_of_abs_le s 18 (by omega) (by omega)
                                                    nlinarith)
                                                  h
                                              · by_cases hs_ge18 : 18 ≤ s
                                                · exact quartic_d9_squeeze_29 s t
                                                    (by nlinarith [sq_ge_of_ge s 18 (by norm_num) hs_ge18])
                                                    (by
                                                      have hsabs := sq_le_of_abs_le s 18 (by omega) (by omega)
                                                      nlinarith)
                                                    h
                                                · by_cases hs_le_neg17 : s ≤ -17
                                                  · exact quartic_d9_squeeze_27 s t
                                                      (by nlinarith [sq_ge_of_le_neg s 17 (by norm_num) hs_le_neg17])
                                                      (by
                                                        have hsabs := sq_le_of_abs_le s 17 (by omega) (by omega)
                                                        nlinarith)
                                                      h
                                                  · by_cases hs_ge17 : 17 ≤ s
                                                    · exact quartic_d9_squeeze_27 s t
                                                        (by nlinarith [sq_ge_of_ge s 17 (by norm_num) hs_ge17])
                                                        (by
                                                          have hsabs := sq_le_of_abs_le s 17 (by omega) (by omega)
                                                          nlinarith)
                                                        h
                                                    · by_cases hs_le_neg16 : s ≤ -16
                                                      · exact quartic_d9_squeeze_26 s t
                                                          (by nlinarith [sq_ge_of_le_neg s 16 (by norm_num) hs_le_neg16])
                                                          (by
                                                            have hsabs := sq_le_of_abs_le s 16 (by omega) (by omega)
                                                            nlinarith)
                                                          h
                                                      · by_cases hs_ge16 : 16 ≤ s
                                                        · exact quartic_d9_squeeze_26 s t
                                                            (by nlinarith [sq_ge_of_ge s 16 (by norm_num) hs_ge16])
                                                            (by
                                                              have hsabs := sq_le_of_abs_le s 16 (by omega) (by omega)
                                                              nlinarith)
                                                            h
                                                        · by_cases hs_le_neg15 : s ≤ -15
                                                          · exact quartic_d9_squeeze_24 s t
                                                              (by nlinarith [sq_ge_of_le_neg s 15 (by norm_num) hs_le_neg15])
                                                              (by
                                                                have hsabs := sq_le_of_abs_le s 15 (by omega) (by omega)
                                                                nlinarith)
                                                              h
                                                          · by_cases hs_ge15 : 15 ≤ s
                                                            · exact quartic_d9_squeeze_24 s t
                                                                (by nlinarith [sq_ge_of_ge s 15 (by norm_num) hs_ge15])
                                                                (by
                                                                  have hsabs := sq_le_of_abs_le s 15 (by omega) (by omega)
                                                                  nlinarith)
                                                                h
                                                            · by_cases hs_le_neg14 : s ≤ -14
                                                              · exact quartic_d9_squeeze_22 s t
                                                                  (by nlinarith [sq_ge_of_le_neg s 14 (by norm_num) hs_le_neg14])
                                                                  (by
                                                                    have hsabs := sq_le_of_abs_le s 14 (by omega) (by omega)
                                                                    nlinarith)
                                                                  h
                                                              · by_cases hs_ge14 : 14 ≤ s
                                                                · exact quartic_d9_squeeze_22 s t
                                                                    (by nlinarith [sq_ge_of_ge s 14 (by norm_num) hs_ge14])
                                                                    (by
                                                                      have hsabs := sq_le_of_abs_le s 14 (by omega) (by omega)
                                                                      nlinarith)
                                                                    h
                                                                · by_cases hs_le_neg13 : s ≤ -13
                                                                  · exact quartic_d9_squeeze_19 s t
                                                                      (by nlinarith [sq_ge_of_le_neg s 13 (by norm_num) hs_le_neg13])
                                                                      (by
                                                                        have hsabs := sq_le_of_abs_le s 13 (by omega) (by omega)
                                                                        nlinarith)
                                                                      h
                                                                  · by_cases hs_ge13 : 13 ≤ s
                                                                    · exact quartic_d9_squeeze_19 s t
                                                                        (by nlinarith [sq_ge_of_ge s 13 (by norm_num) hs_ge13])
                                                                        (by
                                                                          have hsabs := sq_le_of_abs_le s 13 (by omega) (by omega)
                                                                          nlinarith)
                                                                        h
                                                                    · by_cases hs_le_neg12 : s ≤ -12
                                                                      · exact quartic_d9_squeeze_16 s t
                                                                          (by nlinarith [sq_ge_of_le_neg s 12 (by norm_num) hs_le_neg12])
                                                                          (by
                                                                            have hsabs := sq_le_of_abs_le s 12 (by omega) (by omega)
                                                                            nlinarith)
                                                                          h
                                                                      · by_cases hs_ge12 : 12 ≤ s
                                                                        · exact quartic_d9_squeeze_16 s t
                                                                            (by nlinarith [sq_ge_of_ge s 12 (by norm_num) hs_ge12])
                                                                            (by
                                                                              have hsabs := sq_le_of_abs_le s 12 (by omega) (by omega)
                                                                              nlinarith)
                                                                            h
                                                                        · by_cases hs_le_neg11 : s ≤ -11
                                                                          · exact quartic_d9_squeeze_12 s t
                                                                              (by nlinarith [sq_ge_of_le_neg s 11 (by norm_num) hs_le_neg11])
                                                                              (by
                                                                                have hsabs := sq_le_of_abs_le s 11 (by omega) (by omega)
                                                                                nlinarith)
                                                                              h
                                                                          · by_cases hs_ge11 : 11 ≤ s
                                                                            · exact quartic_d9_squeeze_12 s t
                                                                                (by nlinarith [sq_ge_of_ge s 11 (by norm_num) hs_ge11])
                                                                                (by
                                                                                  have hsabs := sq_le_of_abs_le s 11 (by omega) (by omega)
                                                                                  nlinarith)
                                                                                h
                                                                            · by_cases hs_le_neg10 : s ≤ -10
                                                                              · exact quartic_d9_squeeze_7 s t
                                                                                  (by nlinarith [sq_ge_of_le_neg s 10 (by norm_num) hs_le_neg10])
                                                                                  (by
                                                                                    have hsabs := sq_le_of_abs_le s 10 (by omega) (by omega)
                                                                                    nlinarith)
                                                                                  h
                                                                              · by_cases hs_ge10 : 10 ≤ s
                                                                                · exact quartic_d9_squeeze_7 s t
                                                                                    (by nlinarith [sq_ge_of_ge s 10 (by norm_num) hs_ge10])
                                                                                    (by
                                                                                      have hsabs := sq_le_of_abs_le s 10 (by omega) (by omega)
                                                                                      nlinarith)
                                                                                    h
                                                                                · have hs_small :
                                                                                      s = -9 ∨ s = -8 ∨ (-7 ≤ s ∧ s ≤ 7) ∨ s = 8 ∨ s = 9 := by
                                                                                    omega
                                                                                  rcases hs_small with rfl | rfl | hs_mid | rfl | rfl
                                                                                  · norm_num at hcop
                                                                                  · norm_num at h
                                                                                    exact not_sq_2719 t h
                                                                                  · exact quartic_d9_negative s t
                                                                                      (by
                                                                                        have hsabs := sq_le_of_abs_le s 7 hs_mid.1 hs_mid.2
                                                                                        nlinarith)
                                                                                      h
                                                                                  · norm_num at h
                                                                                    exact not_sq_2719 t h
                                                                                  · norm_num at hcop
```
