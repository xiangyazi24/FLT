# ChatGPT Drop File (dm2)

The target is the `d = 11` quartic obstruction:

```lean
theorem quartic_no_sol_d11 (s t : ℤ) (hcop : Int.gcd s 11 = 1) :
    s ^ 4 + 121 * s ^ 2 - 14641 = t ^ 2 → False
```

For `d = 11`, a compact proof comes from the same Pellian factorization that appears naturally for the quartic:

```text
(2*s^2 + d^2)^2 - (2*t)^2 = 5*d^4.
```

With `d = 11`, this gives

```text
(2*s^2 + 121 - 2*t) * (2*s^2 + 121 + 2*t) = 73205 = 5*11^4.
```

Both factors are positive.  Taking the smaller factor, it is at most `271`, so a finite divisor check leaves only

```text
A = 1, 5, 11, 55, 121.
```

The corresponding values of `s^2` are respectively

```text
18241, 3601, 1606, 286, 121.
```

The first four are not squares, each by a small consecutive-squares squeeze.  The last forces `s = ±11`, contradicting `Int.gcd s 11 = 1`.

```lean
import Mathlib

/-!
# The `d = 11` quartic obstruction

We prove that `s^4 + 121*s^2 - 14641 = t^2` has no integer solution when
`Int.gcd s 11 = 1`.
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

private lemma not_sq_18241 (s : ℤ) (h : s ^ 2 = 18241) : False := by
  exact no_sq_between_consecutive s 135 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_3601 (s : ℤ) (h : s ^ 2 = 3601) : False := by
  exact no_sq_between_consecutive s 60 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_1606 (s : ℤ) (h : s ^ 2 = 1606) : False := by
  exact no_sq_between_consecutive s 40 (by norm_num) (by nlinarith) (by nlinarith)

private lemma not_sq_286 (s : ℤ) (h : s ^ 2 = 286) : False := by
  exact no_sq_between_consecutive s 16 (by norm_num) (by nlinarith) (by nlinarith)

private lemma sq_eq_121_gcd_contra (s : ℤ) (hcop : Int.gcd s 11 = 1)
    (h : s ^ 2 = 121) : False := by
  have hbound : -11 ≤ s ∧ s ≤ 11 :=
    ⟨by nlinarith [sq_nonneg (s + 11)],
     by nlinarith [sq_nonneg (s - 11)]⟩
  interval_cases s <;> norm_num at h hcop

private lemma pos_factors_of_pos_prod_pos_sum {A B : ℤ}
    (hprod : A * B = 73205) (hsum : 0 < A + B) : 0 < A ∧ 0 < B := by
  have hprod_pos : 0 < A * B := by
    rw [hprod]
    norm_num
  by_cases hA : 0 < A
  · by_cases hB : 0 < B
    · exact ⟨hA, hB⟩
    · have hBle : B ≤ 0 := by omega
      have hprod_nonpos : A * B ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hBle
      nlinarith
  · have hAle : A ≤ 0 := by omega
    by_cases hB : 0 < B
    · have hprod_nonpos : A * B ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAle (le_of_lt hB)
      nlinarith
    · have hBle : B ≤ 0 := by omega
      have hsum_nonpos : A + B ≤ 0 := by omega
      nlinarith

private lemma smaller_factor_contra (A B s : ℤ)
    (hApos : 0 < A) (hBpos : 0 < B) (hAleB : A ≤ B)
    (hprod : A * B = 73205) (hsum : A + B = 4 * s ^ 2 + 242)
    (hcop : Int.gcd s 11 = 1) : False := by
  have hA_ge_one : 1 ≤ A := by omega
  have hA_le_271 : A ≤ 271 := by
    by_contra hnot
    have hA272 : (272 : ℤ) ≤ A := by omega
    have hB272 : (272 : ℤ) ≤ B := by omega
    have hprod_ge : (272 : ℤ) * 272 ≤ A * B := by
      exact mul_le_mul hA272 hB272 (by norm_num) (by omega)
    nlinarith
  interval_cases A <;> norm_num at hprod hsum ⊢
  all_goals try omega
  · have hs_sq : s ^ 2 = 18241 := by omega
    exact not_sq_18241 s hs_sq
  · have hs_sq : s ^ 2 = 3601 := by omega
    exact not_sq_3601 s hs_sq
  · have hs_sq : s ^ 2 = 1606 := by omega
    exact not_sq_1606 s hs_sq
  · have hs_sq : s ^ 2 = 286 := by omega
    exact not_sq_286 s hs_sq
  · have hs_sq : s ^ 2 = 121 := by omega
    exact sq_eq_121_gcd_contra s hcop hs_sq

theorem quartic_no_sol_d11 (s t : ℤ) (hcop : Int.gcd s 11 = 1) :
    s ^ 4 + 121 * s ^ 2 - 14641 = t ^ 2 → False := by
  intro h
  let X : ℤ := 2 * s ^ 2 + 121
  let A : ℤ := X - 2 * t
  let B : ℤ := X + 2 * t
  have hfac : A * B = 73205 := by
    dsimp [A, B, X]
    calc
      (2 * s ^ 2 + 121 - 2 * t) * (2 * s ^ 2 + 121 + 2 * t)
          = (2 * s ^ 2 + 121) ^ 2 - (2 * t) ^ 2 := by ring
      _ = 73205 := by nlinarith
  have hsum : A + B = 4 * s ^ 2 + 242 := by
    dsimp [A, B, X]
    ring
  have hsum_pos : 0 < A + B := by
    rw [hsum]
    nlinarith [sq_nonneg s]
  have hpos := pos_factors_of_pos_prod_pos_sum hfac hsum_pos
  by_cases ht : 0 ≤ t
  · have hAleB : A ≤ B := by
      dsimp [A, B]
      omega
    exact smaller_factor_contra A B s hpos.1 hpos.2 hAleB hfac hsum hcop
  · have hB_le_A : B ≤ A := by
      dsimp [A, B]
      omega
    exact smaller_factor_contra B A s hpos.2 hpos.1 hB_le_A
      (by
        rw [mul_comm]
        exact hfac)
      (by
        rw [add_comm]
        exact hsum)
      hcop
```
