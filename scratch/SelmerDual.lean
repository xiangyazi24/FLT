import Mathlib

private lemma pow4_eq_zero {x : ℤ} (h : x ^ 4 = 0) : x = 0 := by
  by_contra hne; exact absurd h (by positivity)

theorem dual_selmer_neg1 (S T W : ℤ)
    (h : -(W ^ 2) = T ^ 4 + 2 * T ^ 2 * S ^ 2 + 5 * S ^ 4) :
    S = 0 ∧ T = 0 ∧ W = 0 := by
  have hW : W = 0 := by nlinarith [sq_nonneg W, sq_nonneg T, sq_nonneg S, sq_nonneg (T*S)]
  have hS : S = 0 := pow4_eq_zero (show S ^ 4 = 0 by nlinarith [sq_nonneg T, sq_nonneg W])
  have hT : T = 0 := pow4_eq_zero (show T ^ 4 = 0 by nlinarith [sq_nonneg S, sq_nonneg W])
  exact ⟨hS, hT, hW⟩

theorem dual_selmer_neg5 (S T W : ℤ)
    (h : -(5 * W ^ 2) = 25 * T ^ 4 + 10 * T ^ 2 * S ^ 2 + 5 * S ^ 4) :
    S = 0 ∧ T = 0 ∧ W = 0 := by
  have hW : W = 0 := by nlinarith [sq_nonneg W, sq_nonneg T, sq_nonneg S, sq_nonneg (T*S)]
  have hS : S = 0 := pow4_eq_zero (show S ^ 4 = 0 by nlinarith [sq_nonneg T, sq_nonneg W])
  have hT : T = 0 := pow4_eq_zero (show T ^ 4 = 0 by nlinarith [sq_nonneg S, sq_nonneg W])
  exact ⟨hS, hT, hW⟩

theorem dual_selmer_neg2 (S T W : ℤ)
    (h : -(2 * W ^ 2) = 4 * T ^ 4 + 4 * T ^ 2 * S ^ 2 + 5 * S ^ 4) :
    S = 0 ∧ T = 0 ∧ W = 0 := by
  have hW : W = 0 := by nlinarith [sq_nonneg W, sq_nonneg T, sq_nonneg S, sq_nonneg (T*S)]
  have hS : S = 0 := pow4_eq_zero (show S ^ 4 = 0 by nlinarith [sq_nonneg T, sq_nonneg W])
  have hT : T = 0 := pow4_eq_zero (show T ^ 4 = 0 by nlinarith [sq_nonneg S, sq_nonneg W])
  exact ⟨hS, hT, hW⟩

theorem dual_selmer_neg10 (S T W : ℤ)
    (h : -(10 * W ^ 2) = 100 * T ^ 4 + 20 * T ^ 2 * S ^ 2 + 5 * S ^ 4) :
    S = 0 ∧ T = 0 ∧ W = 0 := by
  have hW : W = 0 := by nlinarith [sq_nonneg W, sq_nonneg T, sq_nonneg S, sq_nonneg (T*S)]
  have hS : S = 0 := pow4_eq_zero (show S ^ 4 = 0 by nlinarith [sq_nonneg T, sq_nonneg W])
  have hT : T = 0 := pow4_eq_zero (show T ^ 4 = 0 by nlinarith [sq_nonneg S, sq_nonneg W])
  exact ⟨hS, hT, hW⟩

