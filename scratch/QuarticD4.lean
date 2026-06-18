import Mathlib

/-!
# The `d = 4` quartic obstruction

We prove that no odd integer `s` makes

` s^4 + 16*s^2 - 256 `

an integer square.
-/

namespace Scratch.ChatGPTDropDM1

/-- No square can lie strictly between two consecutive nonnegative squares. -/
private lemma sq_not_between_consecutive
    (A n : ℤ) (hA : 0 ≤ A)
    (hlo : A ^ 2 < n ^ 2)
    (hhi : n ^ 2 < (A + 1) ^ 2) : False := by
  have hn_ne : n ≠ 0 := by
    intro hn
    subst n
    nlinarith [sq_nonneg A]
  rcases lt_or_gt_of_ne hn_ne with hnneg | hnpos
  · have hlt : A < -n := by
      nlinarith [sq_nonneg (n + A)]
    have hgt : -n < A + 1 := by
      nlinarith [sq_nonneg (n + A + 1)]
    omega
  · have hlt : A < n := by
      nlinarith [sq_nonneg (n - A - 1)]
    have hgt : n < A + 1 := by
      nlinarith [sq_nonneg (n - A)]
    omega

/-- A constant-value square squeeze. -/
private lemma not_square_of_between
    (A N n : ℤ) (hA : 0 ≤ A)
    (hN : N = n ^ 2)
    (hlo : A ^ 2 < N)
    (hhi : N < (A + 1) ^ 2) : False := by
  exact sq_not_between_consecutive A n hA (by nlinarith) (by nlinarith)

/-- The large `|s|` squeeze for `|s| ≥ 13`. -/
private lemma quartic_no_sol_d4_large (s t : ℤ)
    (hlarge : s ≤ -13 ∨ 13 ≤ s)
    (h : s ^ 4 + 16 * s ^ 2 - 256 = t ^ 2) : False := by
  have hs2_ge : (169 : ℤ) ≤ s ^ 2 := by
    rcases hlarge with hs | hs
    · nlinarith [sq_nonneg (s + 13)]
    · nlinarith [sq_nonneg (s - 13)]
  have hA : 0 ≤ s ^ 2 + 7 := by
    nlinarith [sq_nonneg s]
  have hlo : (s ^ 2 + 7) ^ 2 < t ^ 2 := by
    nlinarith
  have hhi : t ^ 2 < ((s ^ 2 + 7) + 1) ^ 2 := by
    nlinarith
  exact sq_not_between_consecutive (s ^ 2 + 7) t hA hlo hhi

/--
For odd integers `s`, the value `s^4 + 16*s^2 - 256` is never a square.
-/
theorem quartic_no_sol_d4 (s t : ℤ) (hs_odd : ¬ (2 : ℤ) ∣ s) :
    s ^ 4 + 16 * s ^ 2 - 256 = t ^ 2 → False := by
  intro h
  have hcases :
      s ≤ -13 ∨ s = -11 ∨ s = -9 ∨ s = -7 ∨ s = -5 ∨ s = -3 ∨ s = -1 ∨
      s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 7 ∨ s = 9 ∨ s = 11 ∨ 13 ≤ s := by
    have hmod : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · exact False.elim (hs_odd (Int.dvd_of_emod_eq_zero h0))
    · omega
  rcases hcases with hle | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | hge
  · exact quartic_no_sol_d4_large s t (Or.inl hle) h
  · norm_num at h
    exact not_square_of_between 127 16321 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 87 7601 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 54 2929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 27 769 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    exact not_square_of_between 27 769 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 54 2929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 87 7601 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 127 16321 t (by norm_num) h (by norm_num) (by norm_num)
  · exact quartic_no_sol_d4_large s t (Or.inr hge) h

end Scratch.ChatGPTDropDM1
