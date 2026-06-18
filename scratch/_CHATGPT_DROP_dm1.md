# Quartic `d = 8` no-square proof

The goal is to prove that

\[
s^4 + 64s^2 - 4096 = t^2
\]

has no integer solutions when `gcd(s,8)=1`, i.e. when `s` is odd.

The proof uses the requested small/large split.  For small odd values, the negative cases `|s|≤5` contradict `sq_nonneg t`, and the positive cases `7≤|s|≤49` are checked by explicit squeezes between consecutive squares.  For the large tail `|s|≥51`, put `x=s^2`; then

\[
(x+31)^2 < x^2+64x-4096 < (x+32)^2,
\]

because the lower difference is `2*x - 5057`, positive once `x≥51^2=2601`, and the upper difference is the constant `5120`.  The helper `sq_not_between_consecutive` follows the same style as `scratch/Descent20a4.lean`: after splitting on the sign of `t`, it uses `nlinarith [sq_nonneg ...]` to turn strict square inequalities into incompatible consecutive integer bounds.

```lean
import Mathlib

/-!
# The `d = 8` quartic obstruction

We prove that no odd integer `s` makes

` s^4 + 64*s^2 - 4096 `

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

/-- The large `|s|` squeeze for `|s| ≥ 51`. -/
private lemma quartic_no_sol_d8_large (s t : ℤ)
    (hlarge : s ≤ -51 ∨ 51 ≤ s)
    (h : s ^ 4 + 64 * s ^ 2 - 4096 = t ^ 2) : False := by
  have hs2_ge : (2601 : ℤ) ≤ s ^ 2 := by
    rcases hlarge with hs | hs
    · nlinarith [sq_nonneg (s + 51)]
    · nlinarith [sq_nonneg (s - 51)]
  have hA : 0 ≤ s ^ 2 + 31 := by
    nlinarith [sq_nonneg s]
  have hlo : (s ^ 2 + 31) ^ 2 < t ^ 2 := by
    nlinarith
  have hhi : t ^ 2 < ((s ^ 2 + 31) + 1) ^ 2 := by
    nlinarith
  exact sq_not_between_consecutive (s ^ 2 + 31) t hA hlo hhi

/--
For odd integers `s`, the value `s^4 + 64*s^2 - 4096` is never a square.
-/
theorem quartic_no_sol_d8 (s t : ℤ) (hs_odd : ¬ (2 : ℤ) ∣ s) :
    s ^ 4 + 64 * s ^ 2 - 4096 = t ^ 2 → False := by
  intro h
  have hcases :
      s ≤ -51 ∨ s = -49 ∨ s = -47 ∨ s = -45 ∨ s = -43 ∨ s = -41 ∨
      s = -39 ∨ s = -37 ∨ s = -35 ∨ s = -33 ∨ s = -31 ∨ s = -29 ∨
      s = -27 ∨ s = -25 ∨ s = -23 ∨ s = -21 ∨ s = -19 ∨ s = -17 ∨
      s = -15 ∨ s = -13 ∨ s = -11 ∨ s = -9 ∨ s = -7 ∨ s = -5 ∨
      s = -3 ∨ s = -1 ∨ s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 7 ∨ s = 9 ∨
      s = 11 ∨ s = 13 ∨ s = 15 ∨ s = 17 ∨ s = 19 ∨ s = 21 ∨
      s = 23 ∨ s = 25 ∨ s = 27 ∨ s = 29 ∨ s = 31 ∨ s = 33 ∨
      s = 35 ∨ s = 37 ∨ s = 39 ∨ s = 41 ∨ s = 43 ∨ s = 45 ∨
      s = 47 ∨ s = 49 ∨ 51 ≤ s := by
    have hmod : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · exact False.elim (hs_odd (Int.dvd_of_emod_eq_zero h0))
    · omega
  rcases hcases with hle |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
  · exact quartic_no_sol_d8_large s t (Or.inl hle) h
  · norm_num at h
    exact not_square_of_between 2431 5914369 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 2239 5016961 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 2055 4226129 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1879 3533041 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1711 2929249 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1551 2406689 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1399 1957681 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1254 1574929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1118 1251521 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 990 980929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 870 757009 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 757 574001 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 653 426529 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 556 309601 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 467 218609 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 386 149329 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 312 97921 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 246 60929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 187 35281 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 135 18289 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 87 7649 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 37 1441 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    nlinarith [sq_nonneg t]
  · norm_num at h
    exact not_square_of_between 37 1441 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 87 7649 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 135 18289 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 187 35281 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 246 60929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 312 97921 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 386 149329 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 467 218609 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 556 309601 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 653 426529 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 757 574001 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 870 757009 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 990 980929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1118 1251521 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1254 1574929 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1399 1957681 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1551 2406689 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1711 2929249 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 1879 3533041 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 2055 4226129 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 2239 5016961 t (by norm_num) h (by norm_num) (by norm_num)
  · norm_num at h
    exact not_square_of_between 2431 5914369 t (by norm_num) h (by norm_num) (by norm_num)
  · exact quartic_no_sol_d8_large s t (Or.inr hge) h

end Scratch.ChatGPTDropDM1
```
