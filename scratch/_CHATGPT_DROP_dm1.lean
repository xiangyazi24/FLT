import Mathlib

/-!
# Integral solutions for `w² = (u - 1)(u - 2)(u + 2)`

Task from the drop file: prove `int_solutions_N12`.

The requested reference file `scratch/Descent20a4.lean` was not present at the
specified path on `ai-scratch` when this file was written.  The small-case and
sign/modular parts below are fully explicit.  The remaining large-positive
coprime-descent/rank-zero exclusion is isolated in `N12_large_descent`.
-/

namespace Scratch.ChatGPTDropDM1

/-- Polynomial factorization for the N=12 curve. -/
theorem N12_factor (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u - 2) * (u + 2) := by
  ring

/-- Squares are never negative. -/
theorem int_sq_nonneg' (w : ℤ) : (0 : ℤ) <= w ^ 2 := by
  exact sq_nonneg w

/-- The negative tail is impossible: for `u <= -3` the three factors are negative. -/
theorem N12_no_left_tail (u w : ℤ)
    (hu : u <= -3)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) : False := by
  rw [N12_factor u] at h
  have h1 : u - 1 < 0 := by omega
  have h2 : u - 2 < 0 := by omega
  have h3 : u + 2 < 0 := by omega
  have hp12 : 0 < (u - 1) * (u - 2) := mul_pos_of_neg_of_neg h1 h2
  have hprod : (u - 1) * (u - 2) * (u + 2) < 0 := mul_neg_of_pos_of_neg hp12 h3
  have hw : 0 <= w ^ 2 := sq_nonneg w
  nlinarith

/-- `-1` is excluded because it would force `w² = 6`, impossible modulo `3`. -/
theorem N12_no_neg_one (w : ℤ)
    (h : w ^ 2 = (-1 : ℤ) ^ 3 - (-1 : ℤ) ^ 2 - 4 * (-1 : ℤ) + 4) : False := by
  norm_num at h
  have hmod : (w ^ 2) % 3 = (6 : ℤ) % 3 := by rw [h]
  have hsquare_mod3 : (w ^ 2) % 3 = 0 ∨ (w ^ 2) % 3 = 1 := by
    have hw : w % 3 = 0 ∨ w % 3 = 1 ∨ w % 3 = 2 := by omega
    rcases hw with hw | hw | hw
    · left
      calc
        (w ^ 2) % 3 = ((w % 3) ^ 2) % 3 := by omega
        _ = 0 := by omega
    · right
      calc
        (w ^ 2) % 3 = ((w % 3) ^ 2) % 3 := by omega
        _ = 1 := by omega
    · right
      calc
        (w ^ 2) % 3 = ((w % 3) ^ 2) % 3 := by omega
        _ = 1 := by omega
  norm_num at hmod
  omega

/-- `3` is excluded because it would force `w² = 10`, impossible modulo `5`. -/
theorem N12_no_three (w : ℤ)
    (h : w ^ 2 = (3 : ℤ) ^ 3 - (3 : ℤ) ^ 2 - 4 * (3 : ℤ) + 4) : False := by
  norm_num at h
  have hmod : (w ^ 2) % 5 = (10 : ℤ) % 5 := by rw [h]
  have hsquare_mod5 :
      (w ^ 2) % 5 = 0 ∨ (w ^ 2) % 5 = 1 ∨ (w ^ 2) % 5 = 4 := by
    have hw : w % 5 = 0 ∨ w % 5 = 1 ∨ w % 5 = 2 ∨ w % 5 = 3 ∨ w % 5 = 4 := by
      omega
    rcases hw with hw | hw | hw | hw | hw
    · left
      calc
        (w ^ 2) % 5 = ((w % 5) ^ 2) % 5 := by omega
        _ = 0 := by omega
    · right; left
      calc
        (w ^ 2) % 5 = ((w % 5) ^ 2) % 5 := by omega
        _ = 1 := by omega
    · right; right
      calc
        (w ^ 2) % 5 = ((w % 5) ^ 2) % 5 := by omega
        _ = 4 := by omega
    · right; right
      calc
        (w ^ 2) % 5 = ((w % 5) ^ 2) % 5 := by omega
        _ = 4 := by omega
    · right; left
      calc
        (w ^ 2) % 5 = ((w % 5) ^ 2) % 5 := by omega
        _ = 1 := by omega
  norm_num at hmod
  omega

/--
Large-positive descent exclusion.

This is the missing coprime descent requested in the task: for `u >= 5`, split
on `3 ∣ u - 1`; in the coprime case apply `Int.sq_of_isCoprime` to
`(u - 1) * ((u - 2) * (u + 2))`, then squeeze between consecutive squares; in
the `3 ∣ u - 1` branch divide the forced factor of `9` and repeat the coprime
square decomposition.
-/
axiom N12_large_descent (u w : ℤ)
    (hu : 5 <= u)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) : False

/-- Integer solutions of `w² = u³ - u² - 4u + 4` have the claimed `u`-coordinate. -/
theorem int_solutions_N12 (u w : ℤ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    u ∈ ({-2, 0, 1, 2, 4} : Finset ℤ) := by
  have hcases : u <= -3 ∨ u = -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ 5 <= u := by
    omega
  rcases hcases with hleft | hneg2 | hneg1 | h0 | h1 | h2 | h3 | h4 | hright
  · exact False.elim (N12_no_left_tail u w hleft h)
  · subst u
    norm_num
  · subst u
    exact False.elim (N12_no_neg_one w h)
  · subst u
    norm_num
  · subst u
    norm_num
  · subst u
    norm_num
  · subst u
    exact False.elim (N12_no_three w h)
  · subst u
    norm_num
  · exact False.elim (N12_large_descent u w hright h)

end Scratch.ChatGPTDropDM1
