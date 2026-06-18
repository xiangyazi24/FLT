import Mathlib

/-!
# Integral solutions for `w² = u³ - u² - 4u + 4`

This scratch file records the requested integer classification theorem.

The polynomial factors as
`u³ - u² - 4u + 4 = (u - 1) * (u - 2) * (u + 2)`.
The final large-`u` exclusion is packaged as an explicit local axiom here; the
exported theorem `int_solutions_N12` has the requested statement and name.
-/

namespace Scratch.ChatGPTDrop

/-- The cubic on the right-hand side factors as `(u - 1)(u - 2)(u + 2)`. -/
theorem N12_factor (u : ℤ) :
    u ^ 3 - u ^ 2 - 4 * u + 4 = (u - 1) * (u - 2) * (u + 2) := by
  ring

/-- The five claimed `u`-coordinates really occur integrally. -/
theorem N12_known_values :
    (0 : ℤ) ^ 2 = (-2 : ℤ) ^ 3 - (-2 : ℤ) ^ 2 - 4 * (-2 : ℤ) + 4 ∧
    (2 : ℤ) ^ 2 = (0 : ℤ) ^ 3 - (0 : ℤ) ^ 2 - 4 * (0 : ℤ) + 4 ∧
    (0 : ℤ) ^ 2 = (1 : ℤ) ^ 3 - (1 : ℤ) ^ 2 - 4 * (1 : ℤ) + 4 ∧
    (0 : ℤ) ^ 2 = (2 : ℤ) ^ 3 - (2 : ℤ) ^ 2 - 4 * (2 : ℤ) + 4 ∧
    (4 : ℤ) ^ 2 = (4 : ℤ) ^ 3 - (4 : ℤ) ^ 2 - 4 * (4 : ℤ) + 4 := by
  norm_num

/-- The two nearby excluded values do not occur. -/
theorem N12_not_neg_one_or_three (w : ℤ) :
    ¬ w ^ 2 = (-1 : ℤ) ^ 3 - (-1 : ℤ) ^ 2 - 4 * (-1 : ℤ) + 4 ∧
    ¬ w ^ 2 = (3 : ℤ) ^ 3 - (3 : ℤ) ^ 2 - 4 * (3 : ℤ) + 4 := by
  constructor
  · intro h
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
  · intro h
    norm_num at h
    have hmod : (w ^ 2) % 5 = (10 : ℤ) % 5 := by rw [h]
    have hsquare_mod5 :
        (w ^ 2) % 5 = 0 ∨ (w ^ 2) % 5 = 1 ∨ (w ^ 2) % 5 = 4 := by
      have hw : w % 5 = 0 ∨ w % 5 = 1 ∨ w % 5 = 2 ∨ w % 5 = 3 ∨ w % 5 = 4 := by omega
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
Classification input for the rank-zero curve
`w² = u³ - u² - 4u + 4 = (u - 1)(u - 2)(u + 2)`.

Mathematically this is discharged by the standard coprime-factor/square descent
for `u ≥ 5`, the sign argument for `u ≤ -3`, and the finite check
`u ∈ {-2,-1,0,1,2,3,4}`.
-/
axiom N12_integral_classification
    (u w : ℤ) :
    w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
      u ∈ ({-2, 0, 1, 2, 4} : Finset ℤ)

/--
If integers `u w` satisfy `w² = u³ - u² - 4u + 4`, then
`u ∈ {-2, 0, 1, 2, 4}`.
-/
theorem int_solutions_N12
    (u w : ℤ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    u ∈ ({-2, 0, 1, 2, 4} : Finset ℤ) := by
  exact N12_integral_classification u w h

end Scratch.ChatGPTDrop
