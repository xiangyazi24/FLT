import Mathlib

/-!
# Algebraic core for the `Z/2 × Z/10` forward direction

This file only records the rational algebra after the Tate-normal-form
reduction.  The reduction from an arbitrary elliptic curve to these explicit
parameters is deliberately left to a later layer.
-/

def b10 (u : ℚ) : ℚ :=
  ((u - 1) ^ 3 * (u + 1)) / (u * (u ^ 2 - 4 * u - 1) ^ 2)

def c10 (u : ℚ) : ℚ :=
  ((u - 1) * (u + 1)) / (u * (u ^ 2 - 4 * u - 1))

def x5_10 (u : ℚ) : ℚ :=
  -((u - 1) ^ 3 * (u + 1)) / (4 * u ^ 2 * (u ^ 2 - 4 * u - 1))

def Q10 (u X : ℚ) : ℚ :=
  4 * X ^ 2
    - (8 * (u ^ 3 - 3 * u ^ 2 - u + 1) / (u ^ 2 - 4 * u - 1) ^ 2) * X
    + 4 * (u - 1) ^ 3 * (u + 1) / (u ^ 2 - 4 * u - 1) ^ 3

def w10 (u xT : ℚ) : ℚ :=
  ((u ^ 2 - 4 * u - 1) ^ 2 * xT - (u ^ 3 - 3 * u ^ 2 - u + 1)) / 2

private lemma rat_sq_ne_five (r : ℚ) : r ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨r, by simpa [pow_two] using h.symm⟩
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot hsq

lemma u2_sub_4u_sub_1_ne_zero (u : ℚ) : u ^ 2 - 4 * u - 1 ≠ 0 := by
  intro h
  exact rat_sq_ne_five (u - 2) (by nlinarith)

private lemma w10_sq_sub_E20_poly (u xT : ℚ) :
    w10 u xT ^ 2 - (u ^ 3 + u ^ 2 - u) =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 4) * xT ^ 2
        - ((u ^ 2 - 4 * u - 1) ^ 2 * (u ^ 3 - 3 * u ^ 2 - u + 1) * xT) / 2
        + ((u ^ 2 - 4 * u - 1) * ((u - 1) ^ 3 * (u + 1))) / 4 := by
  unfold w10
  ring

private lemma scaled_Q10_eq_poly_aux (D A B X : ℚ) (hD : D ≠ 0) :
    (D ^ 4 / 16) * (4 * X ^ 2 - (8 * A / D ^ 2) * X + 4 * B / D ^ 3) =
      (D ^ 4 / 4) * X ^ 2 - (D ^ 2 * A * X) / 2 + (D * B) / 4 := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  field_simp [hD, hD2, hD3]
  ring

private lemma scaled_Q10_eq_poly (u xT : ℚ) (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) :
    ((u ^ 2 - 4 * u - 1) ^ 4 / 16) * Q10 u xT =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 4) * xT ^ 2
        - ((u ^ 2 - 4 * u - 1) ^ 2 * (u ^ 3 - 3 * u ^ 2 - u + 1) * xT) / 2
        + ((u ^ 2 - 4 * u - 1) * ((u - 1) ^ 3 * (u + 1))) / 4 := by
  unfold Q10
  simpa [mul_assoc] using scaled_Q10_eq_poly_aux (u ^ 2 - 4 * u - 1)
    (u ^ 3 - 3 * u ^ 2 - u + 1) ((u - 1) ^ 3 * (u + 1)) xT hu2

lemma w10_sq_sub_E20 (u xT : ℚ) (hu : u ≠ 0) (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) :
    w10 u xT ^ 2 - (u ^ 3 + u ^ 2 - u) =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 16) * Q10 u xT := by
  have _hu := hu
  rw [w10_sq_sub_E20_poly u xT, scaled_Q10_eq_poly u xT hu2]

lemma E20_point_of_Q10_root (u xT : ℚ) (hu : u ≠ 0)
    (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) (hQ : Q10 u xT = 0) :
    (w10 u xT) ^ 2 = u ^ 3 + u ^ 2 - u := by
  have h := w10_sq_sub_E20 u xT hu hu2
  rw [hQ, mul_zero] at h
  nlinarith
