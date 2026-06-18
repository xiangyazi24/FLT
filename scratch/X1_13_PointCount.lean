import Mathlib

/-!
# Point counts for a hyperelliptic model of `X_1(13)`

The genus-2 model is

`y² = x⁶ - 2x⁵ + x⁴ - 2x³ + 6x² - 4x + 1`.
-/

open Polynomial

/-- The sextic defining the affine hyperelliptic model of `X_1(13)`. -/
noncomputable def X1_13_fZ : ℤ[X] :=
  X ^ 6 - C 2 * X ^ 5 + X ^ 4 - C 2 * X ^ 3 + C 6 * X ^ 2 - C 4 * X + C 1

lemma X1_13_fZ_eval_zero : X1_13_fZ.eval 0 = 1 := by
  norm_num [X1_13_fZ]

lemma X1_13_fZ_eval_one : X1_13_fZ.eval 1 = 1 := by
  norm_num [X1_13_fZ]

def X1_13_rhs_F5 (x : ZMod 5) : ZMod 5 :=
  x ^ 6 - 2 * x ^ 5 + x ^ 4 - 2 * x ^ 3 + 6 * x ^ 2 - 4 * x + 1

def X1_13_rhs_F7 (x : ZMod 7) : ZMod 7 :=
  x ^ 6 - 2 * x ^ 5 + x ^ 4 - 2 * x ^ 3 + 6 * x ^ 2 - 4 * x + 1

set_option linter.style.nativeDecide false in
theorem X1_13_F5_affine_count :
    (Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
      p.2 ^ 2 = X1_13_rhs_F5 p.1)).card = 4 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem X1_13_F7_affine_count :
    (Finset.univ.filter (fun p : ZMod 7 × ZMod 7 =>
      p.2 ^ 2 = X1_13_rhs_F7 p.1)).card = 6 := by
  native_decide
