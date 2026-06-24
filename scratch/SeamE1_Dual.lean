module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.LinearCombination

/-! # SEAM1 / E1 — dual-number Taylor layer (A1) -/

open Polynomial TrivSqZeroExt
open scoped Polynomial

namespace SeamE1

variable {R : Type*} [CommRing R]

private lemma dual_pow (x v : R) (n : ℕ) :
    (inl x + inr v : DualNumber R) ^ n = inl (x ^ n) + inr ((n : R) * x ^ (n - 1) * v) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have mlem : (m : R) * x ^ (m - 1) * x = (m : R) * x ^ m := by
      rcases m with _ | k
      · simp
      · rw [Nat.succ_sub_one, pow_succ]; ring
    rw [pow_succ, ih]
    apply TrivSqZeroExt.ext
    · simp [fst_mul, pow_succ]
    · simp only [snd_mul, fst_add, snd_add, fst_inl, fst_inr, snd_inl, snd_inr,
        add_zero, zero_add, op_smul_eq_mul, Nat.add_sub_cancel]
      push_cast
      linear_combination v * mlem

public lemma eval_dualNumber (f : R[X]) (x v : R) :
    aeval (inl x + inr v : DualNumber R) f
      = inl (f.eval x) + inr (v * f.derivative.eval x) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, eval_add, derivative_add, eval_add, mul_add]
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, snd_add, fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add] <;> ring
  | monomial n a =>
    rw [aeval_monomial, dual_pow, TrivSqZeroExt.algebraMap_eq_inl,
      eval_monomial, derivative_monomial]
    apply TrivSqZeroExt.ext
    · simp [fst_mul]
    · simp only [snd_mul, fst_add, snd_add, fst_inl, fst_inr, snd_inl, snd_inr,
        eval_monomial, op_smul_eq_mul, smul_zero, add_zero, zero_add]
      ring

/-- A multiple root gives a first-order (dual) root: if `f` and its derivative both vanish at `x`,
then `f` vanishes at the dual point `x + εv` for every `v`. -/
public lemma aeval_dual_eq_zero_of_root_of_deriv_root {f : R[X]} {x v : R}
    (hx : f.eval x = 0) (hdx : f.derivative.eval x = 0) :
    aeval (inl x + inr v : DualNumber R) f = 0 := by
  rw [eval_dualNumber, hx, hdx, mul_zero]
  simp

end SeamE1

