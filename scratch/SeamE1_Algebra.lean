module

public import Mathlib.FieldTheory.Separable

/-! # SEAM1 / E1 — general-polynomial layer (A3)

`separable_of_deriv_ne_zero_at_roots`: over a field where `f` splits, if `f` shares no root with its
derivative then `f` is separable. This is the rootwise reduction target for `preΨ'_separable`. -/

open Polynomial

namespace SeamE1

variable {K : Type*} [Field K]

/-- A split polynomial with no common root with its derivative is separable. -/
public theorem separable_of_deriv_ne_zero_at_roots {f : K[X]} (hf : f ≠ 0)
    (hsplit : f.Splits)
    (hroot : ∀ x, f.IsRoot x → ¬ (derivative f).IsRoot x) :
    f.Separable := by
  classical
  rw [← Polynomial.nodup_roots_iff_of_splits hf hsplit, Multiset.nodup_iff_count_le_one]
  intro a
  rw [Polynomial.count_roots]
  by_contra hgt
  push_neg at hgt
  rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot_gcd hf] at hgt
  have hgt' : (gcd f (derivative f)).eval a = 0 := hgt
  obtain ⟨c, hc⟩ := gcd_dvd_left f (derivative f)
  obtain ⟨d, hd⟩ := gcd_dvd_right f (derivative f)
  have hfa : f.IsRoot a := by rw [IsRoot, hc, eval_mul, hgt', zero_mul]
  have hf'a : (derivative f).IsRoot a := by rw [IsRoot, hd, eval_mul, hgt', zero_mul]
  exact hroot a hfa hf'a

end SeamE1

