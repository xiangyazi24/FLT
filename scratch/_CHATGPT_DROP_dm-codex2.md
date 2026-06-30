# Q2679 dm-codex2: positive square factors

Target file requested: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

The connector-visible refs did not expose that target file, so this is written as a standalone scratch under `import Mathlib.Tactic`.  It is namespace-neutral: paste it at top level, or inside the target file's existing namespace.  The first proof uses the upstream Mathlib GCD-monoid square-factor theorem rather than relying on a repository-local `Int.sq_of_isCoprime`; the negative associate branch is removed by `Int.eq_of_associated_of_nonneg` and the hypotheses `0 < x`, `0 < y`.

```lean
import Mathlib.Tactic

/-- If two positive coprime integers multiply to a square, then both are squares. -/
def PosSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x -> 0 < y -> IsCoprime x y -> z^2 = x*y ->
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a^2 ∧ y = b^2

private lemma q2679_isUnit_gcd_of_isCoprime_int {x y : ℤ}
    (h : IsCoprime x y) : IsUnit (gcd x y) := by
  exact (gcd_isUnit_iff_isRelPrime (a := x) (b := y)).mpr h.isRelPrime

private lemma q2679_eq_sq_of_pos_of_associated_sq {x a : ℤ}
    (hx : 0 < x) (h : Associated (a ^ 2) x) : x = a ^ 2 := by
  exact (Int.eq_of_associated_of_nonneg h (sq_nonneg a) (le_of_lt hx)).symm

/-- Proof of `PosSqOfCoprimeMulSqStatement`. -/
theorem posSqOfCoprimeMulSqStatement : PosSqOfCoprimeMulSqStatement := by
  intro x y z hx hy hcop hsq
  have hxy : x * y = z ^ 2 := hsq.symm
  have hyx : y * x = z ^ 2 := by
    rw [mul_comm]
    exact hxy
  have hunit_xy : IsUnit (gcd x y) :=
    q2679_isUnit_gcd_of_isCoprime_int hcop
  have hunit_yx : IsUnit (gcd y x) :=
    q2679_isUnit_gcd_of_isCoprime_int hcop.symm
  rcases exists_associated_pow_of_mul_eq_pow
      (a := x) (b := y) (c := z) (k := 2) hunit_xy hxy with ⟨a, ha_assoc⟩
  rcases exists_associated_pow_of_mul_eq_pow
      (a := y) (b := x) (c := z) (k := 2) hunit_yx hyx with ⟨b, hb_assoc⟩
  have hx_sq : x = a ^ 2 := q2679_eq_sq_of_pos_of_associated_sq hx ha_assoc
  have hy_sq : y = b ^ 2 := q2679_eq_sq_of_pos_of_associated_sq hy hb_assoc
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hx0 : x = 0 := by
      rw [hx_sq, ha0]
      norm_num
    exact (ne_of_gt hx) hx0
  have hb_ne : b ≠ 0 := by
    intro hb0
    have hy0 : y = 0 := by
      rw [hy_sq, hb0]
      norm_num
    exact (ne_of_gt hy) hy0
  refine ⟨|a|, |b|, abs_pos.mpr ha_ne, abs_pos.mpr hb_ne, ?_, ?_⟩
  · calc
      x = a ^ 2 := hx_sq
      _ = |a| ^ 2 := (sq_abs a).symm
  · calc
      y = b ^ 2 := hy_sq
      _ = |b| ^ 2 := (sq_abs b).symm

/-- The requested two-adic variant. -/
def PosTwoSqOfGcdTwoMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x -> 0 < y -> 2∣x -> 2∣y ->
    IsCoprime (x/2) (y/2) -> z^2=x*y ->
    ∃ a b, 0<a ∧ 0<b ∧ x=2*a^2 ∧ y=2*b^2

private lemma q2679_eq_two_mul_ediv_two {x : ℤ} (hx2 : (2 : ℤ) ∣ x) :
    x = 2 * (x / 2) := by
  calc
    x = x / 2 * 2 := (Int.ediv_mul_cancel hx2).symm
    _ = 2 * (x / 2) := by ring

private lemma q2679_pos_ediv_two_of_pos_of_dvd {x : ℤ}
    (hx : 0 < x) (hx2 : (2 : ℤ) ∣ x) : 0 < x / 2 := by
  have hx_eq : x = 2 * (x / 2) := q2679_eq_two_mul_ediv_two hx2
  nlinarith

private lemma q2679_sq_ediv_two_eq_of_sq_eq_mul
    {x y z : ℤ} (hx2 : (2 : ℤ) ∣ x) (hy2 : (2 : ℤ) ∣ y)
    (hz2 : (2 : ℤ) ∣ z) (hsq : z ^ 2 = x * y) :
    (z / 2) ^ 2 = (x / 2) * (y / 2) := by
  have hx_eq : x = 2 * (x / 2) := q2679_eq_two_mul_ediv_two hx2
  have hy_eq : y = 2 * (y / 2) := q2679_eq_two_mul_ediv_two hy2
  have hz_eq : z = 2 * (z / 2) := q2679_eq_two_mul_ediv_two hz2
  have h4 :
      (4 : ℤ) * ((z / 2) ^ 2) =
        (4 : ℤ) * ((x / 2) * (y / 2)) := by
    calc
      (4 : ℤ) * ((z / 2) ^ 2) = (2 * (z / 2)) ^ 2 := by ring
      _ = z ^ 2 := by rw [← hz_eq]
      _ = x * y := hsq
      _ = (2 * (x / 2)) * (2 * (y / 2)) := by
        rw [← hx_eq, ← hy_eq]
      _ = (4 : ℤ) * ((x / 2) * (y / 2)) := by ring
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/-- Proof of `PosTwoSqOfGcdTwoMulSqStatement`. -/
theorem posTwoSqOfGcdTwoMulSqStatement : PosTwoSqOfGcdTwoMulSqStatement := by
  intro x y z hx hy hx2 hy2 hcop hsq
  have hz_sq_even : (2 : ℤ) ∣ z ^ 2 := by
    rw [hsq]
    exact dvd_mul_of_dvd_left hx2 y
  have hz2 : (2 : ℤ) ∣ z := by
    exact (show Prime (2 : ℤ) by norm_num).dvd_of_dvd_pow hz_sq_even
  have hx_div_pos : 0 < x / 2 := q2679_pos_ediv_two_of_pos_of_dvd hx hx2
  have hy_div_pos : 0 < y / 2 := q2679_pos_ediv_two_of_pos_of_dvd hy hy2
  have hsq_div : (z / 2) ^ 2 = (x / 2) * (y / 2) :=
    q2679_sq_ediv_two_eq_of_sq_eq_mul hx2 hy2 hz2 hsq
  rcases posSqOfCoprimeMulSqStatement hx_div_pos hy_div_pos hcop hsq_div with
    ⟨a, b, ha_pos, hb_pos, hx_div_sq, hy_div_sq⟩
  refine ⟨a, b, ha_pos, hb_pos, ?_, ?_⟩
  · calc
      x = 2 * (x / 2) := q2679_eq_two_mul_ediv_two hx2
      _ = 2 * a ^ 2 := by rw [hx_div_sq]
  · calc
      y = 2 * (y / 2) := q2679_eq_two_mul_ediv_two hy2
      _ = 2 * b ^ 2 := by rw [hy_div_sq]
```

Notes:

* The key Mathlib API is `exists_associated_pow_of_mul_eq_pow`; over `ℤ`, this gives `Associated (a^2) x`, i.e. a possible sign ambiguity.
* `Int.eq_of_associated_of_nonneg` removes that ambiguity because `a^2 ≥ 0` and the hypotheses give `0 ≤ x`, `0 ≤ y`.
* The witnesses are `|a|` and `|b|`, making their positivity immediate from `x > 0`, `y > 0`.
* For the two-adic variant, `2 ∣ z` follows from `2 ∣ z^2` and primality of `(2 : ℤ)`, then division by two reduces the equation to the first theorem.
