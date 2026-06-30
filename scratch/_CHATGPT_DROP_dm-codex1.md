# Q2376 (dm-codex1): faster integer-to-rational bridge for the Eisenstein quartic

This drop gives a denominator-clearing bridge that avoids the slow standalone rational identity proof. The idea is to prove only tiny cancellation lemmas, multiply the desired rational quartic equation by `n^4`, rewrite the two sides separately, and cancel the final nonzero factor with `mul_right_cancel₀`.

The main speed improvements are:

- no `field_simp` in the bridge;
- no `ring` goals containing variable divisions, except where the division term is treated as an atom in a tiny distributivity lemma;
- the main RHS identity is built from two one-term cancellation lemmas;
- the wrapper lemmas `x = 0 → m = 0` and `x^2 = 1 → m^2 = n^2` also avoid `field_simp`.

The code is standalone. In the project file, omit duplicated definitions and replace the old theorem bodies with these ones.

```lean
import Mathlib.Tactic

/-- Rational affine Eisenstein quartic. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- Rational x-coordinate classification for the Eisenstein quartic. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

/-- Homogeneous integer classification target. -/
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- One-term denominator cancellation for a square. -/
theorem rat_div_pow_two_mul_pow_two (a b : ℚ) (hb : b ≠ 0) :
    (a / b) ^ 2 * b ^ 2 = a ^ 2 := by
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  calc
    (a / b) ^ 2 * b ^ 2
        = (a ^ 2 / b ^ 2) * b ^ 2 := by
            rw [div_pow]
    _ = a ^ 2 := by
            exact div_mul_cancel₀ (a ^ 2) hb2

/-- One-term denominator cancellation for a fourth power. -/
theorem rat_div_pow_four_mul_pow_four (a b : ℚ) (hb : b ≠ 0) :
    (a / b) ^ 4 * b ^ 4 = a ^ 4 := by
  have hb4 : b ^ 4 ≠ 0 := pow_ne_zero 4 hb
  calc
    (a / b) ^ 4 * b ^ 4
        = (a ^ 4 / b ^ 4) * b ^ 4 := by
            rw [div_pow]
    _ = a ^ 4 := by
            exact div_mul_cancel₀ (a ^ 4) hb4

/-- Left side of the rational quartic after multiplying by `n^4`. -/
theorem rat_c_over_nsq_square_mul_denom_four (c n : ℚ) (hn : n ≠ 0) :
    (c / n ^ 2) ^ 2 * n ^ 4 = c ^ 2 := by
  calc
    (c / n ^ 2) ^ 2 * n ^ 4
        = (c / n ^ 2) ^ 2 * (n ^ 2) ^ 2 := by
            rw [show n ^ 4 = (n ^ 2) ^ 2 by ring]
    _ = c ^ 2 := by
            exact rat_div_pow_two_mul_pow_two c (n ^ 2) (pow_ne_zero 2 hn)

/-- The quadratic term of the RHS after multiplying by `n^4`. -/
theorem rat_div_square_mul_denom_four (m n : ℚ) (hn : n ≠ 0) :
    (m / n) ^ 2 * n ^ 4 = m ^ 2 * n ^ 2 := by
  calc
    (m / n) ^ 2 * n ^ 4
        = (m / n) ^ 2 * (n ^ 2 * n ^ 2) := by
            rw [show n ^ 4 = n ^ 2 * n ^ 2 by ring]
    _ = ((m / n) ^ 2 * n ^ 2) * n ^ 2 := by
            rw [← mul_assoc]
    _ = m ^ 2 * n ^ 2 := by
            rw [rat_div_pow_two_mul_pow_two m n hn]

/-- Fast RHS denominator-clearing identity.

This is the replacement for the previously slow all-at-once rational identity.
The only `ring` goal with the quotients present is the tiny distributivity lemma
`(A - B + 1) * D = A * D - B * D + D`, where the quotient expressions are
passed as opaque arguments. -/
theorem rat_quartic_eisenstein_rhs_mul_denom_fast
    (m n : ℚ) (hn : n ≠ 0) :
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4 =
      m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  have h4 : (m / n) ^ 4 * n ^ 4 = m ^ 4 :=
    rat_div_pow_four_mul_pow_four m n hn
  have h2 : (m / n) ^ 2 * n ^ 4 = m ^ 2 * n ^ 2 :=
    rat_div_square_mul_denom_four m n hn
  have hdistrib (A B D : ℚ) : (A - B + 1) * D = A * D - B * D + D := by
    ring
  calc
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4
        = (m / n) ^ 4 * n ^ 4 - (m / n) ^ 2 * n ^ 4 + n ^ 4 := by
            simpa using hdistrib ((m / n) ^ 4) ((m / n) ^ 2) (n ^ 4)
    _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
            rw [h4, h2]

/-- Divide the homogeneous integer equation by `n^4` without using `field_simp`.

The desired rational equation is proved by multiplying both sides by `(n : ℚ)^4`,
rewriting the left and right sides with small lemmas, and cancelling the nonzero
factor. -/
theorem int_to_ratQuarticEisenstein {m n c : ℤ}
    (hn : n ≠ 0)
    (hc : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    RatQuarticEisenstein ((m : ℚ) / (n : ℚ)) ((c : ℚ) / (n : ℚ) ^ 2) := by
  unfold RatQuarticEisenstein
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hn4Q : (n : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hnQ
  have hcQ :
      (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := by
    exact_mod_cast hc
  have hmul :
      (((c : ℚ) / (n : ℚ) ^ 2) ^ 2) * (n : ℚ) ^ 4 =
        (((m : ℚ) / (n : ℚ)) ^ 4 - ((m : ℚ) / (n : ℚ)) ^ 2 + 1) *
          (n : ℚ) ^ 4 := by
    calc
      (((c : ℚ) / (n : ℚ) ^ 2) ^ 2) * (n : ℚ) ^ 4
          = (c : ℚ) ^ 2 := by
              exact rat_c_over_nsq_square_mul_denom_four (c : ℚ) (n : ℚ) hnQ
      _ = (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := hcQ
      _ = (((m : ℚ) / (n : ℚ)) ^ 4 - ((m : ℚ) / (n : ℚ)) ^ 2 + 1) *
            (n : ℚ) ^ 4 := by
              symm
              exact rat_quartic_eisenstein_rhs_mul_denom_fast
                (m : ℚ) (n : ℚ) hnQ
  exact mul_right_cancel₀ hn4Q hmul

/-- No-`field_simp` helper: from `(m/n : ℚ) = 0`, recover `m = 0`. -/
private theorem int_eq_zero_of_rat_div_eq_zero {m n : ℤ}
    (hn : n ≠ 0)
    (h : (m : ℚ) / (n : ℚ) = 0) :
    m = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hmQ : (m : ℚ) = 0 := by
    calc
      (m : ℚ) = ((m : ℚ) / (n : ℚ)) * (n : ℚ) := by
          symm
          exact div_mul_cancel₀ (m : ℚ) hnQ
      _ = 0 * (n : ℚ) := by
          rw [h]
      _ = 0 := by
          ring
  exact_mod_cast hmQ

/-- No-`field_simp` helper: from `(m/n)^2 = 1`, recover `m^2 = n^2`. -/
private theorem int_sq_eq_of_rat_div_sq_eq_one {m n : ℤ}
    (hn : n ≠ 0)
    (h : ((m : ℚ) / (n : ℚ)) ^ 2 = 1) :
    m ^ 2 = n ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
    calc
      (m : ℚ) ^ 2
          = (((m : ℚ) / (n : ℚ)) ^ 2) * (n : ℚ) ^ 2 := by
              symm
              exact rat_div_pow_two_mul_pow_two (m : ℚ) (n : ℚ) hnQ
      _ = 1 * (n : ℚ) ^ 2 := by
          rw [h]
      _ = (n : ℚ) ^ 2 := by
          ring
  exact_mod_cast hQ

/-- The full integer classification follows from the rational x-coordinate theorem,
using the faster bridge above. -/
theorem eisensteinQuarticSquareClassification_of_rat_x
    (hRat : RatQuarticEisensteinXClassification) :
    EisensteinQuarticSquareClassification := by
  unfold EisensteinQuarticSquareClassification
  intro m n c hc
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  · have hcurve :
        RatQuarticEisenstein ((m : ℚ) / (n : ℚ)) ((c : ℚ) / (n : ℚ) ^ 2) :=
      int_to_ratQuarticEisenstein (m := m) (n := n) (c := c) hn hc
    rcases hRat hcurve with hx0 | hx1
    · exact Or.inl (int_eq_zero_of_rat_div_eq_zero (m := m) (n := n) hn hx0)
    · exact Or.inr (Or.inr (int_sq_eq_of_rat_div_sq_eq_one (m := m) (n := n) hn hx1))
```

## If `mul_right_cancel₀` has local inference trouble

Lean 4.31 Mathlib should accept

```lean
exact mul_right_cancel₀ hn4Q hmul
```

in `int_to_ratQuarticEisenstein`. If local inference picks the wrong factor, replace only the final line with the iff-style cancellation form:

```lean
exact (mul_right_inj' hn4Q).mp hmul
```

No mathematical change is involved.

## Small optional micro-`field_simp` variant

If you want a compact benchmark theorem for comparison, this is the only place I would consider using `field_simp`; the goal is tiny and purely rational:

```lean
theorem rat_quartic_eisenstein_rhs_mul_denom_tinyFieldSimp
    (m n : ℚ) (hn : n ≠ 0) :
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4 =
      m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  field_simp [hn]
  ring
```

But the recommended bridge above does not depend on this theorem.
