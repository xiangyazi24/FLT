# Q2360 (dm-codex1): Lean reduction from integer Eisenstein quartic to rational x-classification

This is the connector-only git drop for the requested Lean/math consultation. The goal is to reduce the homogeneous integer statement

```lean
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2
```

to the rational affine quartic x-coordinate statement

```lean
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1
```

The reduction is exactly the expected division by `n^4`: for `n ≠ 0`, set

```lean
x = (m : ℚ) / (n : ℚ)
y = (c : ℚ) / (n : ℚ) ^ 2
```

Then the homogeneous equation becomes `y^2 = x^4 - x^2 + 1`. In the classification wrapper, split first on `n = 0`; otherwise apply the rational theorem to `x = m/n`. The branch `x = 0` gives `m = 0`, and the branch `x^2 = 1` gives `m^2 = n^2`.

## Lean code

Paste this in the same namespace as the existing project definitions. If the file already has the three definitions, omit the repeated definition block below and keep the helper lemmas plus the two requested theorems.

```lean
import Mathlib

/-- Rational affine Eisenstein quartic. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- The rational x-coordinate classification needed for the homogeneous integer result. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

/-- Homogeneous integer Eisenstein quartic square classification. -/
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- Divide the homogeneous integer equation by `n^4` and view it as a rational point
on `y^2 = x^4 - x^2 + 1`, with `x = m/n` and `y = c/n^2`. -/
theorem int_to_ratQuarticEisenstein {m n c : ℤ}
    (hn : n ≠ 0)
    (hc : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    RatQuarticEisenstein ((m : ℚ) / (n : ℚ)) ((c : ℚ) / (n : ℚ) ^ 2) := by
  unfold RatQuarticEisenstein
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hcQ :
      (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := by
    exact_mod_cast hc
  calc
    ((c : ℚ) / (n : ℚ) ^ 2) ^ 2
        = (c : ℚ) ^ 2 / (n : ℚ) ^ 4 := by
            field_simp [hnQ]
            ring_nf
    _ = ((m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4) /
          (n : ℚ) ^ 4 := by
            rw [hcQ]
    _ = ((m : ℚ) / (n : ℚ)) ^ 4 - ((m : ℚ) / (n : ℚ)) ^ 2 + 1 := by
            field_simp [hnQ]
            ring_nf

private lemma int_eq_zero_of_rat_div_eq_zero {m n : ℤ}
    (hn : n ≠ 0)
    (h : (m : ℚ) / (n : ℚ) = 0) :
    m = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hmQ : (m : ℚ) = 0 := by
    field_simp [hnQ] at h
    simpa using h
  exact_mod_cast hmQ

private lemma int_sq_eq_of_rat_div_sq_eq_one {m n : ℤ}
    (hn : n ≠ 0)
    (h : ((m : ℚ) / (n : ℚ)) ^ 2 = 1) :
    m ^ 2 = n ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have h' : (m : ℚ) ^ 2 / (n : ℚ) ^ 2 = 1 := by
    simpa [div_pow] using h
  have hQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
    field_simp [hnQ] at h'
    simpa using h'
  exact_mod_cast hQ

/-- The integer homogeneous classification follows from the rational x-coordinate
classification on `y^2 = x^4 - x^2 + 1`. -/
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

## Notes and sanity checks

1. The wrapper deliberately splits on `n = 0` before forming the rational point. This avoids any hidden denominator obligation.

2. The conclusion from the rational branch `x ^ 2 = 1` is `m ^ 2 = n ^ 2`, not `m = n`. This keeps both diagonal possibilities `m = n` and `m = -n`.

3. The rational x-classification must not be strengthened to `x = 0 ∨ x = 1`; the point with `x = -1` is real and corresponds to `m = -n`.

4. No coprimality assumption on `m,n` is needed for this reduction. The only denominator hypothesis is `n ≠ 0`.

5. This proves exactly the current integer interface `m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2`. It intentionally does not rule out diagonal residuals, since those are genuine solutions.
