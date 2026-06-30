# Q2360 (dm-codex1): Lean reduction from integer Eisenstein quartic to rational x-classification

## Goal

You have the integer classification target

```lean
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2
```

and want to reduce it to the rational affine quartic x-coordinate classification

```lean
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1
```

The reduction is exactly: if `n ≠ 0`, divide the homogeneous equation by `n^4` and set

```lean
x = (m : ℚ) / (n : ℚ)
y = (c : ℚ) / (n : ℚ) ^ 2
```

Then `x = 0` gives `m = 0`, and `x ^ 2 = 1` gives `m ^ 2 = n ^ 2`. The `n = 0` case is handled before forming `m/n`.

## Lean code

The code below is meant to be pasted in the same namespace as the three definitions above. In the project file, you probably already have enough imports; standalone, `import Mathlib` is sufficient for `field_simp`, `ring_nf`, and `exact_mod_cast`.

```lean
import Mathlib

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

1. The proof deliberately splits on `n = 0` first. The rational point construction only happens in the `n ≠ 0` branch.

2. The conclusion from the rational branch `x ^ 2 = 1` is `m ^ 2 = n ^ 2`, not `m = n`. This correctly keeps the `m = -n` diagonal case.

3. The rational classification theorem must not be strengthened to `x = 0 ∨ x = 1`; `x = -1` is also a rational point and corresponds to `m = -n`.

4. The reduction does not require coprimality of `m,n`. It uses only the nonzero denominator `n ≠ 0` and the homogeneous equation.

5. The theorem proves exactly the current integer interface: `m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2`. It does not rule out diagonal residuals, which are genuine solutions.
