# Q2366 (dm-codex2): fast integer-to-rational bridge for Eisenstein quartic

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/--
Tiny denominator lemma: no `field_simp`; only `div_pow` and the polynomial
identity `(n^2)^2 = n^4`.
-/
theorem rat_sq_div_sq_eq_div_four (c n : ℚ) :
    (c / n ^ 2) ^ 2 = c ^ 2 / n ^ 4 := by
  rw [div_pow]
  rw [show (n ^ 2) ^ 2 = n ^ 4 by ring]

/--
After multiplication by `n^4`, the rational quartic RHS is the homogeneous
integer numerator.  This is the main anti-blowup lemma: all cancellation is
explicit and local.
-/
theorem rat_quartic_eisenstein_rhs_mul_denom
    (m n : ℚ) (hn : n ≠ 0) :
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4 =
      m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have hterm2 : (m ^ 2 / n ^ 2) * n ^ 4 = m ^ 2 * n ^ 2 := by
    calc
      (m ^ 2 / n ^ 2) * n ^ 4
          = (m ^ 2 / n ^ 2) * (n ^ 2 * n ^ 2) := by
              rw [show n ^ 4 = n ^ 2 * n ^ 2 by ring]
      _ = ((m ^ 2 / n ^ 2) * n ^ 2) * n ^ 2 := by ring
      _ = m ^ 2 * n ^ 2 := by
          rw [div_mul_cancel₀ (m ^ 2) hn2]
  calc
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4
        = (m ^ 4 / n ^ 4 - m ^ 2 / n ^ 2 + 1) * n ^ 4 := by
            rw [div_pow, div_pow]
    _ = (m ^ 4 / n ^ 4) * n ^ 4 -
          (m ^ 2 / n ^ 2) * n ^ 4 + 1 * n ^ 4 := by
            ring
    _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        rw [div_mul_cancel₀ (m ^ 4) hn4, hterm2]
        ring

/--
Division form of the previous lemma.  The only cancellation is by the single
nonzero denominator `n^4`.
-/
theorem rat_quartic_eisenstein_rhs_eq_div
    (m n : ℚ) (hn : n ≠ 0) :
    (m / n) ^ 4 - (m / n) ^ 2 + 1 =
      (m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) / n ^ 4 := by
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 hn
  apply mul_right_cancel₀ hn4
  calc
    ((m / n) ^ 4 - (m / n) ^ 2 + 1) * n ^ 4
        = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 :=
            rat_quartic_eisenstein_rhs_mul_denom m n hn
    _ = ((m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) / n ^ 4) * n ^ 4 := by
        exact (div_mul_cancel₀ (m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) hn4).symm

/--
Integer homogeneous Eisenstein quartic equation gives the affine rational C12
equation at `x = m/n`, `y = c/n^2`.

This avoids `field_simp` at the final large expression.  The proof only casts
the integer identity, rewrites the LHS by `rat_sq_div_sq_eq_div_four`, and
rewrites the RHS by `rat_quartic_eisenstein_rhs_eq_div`.
-/
theorem int_to_ratQuarticEisenstein
    {m n c : ℤ}
    (h : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4)
    (hn : n ≠ 0) :
    ((c : ℚ) / (n : ℚ) ^ 2) ^ 2 =
      ((m : ℚ) / (n : ℚ)) ^ 4 -
        ((m : ℚ) / (n : ℚ)) ^ 2 + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hQ :
      (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := by
    exact_mod_cast h
  calc
    ((c : ℚ) / (n : ℚ) ^ 2) ^ 2
        = (c : ℚ) ^ 2 / (n : ℚ) ^ 4 :=
            rat_sq_div_sq_eq_div_four (c : ℚ) (n : ℚ)
    _ = ((m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4) /
          (n : ℚ) ^ 4 := by
            rw [hQ]
    _ = ((m : ℚ) / (n : ℚ)) ^ 4 -
          ((m : ℚ) / (n : ℚ)) ^ 2 + 1 := by
            rw [← rat_quartic_eisenstein_rhs_eq_div (m : ℚ) (n : ℚ) hnQ]

/-- If `m/n = 0` over `ℚ` and `n ≠ 0`, then `m = 0` over `ℤ`. -/
theorem int_eq_zero_of_rat_div_eq_zero
    {m n : ℤ}
    (hn : n ≠ 0)
    (h : (m : ℚ) / (n : ℚ) = 0) :
    m = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hmQ : (m : ℚ) = 0 := by
    calc
      (m : ℚ) = ((m : ℚ) / (n : ℚ)) * (n : ℚ) := by
        exact (div_mul_cancel₀ (m : ℚ) hnQ).symm
      _ = 0 := by
        simp [h]
  exact_mod_cast hmQ

/-- If `(m/n)^2 = 1` over `ℚ` and `n ≠ 0`, then `m^2 = n^2` over `ℤ`. -/
theorem int_sq_eq_sq_of_rat_div_sq_eq_one
    {m n : ℤ}
    (hn : n ≠ 0)
    (h : ((m : ℚ) / (n : ℚ)) ^ 2 = 1) :
    m ^ 2 = n ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hnQ2 : (n : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hnQ
  have hmnQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
    calc
      (m : ℚ) ^ 2
          = (((m : ℚ) / (n : ℚ)) ^ 2) * (n : ℚ) ^ 2 := by
              rw [div_pow]
              exact (div_mul_cancel₀ ((m : ℚ) ^ 2) hnQ2).symm
      _ = 1 * (n : ℚ) ^ 2 := by
          rw [h]
      _ = (n : ℚ) ^ 2 := by
          ring
  exact_mod_cast hmnQ

/--
Wrapper from rational C12 classification to the homogeneous integer
classification frontier.

Use this when the rational theorem is available in the form
`∀ {x y : ℚ}, y^2 = x^4 - x^2 + 1 → x = 0 ∨ x^2 = 1`.
-/
theorem eisensteinQuarticSquareClassification_of_ratC12
    (hRat : ∀ {x y : ℚ},
      y ^ 2 = x ^ 4 - x ^ 2 + 1 → x = 0 ∨ x ^ 2 = 1) :
    EisensteinQuarticSquareClassification := by
  intro m n c h
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  · have hrat :
        ((c : ℚ) / (n : ℚ) ^ 2) ^ 2 =
          ((m : ℚ) / (n : ℚ)) ^ 4 -
            ((m : ℚ) / (n : ℚ)) ^ 2 + 1 :=
        int_to_ratQuarticEisenstein (m := m) (n := n) (c := c) h hn
    have hx :
        (m : ℚ) / (n : ℚ) = 0 ∨
          ((m : ℚ) / (n : ℚ)) ^ 2 = 1 :=
      hRat
        (x := (m : ℚ) / (n : ℚ))
        (y := (c : ℚ) / (n : ℚ) ^ 2)
        hrat
    rcases hx with hx0 | hx1
    · exact Or.inl (int_eq_zero_of_rat_div_eq_zero hn hx0)
    · exact Or.inr (Or.inr (int_sq_eq_sq_of_rat_div_sq_eq_one hn hx1))

end MazurProof.RationalPointsN12
```

## Notes

The code avoids the slow path entirely.  There is no global `field_simp` and no large `ring_nf` on the original rational expression.  The only denominator cancellation happens in these two tiny places:

```lean
div_mul_cancel₀ (m ^ 2) hn2
div_mul_cancel₀ (m ^ 4) hn4
```

and once in the final single-denominator lemma by `mul_right_cancel₀ hn4`.

The shape to test incrementally is:

1. `rat_sq_div_sq_eq_div_four`
2. `rat_quartic_eisenstein_rhs_mul_denom`
3. `rat_quartic_eisenstein_rhs_eq_div`
4. `int_to_ratQuarticEisenstein`
5. the two back-conversion helpers
6. `eisensteinQuarticSquareClassification_of_ratC12`

If `exact_mod_cast h` in `int_to_ratQuarticEisenstein` is sensitive in the repo context, replace only that block by the more explicit variant below:

```lean
  have hQ' :
      ((c ^ 2 : ℤ) : ℚ) =
        ((m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 : ℤ) : ℚ) := by
    exact_mod_cast h
  have hQ :
      (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - (m : ℚ) ^ 2 * (n : ℚ) ^ 2 + (n : ℚ) ^ 4 := by
    simpa using hQ'
```

That fallback is still fast because it only asks the simplifier to commute casts through one fixed polynomial identity; it does not search through field denominators.
