# Q1316 (dm1/dm2): exact tactic for the final cleared-denominator square

Do **not** use `nlinarith`, `linarith`, or `linear_combination` for this final step. The robust tactic is:

```lean
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hBne
  calc
    (w * (B : ℚ) ^ 3) ^ 2 = w ^ 2 * (B : ℚ) ^ 6 := by ring
    _ = ((A * (A ^ 2 + A * B ^ 2 - B ^ 4) : ℤ) : ℚ) := by
      rw [h]
      field_simp [hBq]
      ring_nf
```

Here is the standalone version.

```lean
import Mathlib

namespace DM2

example (A B : ℤ) (w : ℚ) (hBne : B ≠ 0)
    (h : w ^ 2 =
      ((A : ℚ) / (B : ℚ) ^ 2) ^ 3
        + ((A : ℚ) / (B : ℚ) ^ 2) ^ 2
        - (A : ℚ) / (B : ℚ) ^ 2) :
    (w * (B : ℚ) ^ 3) ^ 2 =
      ((A * (A ^ 2 + A * B ^ 2 - B ^ 4) : ℤ) : ℚ) := by
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hBne
  calc
    (w * (B : ℚ) ^ 3) ^ 2 = w ^ 2 * (B : ℚ) ^ 6 := by ring
    _ = ((A * (A ^ 2 + A * B ^ 2 - B ^ 4) : ℤ) : ℚ) := by
      rw [h]
      field_simp [hBq]
      ring_nf

end DM2
```

If you already made a cleared hypothesis first, use this shape:

```lean
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hBne
  have hclear := h
  field_simp [hBq] at hclear
  calc
    (w * (B : ℚ) ^ 3) ^ 2 = w ^ 2 * (B : ℚ) ^ 6 := by ring
    _ = ((A * (A ^ 2 + A * B ^ 2 - B ^ 4) : ℤ) : ℚ) := by
      rw [hclear]
      ring_nf
```

The reason this works is that the first `ring` only expands `(w * B^3)^2` into `w^2 * B^6`; the second block uses the original curve equation, clears denominators with `field_simp`, and lets `ring_nf` normalize the factored rational expression and the `Int.cast` target to the same polynomial.
