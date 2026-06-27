# Q1313 (dm1/dm4): closing the cleared-denominator polynomial identity

Use `ring`/`ring_nf`, not `nlinarith`. The reliable sequence is:

```lean
  rw [h]
  field_simp [hBq]
  ring
```

or, if the RHS is still an integer-cast expression, use `ring_nf` as the final step.

Here is the exact standalone pattern.

```lean
import Mathlib

namespace DM4

example (A B : ℤ) (w : ℚ) (hB : B ≠ 0)
    (h : w ^ 2 =
      ((A : ℚ) / (B : ℚ) ^ 2) ^ 3
        + ((A : ℚ) / (B : ℚ) ^ 2) ^ 2
        - (A : ℚ) / (B : ℚ) ^ 2) :
    w ^ 2 * (B : ℚ) ^ 6 =
      (A : ℚ) * ((A : ℚ) ^ 2 + (A : ℚ) * (B : ℚ) ^ 2 - (B : ℚ) ^ 4) := by
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  rw [h]
  field_simp [hBq]
  ring

/-- Same proof when the target RHS is the cast of the integer expression. -/
example (A B : ℤ) (w : ℚ) (hB : B ≠ 0)
    (h : w ^ 2 =
      ((A : ℚ) / (B : ℚ) ^ 2) ^ 3
        + ((A : ℚ) / (B : ℚ) ^ 2) ^ 2
        - (A : ℚ) / (B : ℚ) ^ 2) :
    w ^ 2 * (B : ℚ) ^ 6 =
      ((A * (A ^ 2 + A * B ^ 2 - B ^ 4) : ℤ) : ℚ) := by
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  rw [h]
  field_simp [hBq]
  ring_nf

/-- If you already have the factored cleared form, just rewrite and `ring`. -/
example (A B : ℤ) (w : ℚ)
    (hclear :
      w ^ 2 * (B : ℚ) ^ 6 =
        (A : ℚ) * ((A : ℚ) * ((A : ℚ) + (B : ℚ) ^ 2) - (B : ℚ) ^ 4)) :
    w ^ 2 * (B : ℚ) ^ 6 =
      (A : ℚ) * ((A : ℚ) ^ 2 + (A : ℚ) * (B : ℚ) ^ 2 - (B : ℚ) ^ 4) := by
  rw [hclear]
  ring

end DM4
```

If your denominator hypothesis is `hBpos : 0 < B` instead of `hB : B ≠ 0`, use:

```lean
  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hBpos)
```

Summary: do not use `nlinarith` here. After `field_simp`, the remaining problem is a polynomial identity over `ℚ`, so `ring` is the right closer. Use `ring_nf` when the target still contains a casted integer polynomial such as `((A * (A^2 + A*B^2 - B^4) : ℤ) : ℚ)`.
