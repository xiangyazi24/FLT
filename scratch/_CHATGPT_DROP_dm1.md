# Q1340 (dm1/dm4): `nlinarith` helpers for the `|r|` rewrite

The raw call

```lean
nlinarith [hs_pos, hrpos, sq_abs r, sq_nonneg r]
```

is not the most reliable form. `sq_nonneg r` is irrelevant, and `nlinarith` is happier if you first name the two helper equalities it actually needs:

```lean
have habs2 : |r| ^ 2 = r ^ 2
have hAabs : A = |r| ^ 2
have hAabs4 : A ^ 2 = |r| ^ 4
```

Then `nlinarith` closes the target.

```lean
import Mathlib

namespace DM4

example (A B r s : ℤ)
    (hs_pos : s ^ 2 = A ^ 2 + A * B ^ 2 - B ^ 4)
    (hrpos : A = r ^ 2) :
    s ^ 2 = |r| ^ 4 + |r| ^ 2 * B ^ 2 - B ^ 4 := by
  have habs2 : |r| ^ 2 = r ^ 2 := by
    simpa [pow_two] using (sq_abs r)
  have hAabs : A = |r| ^ 2 := by
    nlinarith [hrpos, habs2]
  have hAabs4 : A ^ 2 = |r| ^ 4 := by
    rw [hAabs]
    ring
  nlinarith [hs_pos, hAabs, hAabs4]

/-- Same proof, using `rw`/`ring`; often more robust than asking `nlinarith` to normalize powers. -/
example (A B r s : ℤ)
    (hs_pos : s ^ 2 = A ^ 2 + A * B ^ 2 - B ^ 4)
    (hrpos : A = r ^ 2) :
    s ^ 2 = |r| ^ 4 + |r| ^ 2 * B ^ 2 - B ^ 4 := by
  have habs2 : |r| ^ 2 = r ^ 2 := by
    simpa [pow_two] using (sq_abs r)
  calc
    s ^ 2 = A ^ 2 + A * B ^ 2 - B ^ 4 := hs_pos
    _ = |r| ^ 4 + |r| ^ 2 * B ^ 2 - B ^ 4 := by
      rw [hrpos, ← habs2]
      ring

end DM4
```

For the final rational cleanup, `rw [hu, hrpos, hr1, hB1]; norm_num` usually does **not** close, because `hr1 : |r| = 1` does not rewrite a bare `r ^ 2`. First prove `A = 1`.

```lean
import Mathlib

namespace DM4

example (A B r : ℤ) (u : ℚ)
    (hu : u = (A : ℚ) / (B : ℚ) ^ 2)
    (hrpos : A = r ^ 2)
    (hr1 : |r| = 1)
    (hB1 : B = 1) :
    u = 1 := by
  have hr_sq_one : r ^ 2 = 1 := by
    calc
      r ^ 2 = |r| ^ 2 := by
        simpa [pow_two] using (sq_abs r).symm
      _ = 1 := by
        rw [hr1]
        norm_num
  have hA_one : A = 1 := by
    rw [hrpos, hr_sq_one]
  rw [hu, hA_one, hB1]
  norm_num

end DM4
```

So the short answer is: yes, `nlinarith` can close the quartic rewrite, but give it `hAabs : A = |r|^2` and preferably `hAabs4 : A^2 = |r|^4`. For `u = 1`, prove `hA_one : A = 1` first; then `rw [hu, hA_one, hB1]; norm_num` closes.
