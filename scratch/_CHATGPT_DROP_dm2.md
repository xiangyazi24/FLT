# Q1563 (dm2/dm3): parity and mod-4 divisibility for the even branch

Here is the direct `substitute + ring + omega` version.  I am assuming the variables are integers (`ℤ`), which matches the `%`, divisibility, and subtraction usage in the descent algebra.

The three requested local facts are named:

```lean
hs_odd
hdiv_sub
hdiv_add
```

## Lean code

```lean
import Mathlib

namespace FLT.DM3

/-- If `r` is odd, `4 ∣ B`, and
`s^2 = r^4 + r^2 B^2 - B^4`, then `s` is odd and both raw
factors `2*r^2 + B^2 ± 2*s` are divisible by `4`.

This proof intentionally follows the substitute-ring-omega pattern:
first write `B = 4*k` and `r = 2*j+1`, then use `ring_nf`/`ring` and
`omega` for the modular arithmetic. -/
theorem s_odd_and_four_dvd_raw_factors
    {r B s : ℤ}
    (hr : r % 2 = 1)
    (hB4 : (4 : ℤ) ∣ B)
    (hsq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    s % 2 = 1 ∧
      (4 : ℤ) ∣ (2 * r ^ 2 + B ^ 2 - 2 * s) ∧
      (4 : ℤ) ∣ (2 * r ^ 2 + B ^ 2 + 2 * s) := by
  obtain ⟨k, rfl⟩ := hB4
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r = 2 * j + 1 := by
    refine ⟨r / 2, ?_⟩
    omega

  have hs_odd : s % 2 = 1 := by
    have hs_cases : s % 2 = 0 ∨ s % 2 = 1 := by
      omega
    rcases hs_cases with hs_even | hs_odd
    · obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t := by
        refine ⟨s / 2, ?_⟩
        omega
      subst s
      ring_nf at hsq
      omega
    · exact hs_odd

  have hdiv_sub :
      (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t + 1 := by
      refine ⟨s / 2, ?_⟩
      omega
    subst s
    refine ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 - t, ?_⟩
    ring

  have hdiv_add :
      (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t + 1 := by
      refine ⟨s / 2, ?_⟩
      omega
    subst s
    refine ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 + t + 1, ?_⟩
    ring

  exact ⟨hs_odd, hdiv_sub, hdiv_add⟩

end FLT.DM3
```

## Drop-in local snippet

If you already have a surrounding theorem with hypotheses

```lean
hr  : r % 2 = 1
hB4 : (4 : ℤ) ∣ B
hsq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4
```

then the body is exactly the same core block:

```lean
  obtain ⟨k, rfl⟩ := hB4
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r = 2 * j + 1 := by
    refine ⟨r / 2, ?_⟩
    omega

  have hs_odd : s % 2 = 1 := by
    have hs_cases : s % 2 = 0 ∨ s % 2 = 1 := by
      omega
    rcases hs_cases with hs_even | hs_odd
    · obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t := by
        refine ⟨s / 2, ?_⟩
        omega
      subst s
      ring_nf at hsq
      omega
    · exact hs_odd

  have hdiv_sub :
      (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t + 1 := by
      refine ⟨s / 2, ?_⟩
      omega
    subst s
    refine ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 - t, ?_⟩
    ring

  have hdiv_add :
      (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, s = 2 * t + 1 := by
      refine ⟨s / 2, ?_⟩
      omega
    subst s
    refine ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 + t + 1, ?_⟩
    ring
```

After the two `obtain ... rfl` substitutions, the requested divisibility targets are exactly the rewritten forms shown above.  If the surrounding goal still displays the original `r` and `B`, `exact hdiv_sub` and `exact hdiv_add` should elaborate after the substitutions have rewritten the context.
