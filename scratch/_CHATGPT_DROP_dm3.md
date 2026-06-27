# Q1296 (dm3): clearing denominators on `w^2 = u^3 + u^2 - u`

## Executive answer

You do **not** need a special `Rat` denominator lemma.

I would not try to prove directly that the denominator of `q` is `1`.  The clean Mathlib route is:

1. From `q^2 = (N : ℚ)`, prove `q` is integral over `ℤ`, because it is a root of the monic polynomial `X^2 - C N`.
2. Use that `ℤ` is integrally closed in `ℚ`:

```lean
(IsIntegrallyClosed.isIntegral_iff (A := ℤ) (K := ℚ)).mp hq_int
```

This gives `∃ C : ℤ, (C : ℚ) = q`.  So the lemma you want is not specifically a rational-denominator lemma; it is an immediate corollary of the integral-closure API.

Also, the “non-negative integer” observation is not needed.  If `q^2` is an integer, then `q` is an algebraic integer and rational, hence an integer.  The sign is irrelevant.

## Lean code

The following is the concrete code shape I would use.

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.RingTheory.IntegralClosure
import Mathlib.Tactic

noncomputable section

namespace FLT.DM3

open Polynomial

/-- If a rational square is an integer, then the rational is an integer.

This avoids all low-level `Rat.num`/`Rat.den` normalization API.  The proof is:
`q` is a root of the monic polynomial `X^2 - N`, hence integral over `ℤ`; since
`ℤ` is integrally closed in `ℚ`, it lies in the image of `ℤ`. -/
lemma rat_mem_int_range_of_sq_mem_int_range
    (q : ℚ) (N : ℤ) (h : q ^ 2 = (N : ℚ)) :
    ∃ C : ℤ, q = (C : ℚ) := by
  have hq_int : IsIntegral ℤ q := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C N, ?_, ?_⟩
    · simpa using
        (Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) (a := N))
    · simp [h]
  obtain ⟨C, hC⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (A := ℤ) (K := ℚ)).mp hq_int
  exact ⟨C, hC.symm⟩

/-- Denominator clearing for

`u = A / B^2`, `w^2 = u^3 + u^2 - u`.

The output is the integer square equation

`C^2 = A * (A^2 + A * B^2 - B^4)`.
-/
theorem clear_denominators_to_integer_square
    (A B : ℤ) (hB : 0 < B) (u w : ℚ)
    (hu : u = (A : ℚ) / (B : ℚ) ^ 2)
    (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ C : ℤ, C ^ 2 = A * (A ^ 2 + A * B ^ 2 - B ^ 4) := by
  let N : ℤ := A * (A ^ 2 + A * B ^ 2 - B ^ 4)

  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hB)

  have hsq : (w * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    calc
      (w * (B : ℚ) ^ 3) ^ 2
          = w ^ 2 * (B : ℚ) ^ 6 := by
            ring
      _ = (u ^ 3 + u ^ 2 - u) * (B : ℚ) ^ 6 := by
            rw [hw]
      _ = (N : ℚ) := by
            rw [hu]
            field_simp [hBq, N]
            ring

  obtain ⟨C, hC⟩ :=
    rat_mem_int_range_of_sq_mem_int_range
      (q := w * (B : ℚ) ^ 3) (N := N) hsq

  refine ⟨C, ?_⟩
  change C ^ 2 = N
  have hcast : ((C ^ 2 : ℤ) : ℚ) = (N : ℚ) := by
    change (C : ℚ) ^ 2 = (N : ℚ)
    rw [← hC]
    exact hsq
  exact_mod_cast hcast

end FLT.DM3
```

## Notes on the important lines

### 1. The key “`q^2 ∈ ℤ` implies `q ∈ ℤ`” lemma

The important part is:

```lean
have hq_int : IsIntegral ℤ q := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C N, ?_, ?_⟩
  · simpa using
      (Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) (a := N))
  · simp [h]
```

This says `q` satisfies the monic polynomial `X^2 - N`.  Then:

```lean
obtain ⟨C, hC⟩ :=
  (IsIntegrallyClosed.isIntegral_iff (A := ℤ) (K := ℚ)).mp hq_int
```

turns rational integrality into being an actual integer.

So the answer to “does Mathlib have this?” is: it may not have this exact `Rat` lemma under that name, but it has the better general theorem via `IsIntegral` and `IsIntegrallyClosed`.

### 2. The denominator clearing calculation

The whole denominator clearing step is this block:

```lean
have hsq : (w * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
  calc
    (w * (B : ℚ) ^ 3) ^ 2
        = w ^ 2 * (B : ℚ) ^ 6 := by
          ring
    _ = (u ^ 3 + u ^ 2 - u) * (B : ℚ) ^ 6 := by
          rw [hw]
    _ = (N : ℚ) := by
          rw [hu]
          field_simp [hBq, N]
          ring
```

The only denominator hypothesis needed by `field_simp` is:

```lean
have hBq : (B : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt hB)
```

Since all denominators are powers of `(B : ℚ)`, `field_simp [hBq, N]` clears them, and `ring` proves the polynomial identity.

### 3. Casting back from `ℚ` to `ℤ`

After obtaining `hC : w * B^3 = C` in `ℚ`, use the rational square identity and injectivity of `Int.cast` into `ℚ`:

```lean
have hcast : ((C ^ 2 : ℤ) : ℚ) = (N : ℚ) := by
  change (C : ℚ) ^ 2 = (N : ℚ)
  rw [← hC]
  exact hsq
exact_mod_cast hcast
```

That is usually more robust than manually rewriting `Int.cast_pow`, `Int.cast_mul`, etc.

## If `monic_X_pow_sub_C` is not in scope

In some import configurations, the only fragile line is the monicity proof:

```lean
Polynomial.monic_X_pow_sub_C
```

If Lean cannot find it, keep the same proof but add a stronger polynomial import, for example:

```lean
import Mathlib.RingTheory.Polynomial.Basic
```

or search/check:

```lean
#check Polynomial.monic_X_pow_sub_C
#check IsIntegrallyClosed.isIntegral_iff
```

The mathematical dependency is still minimal: polynomial monicity plus integral closure of `ℤ` in `ℚ`.
