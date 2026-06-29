# Q2191 Lean drop: elementary wrapper for the N=12 affine rational-points boundary

This is the elementary wrapper layer for `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.  It should live in the existing namespace:

```lean
namespace MazurProof.RationalPointsN12
```

The hard arithmetic theorem is **not** introduced as an axiom here.  It is passed as a hypothesis:

```lean
∀ u w : ℚ,
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
  N12DegenerateXQ u
```

The code below is intentionally staged into small lemmas:

1. `N12DegenerateXQ`: the five degenerate rational `u`-values.
2. `square_denominator_int_dvd_of_rat_eq_int`: if `A / B^2` is an integer, then `B ∣ A`.
3. `primitive_square_denominator_ne_int`: primitive `A/B^2` with `1 < B` cannot be any integer.
4. `primitive_square_denominator_not_N12DegenerateXQ`: five-case contradiction for `-2,0,1,2,4`.
5. `square_denominator_rational_curve_equation`: denominator clearing from the integral model to the rational curve.
6. `N12NoNontrivialSquareDenominatorResidual_of_affine_boundary`: wrapper from the rational-points boundary to the existing residual.

## Proposed Lean code

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Degenerate affine `u`-coordinates for the N=12 obstruction curve. -/
def N12DegenerateXQ (u : ℚ) : Prop :=
  u = (-2 : ℚ) ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

/--
If `A / B^2` is an integer and `B ≠ 0`, then `B ∣ A`.
This is the denominator-clearing helper used for all five degenerate values.
-/
private theorem square_denominator_int_dvd_of_rat_eq_int
    (A B m : ℤ) (hBne : B ≠ 0)
    (h : (A : ℚ) / (B : ℚ) ^ 2 = (m : ℚ)) :
    B ∣ A := by
  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast hBne
  have hBsq : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBq
  have hAq : (A : ℚ) = (m : ℚ) * (B : ℚ) ^ 2 := by
    calc
      (A : ℚ) = ((A : ℚ) / (B : ℚ) ^ 2) * (B : ℚ) ^ 2 := by
        exact (div_mul_cancel₀ (A : ℚ) hBsq).symm
      _ = (m : ℚ) * (B : ℚ) ^ 2 := by
        rw [h]
  have hAq' : (A : ℚ) = ((m * B ^ 2 : ℤ) : ℚ) := by
    rw [hAq]
    push_cast
    ring
  have hAint : A = m * B ^ 2 := by
    exact_mod_cast hAq'
  rw [hAint]
  exact dvd_mul_of_dvd_right
    (dvd_pow_self B (by norm_num : (2 : ℕ) ≠ 0)) m

/--
A primitive square denominator with `1 < B` cannot represent any integer.
This single lemma handles `-2`, `0`, `1`, `2`, and `4`.
-/
theorem primitive_square_denominator_ne_int
    (A B m : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    (A : ℚ) / (B : ℚ) ^ 2 ≠ (m : ℚ) := by
  intro h
  have hBne : B ≠ 0 := by omega
  have hBdvdA : B ∣ A :=
    square_denominator_int_dvd_of_rat_eq_int A B m hBne h
  have hBdvdgcd : B ∣ ((Int.gcd A B : ℕ) : ℤ) := by
    exact Int.dvd_coe_gcd hBdvdA (dvd_refl B)
  have hBdvd1 : B ∣ (1 : ℤ) := by
    simpa [hcop] using hBdvdgcd
  have hunit : IsUnit B := isUnit_of_dvd_one hBdvd1
  have hBabs : |B| = 1 := Int.isUnit_iff_abs_eq.mp hunit
  have hBnonneg : 0 ≤ B := by omega
  rw [Int.abs_of_nonneg hBnonneg] at hBabs
  omega

/-- The primitive square-denominator `u = A/B^2` is not one of the five degenerate values. -/
theorem primitive_square_denominator_not_N12DegenerateXQ
    (A B : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    ¬ N12DegenerateXQ ((A : ℚ) / (B : ℚ) ^ 2) := by
  intro hdeg
  rcases hdeg with hneg2 | hzero | hone | htwo | hfour
  · exact (primitive_square_denominator_ne_int A B (-2) hBgt hcop) (by simpa using hneg2)
  · exact (primitive_square_denominator_ne_int A B 0 hBgt hcop) (by simpa using hzero)
  · exact (primitive_square_denominator_ne_int A B 1 hBgt hcop) (by simpa using hone)
  · exact (primitive_square_denominator_ne_int A B 2 hBgt hcop) (by simpa using htwo)
  · exact (primitive_square_denominator_ne_int A B 4 hBgt hcop) (by simpa using hfour)

/--
Denominator clearing from the integral square-denominator model to the rational
affine curve equation.

This is the normalization lemma for
`u = A/B^2`, `w = C/B^3`.
-/
theorem square_denominator_rational_curve_equation
    (A B C : ℤ)
    (hBne : B ≠ 0)
    (hC : C ^ 2 =
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    ((C : ℚ) / (B : ℚ) ^ 3) ^ 2 =
      ((A : ℚ) / (B : ℚ) ^ 2) ^ 3 -
        ((A : ℚ) / (B : ℚ) ^ 2) ^ 2 -
          4 * ((A : ℚ) / (B : ℚ) ^ 2) + 4 := by
  have hBq : (B : ℚ) ≠ 0 := by
    exact_mod_cast hBne
  have hB2 : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBq
  have hB3 : (B : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hBq
  have hB4 : (B : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hBq
  have hB5 : (B : ℚ) ^ 5 ≠ 0 := pow_ne_zero 5 hBq
  have hB6 : (B : ℚ) ^ 6 ≠ 0 := pow_ne_zero 6 hBq
  have hCq :
      (C : ℚ) ^ 2 =
        ((A : ℚ) - (B : ℚ) ^ 2) *
          ((A : ℚ) - 2 * (B : ℚ) ^ 2) *
            ((A : ℚ) + 2 * (B : ℚ) ^ 2) := by
    exact_mod_cast hC
  field_simp [hBq, hB2, hB3, hB4, hB5, hB6]
  ring_nf at hCq ⊢
  exact hCq

/--
Wrapper from an affine rational-points boundary to the existing denominator residual.

No new axiom is introduced: the hard arithmetic theorem is an explicit hypothesis.
-/
theorem N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (hboundary : ∀ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
      N12DegenerateXQ u) :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  let u : ℚ := (A : ℚ) / (B : ℚ) ^ 2
  let w : ℚ := (C : ℚ) / (B : ℚ) ^ 3
  have hBne : B ≠ 0 := by omega
  have hcurve : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := by
    dsimp [u, w]
    exact square_denominator_rational_curve_equation
      (A := A) (B := B) (C := C) hBne hC
  have hdeg : N12DegenerateXQ u := hboundary u w hcurve
  exact primitive_square_denominator_not_N12DegenerateXQ A B hBgt hcop hdeg

end MazurProof.RationalPointsN12
```

## Likely brittle lines and alternatives

The code above is designed to be close to sorry-free under Mathlib v4.31.0-rc2, but these are the lines most likely to need local edits.

### `exact_mod_cast hAq'`

If this fails in `square_denominator_int_dvd_of_rat_eq_int`, use explicit injectivity of the integer cast to `ℚ`:

```lean
  have hAint : A = m * B ^ 2 := by
    exact Int.cast_injective hAq'
```

If Lean cannot infer the codomain:

```lean
  have hAint : A = m * B ^ 2 := by
    exact (Int.cast_injective (R := ℚ)) hAq'
```

### `exact_mod_cast hC`

If the integral model does not cast cleanly to the rational equality, split it into a raw cast and a normalization step:

```lean
  have hCq0 :
      ((C ^ 2 : ℤ) : ℚ) =
        (((A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) : ℤ) : ℚ) := by
    exact_mod_cast hC
  have hCq :
      (C : ℚ) ^ 2 =
        ((A : ℚ) - (B : ℚ) ^ 2) *
          ((A : ℚ) - 2 * (B : ℚ) ^ 2) *
            ((A : ℚ) + 2 * (B : ℚ) ^ 2) := by
    push_cast at hCq0
    simpa [pow_two] using hCq0
```

### `field_simp [hBq, hB2, hB3, hB4, hB5, hB6]`

If `field_simp` asks for more nonzero side conditions, add the corresponding powers:

```lean
  have hB7 : (B : ℚ) ^ 7 ≠ 0 := pow_ne_zero 7 hBq
  have hB8 : (B : ℚ) ^ 8 ≠ 0 := pow_ne_zero 8 hBq
  field_simp [hBq, hB2, hB3, hB4, hB5, hB6, hB7, hB8]
```

If the final equality is oriented the other way after `ring_nf`, use:

```lean
  exact hCq.symm
```

If the post-`field_simp` expression keeps powers arranged differently, keep the same structure and add one more normalization line:

```lean
  ring_nf at hCq ⊢
  nlinarith [hCq]
```

The equality is polynomial after denominators are cleared, so `ring_nf` should usually suffice.

### `Int.dvd_coe_gcd`

The intended v4.31-style call is:

```lean
have hBdvdgcd : B ∣ ((Int.gcd A B : ℕ) : ℤ) := by
  exact Int.dvd_coe_gcd hBdvdA (dvd_refl B)
```

where the first proof is `B ∣ A` and the second is `B ∣ B`.  If the target is written with a slightly different cast, normalize it to exactly:

```lean
B ∣ ((Int.gcd A B : ℕ) : ℤ)
```

before applying the lemma.

### `Int.isUnit_iff_abs_eq`

If this theorem is not imported by the local import stack, `import Mathlib` certainly provides it.  If the project file avoids `import Mathlib`, add the narrower import providing integer unit/order facts, or replace the unit step by cases on the divisor of `1`:

```lean
  rcases hBdvd1 with ⟨t, ht⟩
  have ht' : B * t = 1 := ht.symm
  -- Then use integer order/case analysis, or derive `|B| = 1` through `IsUnit`.
```

The `IsUnit` route is much cleaner.

## Why this wrapper is the right boundary

The theorem

```lean
N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
```

is exactly the formalization cut recommended in Q2186.  The hard arithmetic input is the affine rational-points theorem; everything here is elementary denominator clearing and primitive-denominator contradiction.

This layer deliberately avoids the false global sign statement

```lean
B ^ 2 ∣ C - z ^ 3 ∨ B ^ 2 ∣ C + z ^ 3
```

which is not valid for composite `B`: different odd prime powers can choose different CRT signs, and the prime `2` must be handled separately.