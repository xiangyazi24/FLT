# Q2190 Lean drop: elementary wrapper for the N=12 affine rational-points boundary

This is the wrapper layer I would add in `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, in namespace

```lean
namespace MazurProof.RationalPointsN12
```

The intended boundary is passed as a hypothesis, not introduced as an axiom:

```lean
∀ u w : ℚ,
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
  N12DegenerateXQ u
```

The elementary work is:

1. define the degenerate rational `u`-values;
2. show a primitive square denominator `A/B^2`, `1 < B`, `gcd A B = 1`, cannot equal any integer, hence cannot equal `-2,0,1,2,4`;
3. clear denominators from the integral model to the affine equation;
4. wrap the rational-points boundary into `N12NoNontrivialSquareDenominatorResidual`.

## Drop-in code

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Degenerate affine `u`-coordinates for the N=12 obstruction curve. -/
def N12DegenerateXQ (u : ℚ) : Prop :=
  u = (-2 : ℚ) ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

/--
If `A / B^2` is an integer and `B ≠ 0`, then `B ∣ A`.
This is the denominator-clearing helper for the five degenerate values.
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
This single lemma handles the five values `-2, 0, 1, 2, 4`.
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

This is the key normalization lemma for
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
  have hB6 : (B : ℚ) ^ 6 ≠ 0 := pow_ne_zero 6 hBq
  have hCq :
      (C : ℚ) ^ 2 =
        ((A : ℚ) - (B : ℚ) ^ 2) *
          ((A : ℚ) - 2 * (B : ℚ) ^ 2) *
            ((A : ℚ) + 2 * (B : ℚ) ^ 2) := by
    exact_mod_cast hC
  field_simp [hBq, hB2, hB3, hB6]
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

## If one of the brittle lines fails

The helper lemmas above are intended to be sorry-free.  These are the only lines I would expect to need local editing in Mathlib v4.31.0-rc2.

### 1. `exact_mod_cast hAq'`

If this line fails in `square_denominator_int_dvd_of_rat_eq_int`, replace it with the explicit injectivity route:

```lean
  have hAint : A = m * B ^ 2 := by
    exact Int.cast_injective hAq'
```

If `Int.cast_injective` does not resolve the codomain, make the target explicit:

```lean
  have hAint : A = m * B ^ 2 := by
    exact (Int.cast_injective (R := ℚ)) hAq'
```

### 2. `exact_mod_cast hC`

If the cast of the integral model to `ℚ` fails, use a two-step cast plus normalization:

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
    simpa using hCq0
```

If `simpa` is not enough, use:

```lean
    push_cast at hCq0
    simpa [pow_two] using hCq0
```

### 3. `field_simp [hBq, hB2, hB3, hB6]`

If `field_simp` leaves side goals, add the exact nonzero denominators it asks for.  Usually these are powers of `(B : ℚ)` or products of such powers, all solved by `simp [hBq]` or `positivity`-free `pow_ne_zero`:

```lean
  have hB4 : (B : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 hBq
  have hB5 : (B : ℚ) ^ 5 ≠ 0 := pow_ne_zero 5 hBq
  field_simp [hBq, hB2, hB3, hB4, hB5, hB6]
```

If the post-`field_simp` goal is the same polynomial but arranged differently, keep the existing pattern:

```lean
  ring_nf at hCq ⊢
  exact hCq
```

or, if orientation is reversed:

```lean
  exact hCq.symm
```

### 4. `Int.dvd_coe_gcd`

Your existing file already uses the correct v4.31-style call:

```lean
Int.dvd_coe_gcd hA hB
```

where `hA : d ∣ A` and `hB : d ∣ B`.  Since `Int.gcd A B : ℕ`, the target should be written as

```lean
(d : ℤ) ∣ ((Int.gcd A B : ℕ) : ℤ)
```

or, as above, with `d = B`:

```lean
have hBdvdgcd : B ∣ ((Int.gcd A B : ℕ) : ℤ) := by
  exact Int.dvd_coe_gcd hBdvdA (dvd_refl B)
```

## Why this wrapper is the right cut

The theorem

```lean
N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
```

is exactly the desired formalization boundary: the hard arithmetic input is the affine rational-points statement, while the conversion from the integral square-denominator model to the curve and the contradiction with primitive denominator are elementary Lean code.

The proof deliberately avoids adding a global sign claim such as

```lean
B ^ 2 ∣ C - z ^ 3 ∨ B ^ 2 ∣ C + z ^ 3
```

which is false for composite `B` because different odd prime powers may choose different CRT signs, and because `p = 2` behaves separately.