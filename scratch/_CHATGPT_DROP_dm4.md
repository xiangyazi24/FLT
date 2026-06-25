# Q290 (dm4): Mathlib API for the even `ψ` / EDS recurrence

## Exact theorem for bivariate division polynomials

Mathlib already has the Weierstrass-specialized bivariate theorem.  The exact name is:

```lean
WeierstrassCurve.ψ_even
```

In namespace form, with `W : WeierstrassCurve R`, its signature is:

```lean
lemma WeierstrassCurve.ψ_even
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (m : ℤ) :
    W.ψ (2 * m) * W.ψ₂ =
      W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) -
        W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2
```

Inside `namespace WeierstrassCurve`, or with dot notation, use:

```lean
W.ψ_even m
```

This is exactly the recurrence you asked for:

```lean
ψ_{2m} · ψ₂ = ψ_{m-1}² · ψ_m · ψ_{m+2}
             - ψ_{m-2} · ψ_m · ψ_{m+1}²
```

It is proved in `DivisionPolynomial/Basic.lean` by specialization from the abstract EDS recurrence:

```lean
lemma ψ_even (m : ℤ) :
    W.ψ (2 * m) * W.ψ₂ =
      W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) -
        W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 :=
  normEDS_even ..
```

So there is no need to construct this from `normEDS_even` by hand unless you are working with an abstract normalized EDS rather than `W.ψ`.

## Underlying abstract EDS theorem

The exact abstract theorem is:

```lean
normEDS_even
```

with signature:

```lean
lemma normEDS_even
    {R : Type*} [CommRing R]
    (b c d : R) (m : ℤ) :
    normEDS b c d (2 * m) * b =
      normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
        normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2
```

This lives in:

```lean
import Mathlib.NumberTheory.EllipticDivisibilitySequence
```

The deprecated alias also exists:

```lean
normEDS_even_ofNat
```

but Mathlib marks it deprecated since `2025-05-15`; use `normEDS_even`.

## Related normalized division-polynomial theorem

There is also a theorem for the normalized bivariate `Ψ`, not raw `ψ`:

```lean
WeierstrassCurve.Ψ_even
```

Signature:

```lean
lemma WeierstrassCurve.Ψ_even
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (m : ℤ) :
    W.Ψ (2 * m) * W.ψ₂ =
      W.Ψ (m - 1) ^ 2 * W.Ψ m * W.Ψ (m + 2) -
        W.Ψ (m - 2) * W.Ψ m * W.Ψ (m + 1) ^ 2
```

For univariate `preΨ`, the corresponding theorem is:

```lean
WeierstrassCurve.preΨ_even
```

Signature:

```lean
lemma WeierstrassCurve.preΨ_even
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (2 * m) =
      W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
        W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2
```

## Usage snippets

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R) (m : ℤ)

example :
    W.ψ (2 * m) * W.ψ₂ =
      W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) -
        W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 := by
  exact W.ψ_even m

example :
    W.ψ (2 * m) * W.ψ₂ =
      W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) -
        W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 := by
  simpa using WeierstrassCurve.ψ_even (W := W) m

end WeierstrassCurve
```

If your goal has the opposite orientation, use:

```lean
  exact (W.ψ_even m).symm
```

or:

```lean
  simpa using (WeierstrassCurve.ψ_even (W := W) m).symm
```

If associativity/parentheses differ, `simpa [mul_assoc, mul_left_comm, mul_comm] using W.ψ_even m` is usually enough; for polynomial-heavy goals, `ring_nf` after rewriting is also fine.

## Answer to the concrete search question

The names are:

```lean
WeierstrassCurve.ψ_even        -- specialized raw bivariate ψ recurrence
normEDS_even                  -- abstract normalized EDS recurrence
WeierstrassCurve.Ψ_even        -- normalized bivariate Ψ recurrence
WeierstrassCurve.preΨ_even     -- univariate preΨ recurrence
```

There is no separate `ψ_two_mul` theorem needed for the displayed identity; `W.ψ_even m` is the exact theorem.
