# Q546 (dm3): `diagDiffQuot_formalW`

## Target identity

For

```lean
w = PowerSeries.X ^ 3 * u
```

the diagonal quotient should satisfy

```lean
diagDiffQuot (PowerSeries.X ^ 3 * u)
  = X0 ^ 3 * diagDiffQuot u
    + substX1 u * (X0 ^ 2 + X0 * X1 + X1 ^ 2)
```

up to the exact local names for `X0`, `X1`, `substX0`, and `substX1`.

The proof is exactly: use the defining equation for `diagDiffQuot` twice, prove the candidate quotient gives the same product by `(X0-X1)`, then cancel `(X0-X1)`.

## Compact Lean proof

This is the proof I would try first.  It assumes the defining lemma is oriented as

```lean
substX0 f - substX1 f = (X0 - X1) * diagDiffQuot f
```

and that the substitution maps simp-expand `substX0 (X^3*u)` and `substX1 (X^3*u)` to `X0^3*u0` and `X1^3*u1`.

```lean
theorem diagDiffQuot_formalW
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (u : PowerSeries R) :
    diagDiffQuot (PowerSeries.X ^ 3 * u)
      = X0 ^ 3 * diagDiffQuot u
        + substX1 u * (X0 ^ 2 + X0 * X1 + X1 ^ 2) := by
  let δ := X0 - X1
  let u0 := substX0 u
  let u1 := substX1 u
  let qu := diagDiffQuot u
  let qw := diagDiffQuot (PowerSeries.X ^ 3 * u)
  have hu : u0 - u1 = δ * qu := by
    simpa [δ, u0, u1, qu] using
      (subst_X_sub_subst_X_eq_mul_diagDiffQuot (f := u))
  have hw : X0 ^ 3 * u0 - X1 ^ 3 * u1 = δ * qw := by
    simpa [δ, u0, u1, qw, substX0, substX1, map_mul, map_pow] using
      (subst_X_sub_subst_X_eq_mul_diagDiffQuot
        (f := PowerSeries.X ^ 3 * u))
  have hcand :
      X0 ^ 3 * u0 - X1 ^ 3 * u1 =
        δ * (X0 ^ 3 * qu + u1 * (X0 ^ 2 + X0 * X1 + X1 ^ 2)) := by
    linear_combination (norm := ring) X0 ^ 3 * hu
  have hmul :
      δ * qw = δ * (X0 ^ 3 * qu + u1 * (X0 ^ 2 + X0 * X1 + X1 ^ 2)) := by
    rw [← hw, hcand]
  have hδ : δ ≠ 0 := by
    simpa [δ] using X0_sub_X1_ne_zero (R := R)
  have hcancel := mul_left_cancel₀ hδ hmul
  simpa [δ, qw, qu, u1]
    using hcancel
```

The only likely local edits are:

```lean
X0_sub_X1_ne_zero
substX0
substX1
```

If the file uses `subst_X0`, `subst_X1`, `X₀`, `X₁`, or `diagSub_ne_zero`, replace those names accordingly.

## If `rw [← hw, hcand]` has orientation trouble

Use `linear_combination` for the product equality too:

```lean
  have hmul :
      δ * qw = δ * (X0 ^ 3 * qu + u1 * (X0 ^ 2 + X0 * X1 + X1 ^ 2)) := by
    linear_combination (norm := ring) hw - hcand
```

Depending on `linear_combination`'s normalization, the sign may need to be reversed:

```lean
    linear_combination (norm := ring) hcand - hw
```

But the `rw` version should be more stable.

## If the defining lemma is oriented oppositely

If the local theorem is instead

```lean
(X0 - X1) * diagDiffQuot f = substX0 f - substX1 f
```

then just flip the two `simpa` proofs:

```lean
  have hu : u0 - u1 = δ * qu := by
    simpa [δ, u0, u1, qu] using
      (subst_X_sub_subst_X_eq_mul_diagDiffQuot (f := u)).symm

  have hw : X0 ^ 3 * u0 - X1 ^ 3 * u1 = δ * qw := by
    simpa [δ, u0, u1, qw, substX0, substX1, map_mul, map_pow] using
      (subst_X_sub_subst_X_eq_mul_diagDiffQuot
        (f := PowerSeries.X ^ 3 * u)).symm
```

Everything else is unchanged.

## If cancellation needs a domain instance on `MvPowerSeries`

`mul_left_cancel₀` needs the ambient target ring to have no zero divisors.  If Lean does not synthesize this automatically for `MvPowerSeries (Fin 2) R`, add the local instance/import that the surrounding file already uses for quotient uniqueness.  The proof only needs:

```lean
[NoZeroDivisors (MvPowerSeries (Fin 2) R)]
```

or an equivalent lemma:

```lean
theorem mul_left_cancel_delta
    {a b : MvPowerSeries (Fin 2) R}
    (h : (X0 - X1) * a = (X0 - X1) * b) : a = b := ...
```

Then replace the last three lines by:

```lean
  have hcancel := mul_left_cancel_delta (R := R) hmul
  simpa [δ, qw, qu, u1] using hcancel
```

## Why the proof works

The only nontrivial algebraic line is:

```lean
linear_combination (norm := ring) X0 ^ 3 * hu
```

It uses

```text
u0 - u1 = (X0-X1)*diagDiffQuot(u)
```

and the polynomial identity

```text
X0^3*u0 - X1^3*u1
= X0^3*(u0-u1) + u1*(X0^3-X1^3)
= (X0-X1)*(X0^3*diagDiffQuot(u)
    + u1*(X0^2 + X0*X1 + X1^2)).
```

Then `hw` says the same left-hand side is `(X0-X1)*diagDiffQuot(X^3*u)`, and cancellation gives the desired quotient identity.
