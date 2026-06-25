# Q341 (dm3): Can the division-polynomial discriminant be proved by an EDS/resultant induction?

## Short answer

The closed form is yes:

```text
Disc(preΨ'_n) = unit_n · Δ^e(n)
```

with

```text
d(n) = deg(preΨ'_n)
     = (n^2 - 1) / 2   for n odd,
     = (n^2 - 4) / 2   for n even,

e(n) = d(n)(d(n)-1)/6.
```

For odd `n`, in the usual normalization with leading coefficient `n`, this gives

```text
Disc(preΨ'_n) = ± n^(d(n)-1) · Δ^e(n),
Res(preΨ'_n, (preΨ'_n)') = ± n^d(n) · Δ^e(n).
```

For even `n`, the exponent is the same, while the integer unit factor depends on
the exact reduced normalization of `preΨ'_n`.  Its prime support is still contained
in the primes dividing `n`, which is all separability needs.

But the important strategic answer is: **there is no simple one-dimensional EDS
recurrence for the discriminants/resultants that makes this an easy Lean route.**
The EDS recurrence is a difference of products, and discriminants/resultants are
well behaved under products and composition, not under subtraction.  To turn the
EDS recurrence into a discriminant induction one would need a large auxiliary
system of mixed resultants or a divisor/differential theorem.  That is comparable
to, or harder than, the projective/tangent infrastructure.

For the Mazur `n ≤ 16` target, per-`n` Bezout/resultant certificates remain the
pragmatic route.

---

## Why the product discriminant formula does not apply

For a product one has the classical identity

```text
Disc(fg) = Disc(f) Disc(g) Res(f,g)^2,
```

and similarly

```text
Res(fg,h) = Res(f,h) Res(g,h).
```

So if `preΨ'_{2m+1}` were a product of earlier division polynomials, an induction
would be plausible.

But the Ward/EDS recurrence is of the shape

```text
preΨ'_{2m+1}
  = preΨ'_{m+2} · preΨ'_m^3
      - preΨ'_{m-1} · preΨ'_{m+1}^3
```

up to the expected even/`Ψ₂Sq` factors in the full Weierstrass normalization.  A
resultant/discriminant of

```text
A - B
```

is not determined by the resultants/discriminants of `A` and `B`.  Differentiating
also does not solve this:

```text
(A - B)' = A' - B'.
```

To compute

```text
Res(A - B, A' - B')
```

one needs information about values of the factors in `A` and `B` at the roots of
`A - B`.  Those roots are not roots of the smaller `preΨ'_i` in general.  Thus a
simple induction on

```text
D_n := Disc(preΨ'_n)
```

cannot close from only the previous `D_i`.

---

## What consecutive/resultant formulas do give

There are clean formulas for resultants of nearby division polynomials.  The
standard example you cited is of the form

```text
Res(ψ_n, ψ_{n-1} ψ_{n+1}) = unit · Δ^power
```

with normalization-dependent integer constants.  Such identities are extremely
useful for proving coprimality of adjacent division polynomials, and they are
morally the algebraic shadow of the fact that a nonzero `n`-torsion point is not
simultaneously `(n-1)`- or `(n+1)`-torsion except in the exceptional singular
fibers.

However, this is not the discriminant.  The discriminant is controlled by

```text
Res(ψ_n, ψ_n'),
```

whereas the adjacent resultant is controlled by

```text
Res(ψ_n, ψ_{n-1}ψ_{n+1}).
```

At a root `α` of `ψ_n`, the adjacent resultant multiplies the values

```text
ψ_{n-1}(α) ψ_{n+1}(α),
```

while the discriminant multiplies the values

```text
ψ_n'(α).
```

There is no purely formal identity in the EDS recurrence saying

```text
ψ_n'(α) = unit · ψ_{n-1}(α) ψ_{n+1}(α)
```

for every root `α`.  A statement of this flavor becomes true only after adding
geometric/differential input: namely the local behavior of the multiplication map
`[n]` at an `n`-torsion point.  In the project’s language, this is exactly the
local-parameter / `TangentO.nsmul₁` bridge.

---

## Can the discriminant follow from `Res(ψ_n, ψ_{n±1})` by chain rule?

Not directly.

There is a tempting chain:

```text
φ_n = X ψ_n^2 - ψ_{n-1}ψ_{n+1}
```

so modulo `ψ_n`,

```text
φ_n ≡ -ψ_{n-1}ψ_{n+1}.
```

Thus

```text
Res(ψ_n, φ_n) = ± Res(ψ_n, ψ_{n-1}ψ_{n+1}).
```

This explains why adjacent resultants naturally appear in the projective formula.
But differentiating this identity does not isolate `ψ_n'`.  Modulo `ψ_n`, the
term `X ψ_n^2` and its derivative both vanish:

```text
(X ψ_n^2)' = ψ_n^2 + 2X ψ_n ψ_n' ≡ 0  mod ψ_n.
```

Therefore differentiating `φ_n = Xψ_n² - ψ_{n-1}ψ_{n+1}` gives only

```text
φ_n' ≡ -(ψ_{n-1}ψ_{n+1})'  mod ψ_n,
```

not an expression for `ψ_n'`.

To see `ψ_n'`, one must look at the **local parameter** near the pole of
`x([n]P)` or, equivalently, at the differential of `[n]`.  That uses the fact that

```text
[n]^* t_O = n · t_P + higher terms
```

when `(n : K) ≠ 0`.  This is not contained in the adjacent-resultant formula.

So the adjacent resultant and the discriminant are related geometrically, but the
missing relation is precisely the ramification/differential statement.  It is not
a cheap algebraic consequence of the EDS recurrence alone.

---

## What an EDS-resultant induction would actually require

A realistic induction would need to maintain far more than

```text
D_n = Disc(preΨ'_n).
```

It would need a large family of mixed resultants, for example:

```text
R(i,j)      = Res(preΨ'_i, preΨ'_j),
R'(i,j)     = Res(preΨ'_i, (preΨ'_j)'),
R(i, A_m-B_m) for the product-difference pieces,
```

plus formulas for resultants of the symmetric companion expressions that occur
when differentiating the Ward recurrence.

For the odd recurrence, set

```text
F = A - B
A = ψ_{m+2} ψ_m^3,
B = ψ_{m-1} ψ_{m+1}^3.
```

Then

```text
Disc(F) = Res(F,F') / lc(F)
```

requires controlling

```text
Res(A-B, A'-B').
```

There is no multiplicativity principle for this expression.  To reduce it to
previous data, one would need identities describing `A' - B'` modulo `A - B`, and
those identities are essentially the derivative/local-parameter structure of the
multiplication map.

In other words, an “EDS discriminant induction” is possible only after expanding
the state space until it contains enough mixed resultants/differential identities
to encode the geometry.  At that point it is no longer a small third route.

---

## Known proof style in the literature

The known discriminant formula for division polynomials is usually proved using
one of these viewpoints:

1. **Divisor/intersection theory:** `preΨ'_n` cuts out the x-coordinates of the
   nonzero `n`-torsion divisor modulo `±1`; collisions occur only over the
   discriminant divisor; intersection multiplicity gives
   `e(n)=d(n)(d(n)-1)/6`.
2. **Formal/differential argument:** multiplication by `n` has differential `n`,
   so when `(n : K) ≠ 0` the torsion divisor is reduced; the discriminant support
   is then forced to lie on `Δ=0`, and weighted homogeneity gives the exponent.
3. **Explicit universal resultants:** compute/prove
   `Res(preΨ'_n,(preΨ'_n)') = unit · Δ^e` directly.

These are not plain scalar recurrences for `Disc(ψ_n)`.  They are either
geometric proofs or explicit resultant proofs.

---

## Lean impact

For Lean, the possible routes are:

### Route A: per-`n` Bezout certificates

For `n ≤ 16`, this is still the fastest.

```lean
A_n * W.preΨ' n + B_n * derivative (W.preΨ' n)
  = C_n * W.Δ ^ e(n)
```

Then `[W.IsElliptic]` gives `W.Δ ≠ 0`, and `(n : K) ≠ 0` gives `(C_n : K) ≠ 0`.
This closes `IsCoprime` directly.

### Route B: projective formula plus tangent bridge

This can prove separability for all `n`, but the key missing step is the tangent
identification:

```text
coeff([n]^*t_O) = (n : K) · coeff(t_P).
```

The adjacent-resultant formulas help with `φ_n ≠ 0` and the projective-coordinate
side, but the derivative nonvanishing comes from the tangent bridge.

### Route C: discriminant formula by general theorem

A general theorem

```lean
Disc(W.preΨ' n) = unit_n * W.Δ ^ (d(n)*(d(n)-1)/6)
```

would be excellent, but proving it by EDS recurrence alone is not a short path.
It would require a large mixed-resultant/differential system or a geometric
function-field/divisor development.

---

## Recommendation

Do not plan on a simple discriminant induction from the Ward/EDS recurrence.

Use the formula

```text
e(n) = d(n)(d(n)-1)/6
```

as metadata and a consistency check for generated certificates.  If the goal is
Mazur `|T| ≤ 16`, finish the per-`n` Bezout/resultant certificates.  If the goal
is an all-`n` theorem, the clean route is the projective formula plus the tangent
or divisor-theoretic bridge, not a scalar EDS recurrence for discriminants.

The adjacent resultant

```text
Res(ψ_n, ψ_{n-1}ψ_{n+1})
```

is useful but insufficient: it measures values of neighboring division polynomials
at `n`-torsion x-coordinates, while the discriminant measures the derivative of
`ψ_n` at those same x-coordinates.  Connecting those two measurements is exactly
the ramification/differential theorem for `[n]`.
