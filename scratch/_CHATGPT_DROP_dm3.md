# Q256 (dm3): Resultant recurrence for division-polynomial separability

## Verdict

There is a clean closed form for the **power of the discriminant** in

```text
R_n = Res_X(preΨ'_n, derivative(preΨ'_n)).
```

For the reduced x-division polynomial `preΨ'_n`, let

```text
d(n) = deg(preΨ'_n)
     = (n^2 - 1) / 2   if n is odd,
     = (n^2 - 4) / 2   if n is even.
```

Then the discriminant exponent is

```text
e(n) = d(n) * (d(n) - 1) / 6.
```

Equivalently,

```text
n odd:   e(n) = (n^2 - 1)(n^2 - 3) / 24,
n even:  e(n) = (n^2 - 4)(n^2 - 6) / 24.
```

This matches the examples:

```text
n = 3:  d = 4,   e = 4*3/6 = 2
n = 4:  d = 6,   e = 6*5/6 = 5
n = 5:  d = 12,  e = 12*11/6 = 22
n = 7:  d = 24,  e = 24*23/6 = 92
```

For odd `n`, with the standard normalization where `preΨ'_n` has leading
coefficient `n`, the resultant has the familiar shape

```text
Res(preΨ'_n, (preΨ'_n)') = ± n^d(n) · Δ^e(n).
```

Indeed the polynomial discriminant satisfies

```text
Disc(preΨ'_n) = ± n^(d(n)-1) · Δ^e(n),
```

and

```text
Res(f, f') = (-1)^(d(d-1)/2) · lc(f) · Disc(f).
```

For even `n`, the exponent `e(n)` is still exactly the same formula above, but the
integer constant is normalization-dependent.  With Mathlib’s reduced even
polynomial, the constant is not simply `n^d`; your example

```text
R_4 = 2^9 · Δ^5
```

already shows this, since `4^6 = 2^12`.  The correct all-`n` statement should be
formulated as

```text
Res(preΨ'_n, (preΨ'_n)') = ± C_n · Δ^e(n),
```

where `C_n ∈ ℤ \ {0}` has only prime divisors dividing `n`.  For separability over
a field, this is enough: `(n : k) ≠ 0` implies `(C_n : k) ≠ 0`, and
`W.IsElliptic` implies `W.Δ ≠ 0`.

## Is there an EDS-style recurrence for `R_n`?

I would **not** expect a useful scalar recurrence for

```text
R_n = Res(preΨ'_n, (preΨ'_n)').
```

that mirrors the EDS recurrence for `ψ_n` in a way that gives a short Lean proof.
There are two different issues.

### 1. Resultants are multiplicative for products, not for EDS differences

The useful formal identities are things like

```text
Disc(fg) = Disc(f) Disc(g) Res(f,g)^2
Res(fg, h) = Res(f,h) Res(g,h).
```

But the Ward/EDS recurrence is not a product recurrence.  It has the shape

```text
ψ_{2m+1} = ψ_{m+2} ψ_m^3 - ψ_{m-1} ψ_{m+1}^3
ψ_{2m}   = (ψ_m / ψ_2) · (ψ_{m+2} ψ_{m-1}^2 - ψ_{m-2} ψ_{m+1}^2)
```

or the corresponding reduced/univariate version.  The discriminant of a
**difference of products** is not controlled by the discriminants of the factors.
To get a recurrence for `R_{2m+1}` from previous `R_i`, one would also need a
large package of mixed resultants such as

```text
Res(ψ_i, ψ_j),
Res(ψ_i, ψ_j'),
Res(ψ_{m+2}ψ_m^3 - ψ_{m-1}ψ_{m+1}^3,
    derivative(...)),
```

and those mixed resultants encode the same torsion-intersection information that
the projective formula or the resultant certificates were trying to avoid.

So there is an arithmetic structure behind the answer, but it is not a simple
one-dimensional EDS recurrence for `R_n`.

### 2. The known formula is geometric/divisor-theoretic, not recurrence-theoretic

The clean explanation is that `preΨ'_n` cuts out the x-coordinates of the relevant
nonzero `n`-torsion points modulo `±1`, with the nonzero 2-torsion removed in the
even case.  The discriminant of this x-polynomial measures collisions of those
x-coordinates.  Such collisions happen exactly over the discriminant divisor of
the Weierstrass model, and weighted homogeneity/intersection theory gives the
power

```text
e(n) = d(n)(d(n)-1)/6.
```

This is the standard “division-polynomial discriminant” story.  It is usually
proved from the geometry of the multiplication-by-`n` map/torsion divisor, or
from Cantor/de Jong style division-polynomial divisor calculations, rather than
from the Ward recurrence alone.

A recurrence proof may exist in a broad sense if one sets up a much larger system
of recurrences for all relevant pairwise resultants/intersections.  But that would
not be the small third route suggested in the question.  It would become another
large project, comparable in size to the projective-formula infrastructure.

## What a realistic general theorem would look like

The most robust all-`n` theorem for Lean would not mention a scalar recurrence.  I
would state it as a closed-form resultant theorem:

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

/-- Degree of the reduced x-division polynomial. -/
def preΨ'DegreeFormula (n : ℕ) : ℕ :=
  if Even n then (n ^ 2 - 4) / 2 else (n ^ 2 - 1) / 2

/-- Discriminant exponent for the reduced x-division polynomial. -/
def preΨ'DiscExponent (n : ℕ) : ℕ :=
  let d := preΨ'DegreeFormula n
  d * (d - 1) / 6

/-- Schematic all-`n` resultant theorem. -/
theorem resultant_preΨ'_derivative_shape
    (W : WeierstrassCurve k) (n : ℕ) :
    ∃ C : ℤ,
      C ≠ 0 ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ C.natAbs → p ∣ n) ∧
      Polynomial.resultant (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
        = (C : k) * W.Δ ^ preΨ'DiscExponent n := by
  -- This is the real general theorem.  It is not currently a small consequence
  -- of the Ward recurrence.
  sorry

/-- Separability follows immediately from the closed-form resultant theorem. -/
theorem isCoprime_preΨ'_derivative_of_resultant_shape
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- Use `resultant_preΨ'_derivative_shape`, `W.Δ ≠ 0`, and the prime-support
  -- condition on `C` to prove the resultant is nonzero/unit, then convert
  -- resultant nonzero to coprimality in `k[X]`.
  sorry

end WeierstrassCurve
```

This theorem is mathematically clean, but proving it in Lean is not obviously
shorter than the projective formula.  It would require one of the following:

1. a formal divisor/intersection proof for the torsion divisor under `x : E → P¹`;
2. a formal proof of the known division-polynomial discriminant formula;
3. a large generated algebraic certificate for the universal resultant identity;
4. a large recurrence system for not only `R_n`, but also mixed resultants between
   the division-polynomial factors appearing in the Ward recurrences.

Only option 3 is close to the current project’s certificate technology; but option
3 is exactly the per-`n` certificate route unless you generate a symbolic all-`n`
proof, which is much harder.

## Relation to the three routes

### Route A: per-`n` Bezout certificates

For Mazur `|T| ≤ 16`, this is still the fastest route.  It proves exactly the
needed finite range.  It does not require `ω_n`, a projective formula, generic
points, or an all-`n` discriminant theorem.

### Route B: projective formula with `ω_n`

This gives more reusable infrastructure and can prove the division-polynomial
representability theorem.  But it is a genuine 600–1200 line development and still
has hard X/Y coordinate-ring identities.

### Route C: resultant/discriminant closed formula for all `n`

Mathematically elegant, but I would not classify it as “short” unless the project
already has enough geometry of torsion divisors.  It bypasses `ω_n`, but it
replaces it with an all-`n` discriminant theorem for division polynomials.  A
simple EDS-style recurrence for the scalar resultant does not seem to be the known
or practical way to prove it.

## Recommendation

For the FLT/Mazur bound, do **not** switch to the all-`n` resultant-recurrence
route.  Use the closed-form exponent as a sanity check and as metadata for the
per-`n` certificates:

```text
e(n) = d(n)(d(n)-1)/6.
```

For each fixed `n ≤ 16`, generate

```text
A_n · preΨ'_n + B_n · (preΨ'_n)' = C_n · Δ^e(n),
```

with `C_n` factored and prime-supported on `n`.  Then Lean only needs:

```text
W.IsElliptic  ⇒  W.Δ ≠ 0
(n : k) ≠ 0   ⇒  (C_n : k) ≠ 0
```

The recurrence idea is useful conceptually, but as a formalization strategy it is
unlikely to beat finite generated certificates for `n = 1..16`.

## Reference pointers

* Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7, for the
  classical division-polynomial degree and discriminant formula background.
* Robin de Jong, “One half log discriminant and division polynomials,” especially
  the introduction and Cantor-division-polynomial discussion, for the divisor and
  discriminant/intersection viewpoint.
* The standard polynomial identity

  ```text
  Disc(f) = (-1)^(d(d-1)/2) · lc(f)^(-1) · Res(f,f')
  ```

  explains the shift from discriminant constants to resultant constants.
