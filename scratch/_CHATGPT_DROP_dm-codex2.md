# Q2389 (dm-codex2): E1 nonzero-Y squareclass extraction interface

This is the exact interface I would put between the rational-point theorem and the finite full-cover obstruction table.  It avoids quotienting by `ℚˣ/(ℚˣ)^2`; the squareclass choices are ordinary integers in the finite list `S23 = {±1, ±2, ±3, ±6}` plus explicit rational or integer square factors.

## Lean-facing interface

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- The shifted curve `E1 : Y^2 = X(X-1)(X+3)`. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 1) * (X + 3)

/-- Squareclass representatives supported only at `2` and `3`, with sign. -/
def S23 : List ℤ := [1, -1, 2, -2, 3, -3, 6, -6]

/-- Membership in the chosen finite squareclass representative list. -/
def InS23 (d : ℤ) : Prop :=
  d ∈ S23

/-- A rational number is an ordinary rational square. -/
def IsRatSquare (q : ℚ) : Prop :=
  ∃ r : ℚ, q = r ^ 2

/-- `q` has squareclass represented by the integer `d`:
`q = d * r^2` for a nonzero rational `r`. -/
def SquareclassBy (q : ℚ) (d : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2

/-- `q` is nonzero and its squareclass is supported only at `2` and `3`. -/
def SquareclassSupportedOn23 (q : ℚ) : Prop :=
  q ≠ 0 ∧ ∃ d : ℤ, InS23 d ∧ SquareclassBy q d

/-- The two rational cover equations, before choosing integer denominators. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2 ∧
    (d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2

/-- The two integer cover equations used by the local obstruction search. -/
def CoverInt (d0 d1 d3 A B C T : ℤ) : Prop :=
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
    d3 * C ^ 2 - d0 * A ^ 2 = (3 : ℤ) * T ^ 2

/-- Primitive projective condition over the integers: no prime divides all four
coordinates.  This is the global version whose reduction modulo a prime says
at least one of `A,B,C,T` is nonzero modulo that prime. -/
def PrimitiveInt4 (A B C T : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ¬ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ B ∧ (p : ℤ) ∣ C ∧ (p : ℤ) ∣ T)

/-- Rational full-cover data.  This is already enough for algebraic descent; the
integer version below is what feeds the finite local obstruction theorem. -/
def E1FullCoverQData (X Y : ℚ) : Prop :=
  ∃ d0 d1 d3 : ℤ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    IsRatSquare (((d0 * d1 * d3 : ℤ) : ℚ)) ∧
    ∃ A B C T : ℚ,
      T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      X = (d0 : ℚ) * (A / T) ^ 2 ∧
      X - 1 = (d1 : ℚ) * (B / T) ^ 2 ∧
      X + 3 = (d3 : ℚ) * (C / T) ^ 2 ∧
      CoverQ d0 d1 d3 A B C T

/-- Integer full-cover data with a common denominator and primitive coordinates.
This is the target shape for Q2384-style local obstruction certificates. -/
def E1FullCoverIntData (X Y : ℚ) : Prop :=
  ∃ d0 d1 d3 : ℤ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    IsRatSquare (((d0 * d1 * d3 : ℤ) : ℚ)) ∧
    ∃ A B C T : ℤ,
      T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      PrimitiveInt4 A B C T ∧
      X = (d0 : ℚ) * (((A : ℚ) / (T : ℚ)) ^ 2) ∧
      X - 1 = (d1 : ℚ) * (((B : ℚ) / (T : ℚ)) ^ 2) ∧
      X + 3 = (d3 : ℚ) * (((C : ℚ) / (T : ℚ)) ^ 2) ∧
      CoverInt d0 d1 d3 A B C T

/-- The valuation-heavy support theorem.  This is the clean residual boundary if
you want to postpone p-adic/factorization work. -/
def E1FactorSquareclassSupport23Statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X ∧
      SquareclassSupportedOn23 (X - 1) ∧
        SquareclassSupportedOn23 (X + 3)

/-- Strongest one-shot extraction statement for the local obstruction route. -/
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y

/-- Convenience wrapper if the extraction is carried as a named residual Prop. -/
theorem e1_full_cover_int_of_extraction_statement
    (h : E1FullCoverSquareclassExtractionIntStatement)
    {X Y : ℚ} (hE : E1 X Y) (hY : Y ≠ 0) :
    E1FullCoverIntData X Y :=
  h hE hY

end MazurProof.RationalPointsN12
```

The strongest useful theorem is therefore:

```lean
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

This says exactly: for every nonzero-`Y` rational point, there are `d0,d1,d3 ∈ S23` and primitive integers `A,B,C,T`, with `T,A,B,C` all nonzero, satisfying

```text
X     = d0 * (A/T)^2,
X - 1 = d1 * (B/T)^2,
X + 3 = d3 * (C/T)^2,
d0*A^2 - d1*B^2 = T^2,
d3*C^2 - d0*A^2 = 3*T^2,
d0*d1*d3 is a rational square.
```

The product-square condition is intentionally explicit.  It is the quotient-free replacement for saying `d0*d1*d3 = 1` in `ℚ*/(ℚ*)^2`.  With these representatives it is equivalent to the usual statement that `d3` is the representative of the squareclass of `d0*d1`, but the existential square condition is easier to use and harder to mis-index.

## Proof roadmap with exact arithmetic

Start with

```text
Y^2 = X * (X - 1) * (X + 3),     Y ≠ 0.
```

First prove the nonzero factor lemma.  If any of `X`, `X-1`, or `X+3` is zero, the right side is zero, so `Y^2 = 0`, hence `Y = 0`, contradiction.  Therefore all three factors are nonzero.  In Lean this is pure field/integral-domain algebra.

Choose a reduced integer denominator for `X`:

```text
X = N / D,     D > 0,     gcd(N,D) = 1.
```

Then

```text
X     = N / D,
X - 1 = (N - D) / D,
X + 3 = (N + 3D) / D.
```

The key gcd facts are:

```text
gcd(N, D) = 1,
gcd(N - D, D) = 1,
gcd(N + 3D, D) = 1,
gcd(N, N - D) = 1,
gcd(N, N + 3D) ∣ 3,
gcd(N - D, N + 3D) ∣ 4.
```

The last two are the only places where primes `3` and `2` enter:

```text
gcd(N, N + 3D) = gcd(N, 3D), and gcd(N,D)=1, so it divides 3.
gcd(N - D, N + 3D) divides (N + 3D) - (N - D) = 4D,
and gcd(N - D, D)=1, so it divides 4.
```

Now fix a prime `p` with `p ≠ 2` and `p ≠ 3`.

If `p ∤ D`, then the denominator contributes nothing to any of the three factors.  The gcd facts imply that at most one of

```text
N, N-D, N+3D
```

is divisible by `p`.  Since the product is the rational square `Y^2`, the total `p`-adic valuation of the product is even.  Therefore the unique nonzero numerator valuation, if present, is even.  So all three valuations

```text
v_p(X), v_p(X-1), v_p(X+3)
```

are even.

If `p ∣ D`, then none of `N`, `N-D`, `N+3D` is divisible by `p`, because all three are congruent to `N` modulo `p` and `gcd(N,D)=1`.  Hence

```text
v_p(X) = v_p(X-1) = v_p(X+3) = -v_p(D).
```

The product valuation is `-3*v_p(D)`, and it is even because the product is `Y^2`.  Since `3` is odd, `v_p(D)` is even.  Again all three factor valuations are even.

Therefore every prime outside `{2,3}` occurs with even valuation in each factor.  Hence each nonzero factor has squareclass supported only at `2` and `3`, including sign:

```text
X     = d0 * r0^2,
X - 1 = d1 * r1^2,
X + 3 = d3 * r3^2,
```

with

```text
d0,d1,d3 ∈ {±1, ±2, ±3, ±6},      r0,r1,r3 ∈ ℚ*,
```

where the sign of each `dᵢ` accounts for negative rational factors.  No positivity assumption on `X`, `X-1`, or `X+3` is allowed or needed.

The product-square condition follows from the curve equation:

```text
Y^2 = d0*d1*d3 * (r0*r1*r3)^2.
```

Because `Y ≠ 0` and all `rᵢ ≠ 0`,

```text
d0*d1*d3 = (Y / (r0*r1*r3))^2.
```

In the common-denominator form below, this same square can be written as

```text
d0*d1*d3 = (Y*T^3/(A*B*C))^2.
```

## Exact clearing-denominator formulas

From the rational squareclass representatives, choose a common nonzero integer denominator `T` and integers `A,B,C` such that

```text
r0 = A/T,
r1 = B/T,
r3 = C/T.
```

Then

```text
X     = d0 * (A/T)^2,
X - 1 = d1 * (B/T)^2,
X + 3 = d3 * (C/T)^2.
```

Subtract the second identity from the first:

```text
X - (X - 1) = 1
```

so

```text
d0*(A/T)^2 - d1*(B/T)^2 = 1.
```

Multiplying by `T^2` gives the first cover equation:

```text
d0*A^2 - d1*B^2 = T^2.
```

Subtract the first identity from the third:

```text
(X + 3) - X = 3
```

so

```text
d3*(C/T)^2 - d0*(A/T)^2 = 3.
```

Multiplying by `T^2` gives the second cover equation:

```text
d3*C^2 - d0*A^2 = 3*T^2.
```

Finally divide `(A,B,C,T)` by their common integer gcd until primitive.  Because both cover equations are homogeneous of degree two in `A,B,C,T`, dividing all four coordinates by a common divisor preserves the equations.  The final primitive condition is exactly

```text
∀ prime p, not (p ∣ A and p ∣ B and p ∣ C and p ∣ T).
```

This is the global integer condition whose reduction modulo any prime `p` gives the local projective condition used in Q2384: at least one of `A,B,C,T` is not divisible by `p`.

## What should be proved now vs kept residual

Lean-now, pure algebra/gcd lemmas:

1. `Y ≠ 0` implies `X ≠ 0`, `X - 1 ≠ 0`, and `X + 3 ≠ 0` from the curve equation.
2. Reduced-denominator identities:
   ```text
   X = N/D, X-1 = (N-D)/D, X+3 = (N+3D)/D.
   ```
3. Integer gcd facts:
   ```text
   gcd(N, N-D)=1,
   gcd(N, N+3D) ∣ 3,
   gcd(N-D, N+3D) ∣ 4,
   gcd(D,N-D)=1,
   gcd(D,N+3D)=1.
   ```
4. Product-square formula:
   ```text
   d0*d1*d3 = (Y/(r0*r1*r3))^2.
   ```
5. Clearing denominators from rational reps to `CoverQ`, then to primitive `CoverInt`.
6. Primitive normalization by dividing the common gcd of `(A,B,C,T)`.

Best named residual if the valuation layer becomes long:

```lean
def E1FactorSquareclassSupport23Statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X ∧
      SquareclassSupportedOn23 (X - 1) ∧
        SquareclassSupportedOn23 (X + 3)
```

This residual is exactly the p-adic/factorization content: outside primes `2` and `3`, all valuations of the three factors are even.  Once this is available, the rest of the extraction is denominator and algebra plumbing.

If you prefer a single residual consumed directly by the local obstruction route, use:

```lean
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

## Hidden-assumption checklist

- `Y ≠ 0` is essential.  The zero-`Y` branch contains the torsion roots `X=-3,0,1` and should be handled separately.
- `X`, `X-1`, and `X+3` are all nonzero in this branch; this is what forces `A,B,C` nonzero.
- `T ≠ 0` must be a field in the data; otherwise `(A/T)^2` is meaningless as a descent parametrization even though Lean totalizes division.
- The signs of `X`, `X-1`, and `X+3` are not fixed.  Negative rationals are handled by negative representatives in `S23`.
- Do not drop the product-square condition.  Merely having `d0,d1,d3 ∈ S23` is not enough; the finite table should only use triples for which `d0*d1*d3` is a square in `ℚ`.
- The primitive integer condition is not automatic after choosing a common denominator.  It must be enforced by dividing out the common gcd of all four coordinates.
- `T` need not be positive for the local obstruction; replacing `T` by `-T` changes nothing.  If uniqueness is desired, add `0 < T`, but the finite residue proof only needs `T ≠ 0` plus primitivity.
- Independent denominators for `r0,r1,r3` are not enough for the cover equations in the Q2384 form.  Use one common denominator `T` before clearing.
