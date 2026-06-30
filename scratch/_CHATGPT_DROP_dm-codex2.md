# Q2408 (dm-codex2): Lean-realistic plan for E1 nonzero-Y squareclass extraction

## Executive split

For the N=12 route, do **not** try to prove the full extraction in one theorem.  The smallest honest split is:

1. **Hard arithmetic residual A:** prove that the three E1 factors have even `p`-adic valuation away from `2,3`.
2. **Hard arithmetic residual B:** convert “even valuation away from `2,3`” into an explicit representative `d ∈ {±1,±2,±3,±6}` and a rational square factor.
3. **Algebraic wrappers:** from three squareclass reps, build the rational cover equations, clear to integer `A B C T`, normalize primitive, and derive the two integer cover equations.

The one-shot theorem requested by the route should remain:

```lean
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

but internally I would implement it from the smaller residuals below.

## Mathlib APIs to use

### Rational normalization

Use `Rat.num`/`Rat.den` rather than inventing your own reduced fraction structure.

Likely local checks:

```lean
import Mathlib.Data.Rat.Lemmas

#check Rat.num
#check Rat.den
#check Rat.den_nz
#check Rat.den_pos
#check Rat.num_ne_zero
#check Rat.num_divInt_den
#check Rat.num_den_mk
#check Rat.add_num_den
#check Rat.sub_intCast_den
#check Rat.add_intCast_den
#check Rat.isSquare_iff
#check Rat.isSquare_intCast_iff
```

Important pattern:

```lean
-- q = q.num /. q.den, where `/.` is Rat.divInt notation.
conv_lhs => rw [← q.num_divInt_den]
```

For the E1 reduced denominator route, set

```lean
let N : ℤ := X.num
let D : ℤ := X.den
```

Then use the same denominator for all three factors:

```lean
X     = N /. D
X - 1 = (N - D) /. D
X + 3 = (N + 3 * D) /. D
```

Do **not** rely on the normalized numerator of `X-1` being literally `N-D`; instead, rewrite valuations using `padicValRat.defn` with the displayed `q = n /. d` equality.  This avoids fighting normalization.

### Padic valuation / multiplicity

Use the current `padicValRat` API, not a new valuation.

Likely checks:

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity

#check padicValRat
#check padicValRat.defn
#check padicValRat.mul
#check padicValRat.pow
#check padicValRat.div
#check padicValRat.add_eq_min
#check padicValRat.of_int_multiplicity
#check padicValRat.multiplicity_sub_multiplicity
#check multiplicity
#check multiplicity_mul
#check emultiplicity
#check FiniteMultiplicity
#check Nat.prime_iff_prime_int
```

The crucial already-available facts are:

```lean
padicValRat.mul  -- vp(q*r) = vp(q)+vp(r), q,r nonzero
padicValRat.pow  -- vp(q^k) = k*vp(q)
padicValRat.div  -- vp(q/r) = vp(q)-vp(r), q,r nonzero
padicValRat.defn -- vp(n /. d) = multiplicity p n - multiplicity p d
```

The parity equation from the curve should be proved as:

```lean
2 * padicValRat p Y =
  padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3)
```

by rewriting `hE : Y^2 = X*(X-1)*(X+3)`, using nonzero factors, and applying `padicValRat.pow`/`padicValRat.mul`.

### Avoiding `UniqueFactorizationMonoid` where possible

For the explicit representative `d ∈ {±1,±2,±3,±6}`, the most robust route is **not** a generic UFM theorem.  Use `Rat.num`/`Rat.den`, `Rat.isSquare_iff`, and integer multiplicity/parity.  Generic names worth searching only if needed:

```lean
#check UniqueFactorizationMonoid
#check Associated
#check associated
```

But I would keep the UFM/factorization conversion as a named residual first.  It is independent of E1 and can be proved later by integer factorization.

## Code skeleton: definitions and residual interfaces

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity

namespace MazurProof.RationalPointsN12

/-- The curve `E1 : Y^2 = X(X-1)(X+3)`. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 1) * (X + 3)

/-- Chosen representatives for rational squareclasses supported at `2` and `3`. -/
def S23 : List ℤ := [1, -1, 2, -2, 3, -3, 6, -6]

def InS23 (d : ℤ) : Prop := d ∈ S23

def IsRatSquare (q : ℚ) : Prop := ∃ r : ℚ, q = r ^ 2

/-- Quotient-free squareclass representative: `q = d*r^2`, with `r ≠ 0`. -/
def SquareclassBy (q : ℚ) (d : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2

/-- Explicit supported squareclass data. -/
def SquareclassSupportedOn23 (q : ℚ) : Prop :=
  q ≠ 0 ∧ ∃ d : ℤ, InS23 d ∧ SquareclassBy q d

/-- Valuation-only support predicate.  This is easier to prove from the E1
equation and reduced-denominator gcd facts than the explicit `S23` statement. -/
def ValEvenAway23 (q : ℚ) : Prop :=
  q ≠ 0 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      padicValRat p q % 2 = 0

/-- Rational cover equations before integer denominator clearing. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2 ∧
    (d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2

/-- Integer cover equations used by the finite local obstruction layer. -/
def CoverInt (d0 d1 d3 A B C T : ℤ) : Prop :=
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
    d3 * C ^ 2 - d0 * A ^ 2 = (3 : ℤ) * T ^ 2

/-- Global primitive projective condition. -/
def PrimitiveInt4 (A B C T : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ¬ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ B ∧ (p : ℤ) ∣ C ∧ (p : ℤ) ∣ T)

/-- Rational full cover data. -/
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

/-- Integer full cover data. -/
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

/-- Hard residual A: the E1 equation forces even valuations away from `2,3`. -/
def E1FactorValEvenAway23Statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    ValEvenAway23 X ∧ ValEvenAway23 (X - 1) ∧ ValEvenAway23 (X + 3)

/-- Hard residual B: even valuations away from `2,3` give one of the eight
explicit squareclass representatives.  This is independent of E1. -/
def RatSquareclassSupportedOn23OfValEvenAway23Statement : Prop :=
  ∀ {q : ℚ}, ValEvenAway23 q → SquareclassSupportedOn23 q

/-- Algebraic wrapper target: three explicit squareclasses on the E1 factors
produce rational cover data.  This should be proved now. -/
def E1FullCoverQDataOfFactorSquareclassesStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X →
    SquareclassSupportedOn23 (X - 1) →
    SquareclassSupportedOn23 (X + 3) →
      E1FullCoverQData X Y

/-- Algebraic wrapper target: rational cover data can be cleared to primitive
integer cover data.  This is denominator/gcd plumbing, not E1 arithmetic. -/
def E1FullCoverIntDataOfQDataStatement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverQData X Y → E1FullCoverIntData X Y

/-- Final requested interface. -/
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y

/-- No hard proof hidden here: this is just the dependency composition shape. -/
def E1FullCoverSquareclassExtractionInt_from_parts : Prop :=
  E1FactorValEvenAway23Statement →
  RatSquareclassSupportedOn23OfValEvenAway23Statement →
  E1FullCoverQDataOfFactorSquareclassesStatement →
  E1FullCoverIntDataOfQDataStatement →
  E1FullCoverSquareclassExtractionIntStatement

end MazurProof.RationalPointsN12
```

I recommend keeping `E1FullCoverSquareclassExtractionInt_from_parts` as a `def ... : Prop` until each component is implemented; do not add a theorem with a fake proof.  When the components exist as theorems, the composition proof is a short `intro`/`rcases` wrapper.

## Residual A implementation plan: E1 factors have even valuations away from 2,3

### Step A0: nonzero factors

From `E1 X Y` and `Y ≠ 0`, prove:

```lean
X ≠ 0
X - 1 ≠ 0
X + 3 ≠ 0
```

This is easy algebra: if any factor is zero, RHS is zero, so `Y^2=0`, contradiction.

Suggested theorem target:

```lean
def E1NonzeroFactorStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    X ≠ 0 ∧ X - 1 ≠ 0 ∧ X + 3 ≠ 0
```

This should be proved now with `unfold E1`, `nlinarith`, and `sq_eq_zero_iff`.

### Step A1: common reduced denominator for X

Set:

```lean
let N : ℤ := X.num
let D : ℤ := X.den
```

Use:

```lean
X = N /. D
X - 1 = (N - D) /. D
X + 3 = (N + 3 * D) /. D
```

For `X`, use `X.num_divInt_den`.  For the shifts, start from `X = N /. D` and ring-normalize rational division; or use `Rat.sub_intCast_den`/`Rat.add_intCast_den` for denominator facts, but `padicValRat.defn` works with any proof of `q = n /. d`, so normalized numerator equality is not required.

Suggested helper statement:

```lean
def RatShiftNumDenSameDenStatement : Prop :=
  ∀ X : ℚ,
    let N : ℤ := X.num
    let D : ℤ := X.den
    X = N /. D ∧
    X - 1 = (N - D) /. D ∧
    X + 3 = (N + 3 * D) /. D
```

This is algebraic and should be proved now.  Watch notation: `/.` is `Rat.divInt`; if notation is unavailable, use `Rat.divInt` explicitly.

### Step A2: gcd facts among numerator forms

For `N = X.num`, `D = X.den`, use `X.reduced` or direct `Rat` reducedness facts.  The exact object behind `q.reduced` is visible in `Rat.mul_self_num` proofs: Mathlib uses `q.reduced.mul_right ...`, so `X.reduced` should be the key coprimality witness.

Needed integer facts:

```text
gcd(N,D)=1,
gcd(N-D,D)=1,
gcd(N+3D,D)=1,
gcd(N,N-D)=1,
gcd(N,N+3D) ∣ 3,
gcd(N-D,N+3D) ∣ 4.
```

Lean-friendly targets, preferably with `IsCoprime` rather than raw gcd:

```lean
def E1ReducedNumeratorGcdFactsStatement : Prop :=
  ∀ N D : ℤ,
    D ≠ 0 → IsCoprime N D →
      IsCoprime (N - D) D ∧
      IsCoprime (N + 3 * D) D ∧
      IsCoprime N (N - D) ∧
      ((Int.gcd N (N + 3 * D) : ℤ) ∣ (3 : ℤ)) ∧
      ((Int.gcd (N - D) (N + 3 * D) : ℤ) ∣ (4 : ℤ))
```

This is not conceptually hard.  It is pure Bezout/gcd algebra.  Prove it with `IsCoprime.add_mul_left_left`, `IsCoprime.add_mul_right_right`, `Int.isCoprime_iff_gcd_eq_one`, and divisibility from linear combinations.

### Step A3: valuation parity

For a fixed prime `p ≠ 2,3`, rewrite:

```lean
padicValRat p X       = multiplicity (p:ℤ) N       - multiplicity (p:ℤ) D
padicValRat p (X - 1) = multiplicity (p:ℤ) (N-D)   - multiplicity (p:ℤ) D
padicValRat p (X + 3) = multiplicity (p:ℤ) (N+3D) - multiplicity (p:ℤ) D
```

using:

```lean
padicValRat.defn p hq hqdf
```

where `hqdf : q = n /. d` and `hq : q ≠ 0`.

Then split cases:

* If `(p:ℤ) ∤ D`, the denominator valuation is zero.  The gcd facts imply at most one numerator among `N`, `N-D`, `N+3D` has positive multiplicity.  Since the sum of the three valuations is `2*vp(Y)`, the unique possibly nonzero valuation is even.
* If `(p:ℤ) ∣ D`, then none of `N`, `N-D`, `N+3D` is divisible by `p`, so all numerator multiplicities are zero.  The three valuations are all `-multiplicity p D`; their sum is `-3*multiplicity p D`, which is even.  Since `3` is odd, `multiplicity p D` is even, so all three valuations are even.

This is the genuine p-adic proof.  It is the first named residual I would keep if time is limited:

```lean
def E1FactorValEvenAway23Statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    ValEvenAway23 X ∧ ValEvenAway23 (X - 1) ∧ ValEvenAway23 (X + 3)
```

## Residual B implementation plan: valuation support to `S23`

The target is:

```lean
def RatSquareclassSupportedOn23OfValEvenAway23Statement : Prop :=
  ∀ {q : ℚ}, ValEvenAway23 q → SquareclassSupportedOn23 q
```

Proof idea:

1. Write `q = q.num /. q.den` with `q.num ≠ 0`, `q.den > 0`.
2. Separate sign using `q.num.sign` or cases on `q < 0`.
3. For numerator and denominator, remove square factors prime-by-prime.  Since all primes except `2,3` have even valuation in the rational quotient, their parity cancels into the square factor.
4. The only possible nonsquare residue after cancellation is `± 2^a * 3^b` with `a,b ∈ {0,1}`.
5. Choose `d ∈ [1,-1,2,-2,3,-3,6,-6]`; produce `r : ℚ` with `q = d*r^2`.

Useful APIs:

```lean
#check Rat.isSquare_iff
#check Rat.isSquare_intCast_iff
#check padicValRat.multiplicity_sub_multiplicity
#check multiplicity
#check UniqueFactorizationMonoid
#check Associated
```

This is independent of E1.  If you want a smaller version than full valuation-to-squareclass, use this direct squareclass residual:

```lean
def RatSquareclassS23Residual : Prop :=
  ∀ {q : ℚ}, q ≠ 0 →
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → padicValRat p q % 2 = 0) →
      ∃ d : ℤ, InS23 d ∧ SquareclassBy q d
```

This is likely the hardest standalone arithmetic theorem after Residual A.

## Algebraic wrapper: three squareclasses imply rational cover data

Given:

```text
X     = d0*r0^2,
X - 1 = d1*r1^2,
X + 3 = d3*r3^2,
```

with all `rᵢ ≠ 0`, choose a common nonzero denominator:

```text
r0 = A/T,  r1 = B/T,  r3 = C/T.
```

Then the cover equations are just subtraction:

```text
d0*(A/T)^2 - d1*(B/T)^2 = 1,
d3*(C/T)^2 - d0*(A/T)^2 = 3.
```

Multiplying by `T^2` gives `CoverQ` in the normalization used above:

```lean
(d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2
(d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2
```

The product-square condition follows from the curve:

```text
Y^2 = d0*d1*d3*(r0*r1*r3)^2
```

so

```text
d0*d1*d3 = (Y/(r0*r1*r3))^2.
```

This wrapper is algebraic.  It should be proved now once the common-denominator helper is available.

Suggested helper residual only if denominator code gets annoying:

```lean
def RatCommonDenom3NonzeroStatement : Prop :=
  ∀ r0 r1 r3 : ℚ,
    r0 ≠ 0 → r1 ≠ 0 → r3 ≠ 0 →
      ∃ A B C T : ℤ,
        T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
        r0 = (A : ℚ) / (T : ℚ) ∧
        r1 = (B : ℚ) / (T : ℚ) ∧
        r3 = (C : ℚ) / (T : ℚ)
```

This is not mathematically hard.  Construct `T` as a product or lcm of the three denominators, for example:

```text
T = r0.den * r1.den * r3.den
A = r0.num * r1.den * r3.den
B = r1.num * r0.den * r3.den
C = r3.num * r0.den * r1.den
```

using `Rat.num_divInt_den`, `Rat.den_pos`, and `Rat.den_nz`.

## Algebraic wrapper: rational cover data to primitive integer cover data

After `RatCommonDenom3NonzeroStatement`, you already have integer `A B C T` satisfying the rational equations.  Cast equality from `ℚ` back to `ℤ` by clearing the nonzero denominator.  The equations are polynomial with integer coefficients, so this is straightforward with `norm_num`, `ring`, and `exact_mod_cast` where possible.

Primitive normalization:

1. Let `g` be a positive common divisor of `A,B,C,T`, e.g. iterated gcd of natAbs values.
2. Write `A = g*A'`, `B = g*B'`, `C = g*C'`, `T = g*T'`.
3. Divide both homogeneous quadratic equations by `g^2`.
4. Prove no prime divides all `A',B',C',T'`.
5. Nonzero is preserved because original coordinates are nonzero and `g ≠ 0`.

This is algebraic but can be tedious.  If needed, isolate it as:

```lean
def PrimitiveNormalizeCoverIntStatement : Prop :=
  ∀ {d0 d1 d3 A B C T : ℤ},
    T ≠ 0 → A ≠ 0 → B ≠ 0 → C ≠ 0 →
    CoverInt d0 d1 d3 A B C T →
      ∃ A' B' C' T' : ℤ,
        T' ≠ 0 ∧ A' ≠ 0 ∧ B' ≠ 0 ∧ C' ≠ 0 ∧
        PrimitiveInt4 A' B' C' T' ∧
        CoverInt d0 d1 d3 A' B' C' T'
```

This residual is not genuinely hard; it is just gcd normalization.

## Recommended theorem DAG

Use this DAG in the file:

```lean
-- Easy algebra, prove now.
E1NonzeroFactorStatement
RatShiftNumDenSameDenStatement
E1ReducedNumeratorGcdFactsStatement
RatCommonDenom3NonzeroStatement
E1FullCoverQDataOfFactorSquareclassesStatement
PrimitiveNormalizeCoverIntStatement
E1FullCoverIntDataOfQDataStatement

-- Genuine arithmetic residuals.
E1FactorValEvenAway23Statement
RatSquareclassSupportedOn23OfValEvenAway23Statement

-- Final composition.
E1FullCoverSquareclassExtractionIntStatement
```

If you need the smallest single residual for the current N=12 build, use only:

```lean
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

If you want the smallest honest split that still exposes progress, use the two genuine arithmetic residuals:

```lean
def E1FactorValEvenAway23Statement : Prop := ...
def RatSquareclassSupportedOn23OfValEvenAway23Statement : Prop := ...
```

Everything after those two should be treated as Lean plumbing rather than mathematics.
