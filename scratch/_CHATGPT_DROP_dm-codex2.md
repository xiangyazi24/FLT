# Q2729 dm-codex2: primitive Eisenstein triple parametrization audit

Repo target: `xiangyazi24/FLT`, namespace `MazurProof.RationalPointsN12`.

This answers the residual around

```lean
def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2
```

and the proposed full/raw/divided parametrization.

## 1. Verdict: the statement is true, but the unit alternative is unnecessary

The stated theorem

```lean
def EisensteinTriplePrimitiveParamOrUnit : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    EisensteinTripleParamOrUnit X Y Z
```

is mathematically true. I do **not** see a missing `X < Y`, `X ≠ Y`, parity, or sign hypothesis.

Important details:

* `X < Y` is not needed. The conic slope `Y/(Z+X)` always produces a parameter with `0 < n < m`. The first, non-swapped orientation already covers both relative orders of `X` and `Y`; the swapped alternative in `EisensteinParam` is redundant but harmless.
* `X ≠ Y` is not needed. If `X = Y`, the equation gives `Z^2 = X^2`; with `0 < Z` and `IsCoprime X Y`, this forces `X = Y = Z = 1`.
* No parity hypothesis is needed. This is not the classical Pythagorean parametrization; the only exceptional common factor is `3`, not `2`.
* The positivity assumption `0 < Z` is necessary. Without it, the parametrization with positive `m,n` gives the positive representative for `Z`, while the equation itself is invariant under `Z ↦ -Z`.

A stronger and cleaner residual is actually true:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Stronger than the current `...OrUnit`: the unit `(1,1,1)` is itself in
the divided-by-3 sector, with `(m,n) = (2,1)`. -/
def EisensteinTriplePrimitiveFullParamStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ, EisensteinFullParam X Y Z m n

end MazurProof.RationalPointsN12
```

If keeping the current `EisensteinTripleParamOrUnit` interface, the unit branch needs one tiny downstream bridge: `(1,1,1)` gives `EisensteinFullParam 1 1 1 2 1`, and in the quartic bridge it gives `DividedSquareBranch 1 1 1 2 1`.

## 2. Elementary proof route; no Eisenstein UFD needed

The full theorem is an elementary rational-conic parametrization. No unique factorization in `ℤ[ω]` is needed.

Use the rational slope through the rational point `(1,0,1)` on the conic:

```text
Z^2 = X^2 - X*Y + Y^2.
```

For a positive primitive solution, define the reduced slope by

```text
n / m = Y / (Z + X),       with gcd(m,n)=1 and 0<n<m.
```

The inequality `Y < Z+X` follows from

```text
Z^2 - (Y-X)^2 = X*Y > 0.
```

Then

```text
m*Y = n*(Z+X).
```

Since `IsCoprime m n`, Euclid divisibility gives an integer `C` such that

```text
Y = n*C,
Z + X = m*C.
```

Substitute `Z = m*C - X` and `Y = n*C` into the conic:

```text
(m*C - X)^2 = X^2 - X*(n*C) + (n*C)^2.
```

After cancellation,

```text
(m^2 - n^2) * C = (2*m - n) * X.        (★)
```

The only possible common divisor of

```text
m^2 - n^2        and        2*m - n
```

is `1` or `3`. More precisely, under `IsCoprime m n` and `0<n<m`:

```text
gcd(m^2-n^2, 2*m-n) = 1      if ¬ 3 ∣ m+n,
gcd(m^2-n^2, 2*m-n) = 3      if   3 ∣ m+n.
```

So equation `(★)` gives two cases.

### Raw case: `¬ 3 ∣ m+n`

The two factors in `(★)` are coprime, hence

```text
C = k*(2*m - n),
X = k*(m^2 - n^2).
```

Then

```text
Y = n*C = k*(2*m*n - n^2),
Z = m*C - X = k*(m^2 - m*n + n^2).
```

Because `k` divides both `X` and `Y`, and `IsCoprime X Y`, positivity forces `k=1`. Thus

```text
X = m^2 - n^2,
Y = 2*m*n - n^2,
Z = m^2 - m*n + n^2,
¬ 3 ∣ m+n.
```

This is exactly the raw branch of `EisensteinFullParam`.

### Divided case: `3 ∣ m+n`

Now the common divisor of `m^2-n^2` and `2*m-n` is exactly `3`. The same slope equation becomes coprime after dividing both factors by `3`:

```text
((m^2 - n^2)/3) * C = ((2*m - n)/3) * X.
```

Hence

```text
C = k*((2*m - n)/3),
X = k*((m^2 - n^2)/3).
```

Then

```text
Y = k*((2*m*n - n^2)/3),
Z = k*((m^2 - m*n + n^2)/3).
```

Again `k` divides both `X` and `Y`, so primitivity and positivity force `k=1`. Multiplying by `3` gives exactly the divided sector:

```text
3*X = m^2 - n^2,
3*Y = 2*m*n - n^2,
3*Z = m^2 - m*n + n^2,
3 ∣ m+n.
```

The swapped orientation in the current definition is not needed for this derivation, but it is safe to keep.

## 3. Lean decomposition: exact interfaces

Here is a Lean-friendly decomposition into small targets. These are designed as local theorem interfaces, not axioms. The proof scripts are intended to use `ring`, `nlinarith`, Euclid divisibility for `IsCoprime`, and positivity/unit handling in `ℤ`.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Raw algebra identity for the Eisenstein conic parametrization. -/
theorem eisenstein_param_identity_raw (m n : ℤ) :
    (m ^ 2 - m * n + n ^ 2) ^ 2 =
      (m ^ 2 - n ^ 2) ^ 2 -
        (m ^ 2 - n ^ 2) * (2 * m * n - n ^ 2) +
          (2 * m * n - n ^ 2) ^ 2 := by
  ring

/-- Divisibility of all three raw parametrizing polynomials in the `3 ∣ m+n`
sector. This is the algebraic source of the divided branch. -/
def EisensteinDividedSectorDivisibilityStatement : Prop :=
  ∀ {m n : ℤ},
    (3 : ℤ) ∣ m + n →
      (3 : ℤ) ∣ m ^ 2 - n ^ 2 ∧
      (3 : ℤ) ∣ 2 * m * n - n ^ 2 ∧
      (3 : ℤ) ∣ m ^ 2 - m * n + n ^ 2

/-- The reduced conic slope.  Here `n/m = Y/(Z+X)`. -/
def EisensteinReducedSlopeStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ,
      0 < n ∧ n < m ∧ IsCoprime m n ∧
      m * Y = n * (Z + X)

/-- The only possible common factor in the raw slope denominator is excluded
by `¬ 3 ∣ m+n`. -/
def EisensteinDenominatorGcdRawStatement : Prop :=
  ∀ {m n : ℤ},
    0 < n → n < m → IsCoprime m n →
    ¬ (3 : ℤ) ∣ m + n →
    IsCoprime (m ^ 2 - n ^ 2) (2 * m - n)

/-- In the `3 ∣ m+n` sector, the common factor is exactly the factor `3` that
is divided out. -/
def EisensteinDenominatorGcdDividedStatement : Prop :=
  ∀ {m n : ℤ},
    0 < n → n < m → IsCoprime m n →
    (3 : ℤ) ∣ m + n →
    IsCoprime ((m ^ 2 - n ^ 2) / 3) ((2 * m - n) / 3)

/-- Solving the slope equation in the raw sector, before primitivity kills the
scale factor. -/
def EisensteinSlopeScaleRawStatement : Prop :=
  ∀ {X Y Z m n : ℤ},
    0 < X → 0 < Y → 0 < Z →
    EisensteinTriple X Y Z →
    0 < n → n < m → IsCoprime m n →
    m * Y = n * (Z + X) →
    ¬ (3 : ℤ) ∣ m + n →
    ∃ k : ℤ,
      0 < k ∧
      X = k * (m ^ 2 - n ^ 2) ∧
      Y = k * (2 * m * n - n ^ 2) ∧
      Z = k * (m ^ 2 - m * n + n ^ 2)

/-- Solving the slope equation in the divided sector, before primitivity kills
the scale factor. -/
def EisensteinSlopeScaleDividedStatement : Prop :=
  ∀ {X Y Z m n : ℤ},
    0 < X → 0 < Y → 0 < Z →
    EisensteinTriple X Y Z →
    0 < n → n < m → IsCoprime m n →
    m * Y = n * (Z + X) →
    (3 : ℤ) ∣ m + n →
    ∃ k : ℤ,
      0 < k ∧
      X = k * ((m ^ 2 - n ^ 2) / 3) ∧
      Y = k * ((2 * m * n - n ^ 2) / 3) ∧
      Z = k * ((m ^ 2 - m * n + n ^ 2) / 3)

/-- The generic primitivity step: a positive common scale in a coprime pair is
`1`. -/
def PositivePrimitiveScaleOneStatement : Prop :=
  ∀ {X Y U V k : ℤ},
    0 < k → IsCoprime X Y →
    X = k * U → Y = k * V →
    k = 1

/-- Cleaner final theorem: no unit alternative is needed because the unit is in
the divided sector with `(m,n)=(2,1)`. -/
def EisensteinTriplePrimitiveFullParamStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ, EisensteinFullParam X Y Z m n

end MazurProof.RationalPointsN12
```

### Constructor lemmas for `EisensteinFullParam`

These are small enough to prove by constructor/`simp` once the scaled formulas are available.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Raw constructor, choosing the first orientation of `EisensteinParam`. -/
def EisensteinFullParamOfRawStatement : Prop :=
  ∀ {X Y Z m n : ℤ},
    0 < n → n < m → IsCoprime m n →
    ¬ (3 : ℤ) ∣ m + n →
    Z = m ^ 2 - m * n + n ^ 2 →
    X = m ^ 2 - n ^ 2 →
    Y = 2 * m * n - n ^ 2 →
    EisensteinFullParam X Y Z m n

/-- Divided constructor, choosing the first orientation. -/
def EisensteinFullParamOfDividedStatement : Prop :=
  ∀ {X Y Z m n : ℤ},
    0 < n → n < m → IsCoprime m n →
    (3 : ℤ) ∣ m + n →
    3 * Z = m ^ 2 - m * n + n ^ 2 →
    3 * X = m ^ 2 - n ^ 2 →
    3 * Y = 2 * m * n - n ^ 2 →
    EisensteinFullParam X Y Z m n

/-- Unit is not an exceptional mathematical case; it is parametrized by the
`3 ∣ m+n` branch with `(m,n)=(2,1)`. -/
def EisensteinFullParamUnitStatement : Prop :=
  EisensteinFullParam 1 1 1 2 1

end MazurProof.RationalPointsN12
```

Expected proof of the unit statement is just normalization of the definition:

```lean
-- theorem eisensteinFullParam_unit : EisensteinFullParam 1 1 1 2 1 := by
--   norm_num [EisensteinFullParam, EisensteinParam]
```

I leave this as a `Statement` interface above because local simplification of `IsCoprime (2:ℤ) 1` can vary slightly depending on imported simp lemmas, but mathematically the proof is immediate.

## 4. How `m,n` are recovered and normalized

The intended Lean recovery lemma is exactly `EisensteinReducedSlopeStatement`. Internally it should be proved by applying a reduced-ratio lemma to the positive integers

```text
u = Y,
v = Z + X.
```

The separate reduced-ratio lemma can be stated without any Eisenstein content:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Reduced positive integer ratio: if `0<u<v`, write `u/v = n/m` with
`0<n<m` and `IsCoprime m n`. -/
def ExistsReducedPositiveRatioStatement : Prop :=
  ∀ {u v : ℤ},
    0 < u → u < v →
    ∃ m n : ℤ,
      0 < n ∧ n < m ∧ IsCoprime m n ∧
      m * u = n * v

end MazurProof.RationalPointsN12
```

The proof should choose the gcd-normalized pair

```text
n = u / gcd(u,v),
m = v / gcd(u,v),
```

with positive integer gcd interpreted through `natAbs`/`Int.gcd` APIs.

For the Eisenstein-specific bound `Y < Z+X`, prove the identity

```text
Z^2 - (Y-X)^2 = X*Y
```

from `EisensteinTriple X Y Z`. Since `X*Y>0`, if `Y ≥ X`, then `Z > Y-X`; if `Y < X`, the inequality `Y < Z+X` is immediate from `0<Z` and `0<X`.

## 5. Origin and correctness of the `3 ∣ m+n` divided sector

The divided sector comes from the only possible common divisor in the two factors of `(★)`:

```text
(m^2 - n^2) * C = (2*m - n) * X.
```

For coprime `m,n`, any common divisor of `m^2-n^2` and `2*m-n` divides `3`. Moreover,

```text
3 ∣ (2*m - n)    ↔    3 ∣ (m+n)
```

because modulo `3`, `2 ≡ -1`. Also

```text
m^2 - n^2 = (m-n)*(m+n),
2*m*n - n^2 = n*(2*m-n),
m^2 - m*n + n^2 = (m+n)^2 - 3*m*n.
```

Thus `3 ∣ m+n` implies all three raw expressions are divisible by `3`:

```text
3 ∣ m^2-n^2,
3 ∣ 2*m*n-n^2,
3 ∣ m^2-m*n+n^2.
```

After dividing the raw formulas by this forced common factor, the primitive formulas are exactly:

```text
3*X = m^2 - n^2,
3*Y = 2*m*n - n^2,
3*Z = m^2 - m*n + n^2.
```

So the formulas in `EisensteinFullParam` are correct.

The unit example verifies the sector:

```text
m=2, n=1,
m+n=3,
m^2-n^2=3,
2*m*n-n^2=3,
m^2-m*n+n^2=3,
```

hence `X=Y=Z=1`.

## 6. Suspicious or suboptimal current statements

### `EisensteinTripleParamOrUnit` is true but too weak as a downstream interface

It is true, but it is not the best assembly interface. Since `(1,1,1)` is itself covered by `EisensteinFullParam 1 1 1 2 1`, the downstream code is cleaner with

```lean
def EisensteinTriplePrimitiveFullParamStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ, EisensteinFullParam X Y Z m n
```

If you keep `EisensteinTriplePrimitiveParamOrUnit`, add a local bridge from the unit case to the divided branch.

### Swapped orientation is redundant but harmless

The slope `n/m = Y/(Z+X)` always yields the first orientation

```text
X = m^2 - n^2,
Y = 2*m*n - n^2
```

or its divided-by-3 version. If a human initially writes the swapped orientation with parameters `(m,n)`, the slope recovery simply returns `(m, m-n)`, which converts it back to the first orientation.

Keeping the swapped alternatives is fine because they match existing branch APIs, but no proof should depend on them.

### Do not introduce parity cases

Any parity split here is stale/misleading. The exceptional denominator is `3`, arising from the Eisenstein norm/conic denominator, not `2`.

## 7. Minimum honest residual and downstream bridge

The minimum honest residual for the parametrization frontier should be one of these:

```lean
-- Preferred stronger residual.
def EisensteinTriplePrimitiveFullParamStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ, EisensteinFullParam X Y Z m n
```

or, if you keep the current theorem:

```lean
-- Current residual, plus one unit bridge.
def EisensteinTriplePrimitiveParamOrUnit : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    EisensteinTripleParamOrUnit X Y Z
```

The downstream `NormalizedBadParamStatement` bridge can be proved assuming only the current `EisensteinTriplePrimitiveParamOrUnit`, provided the unit case is converted to `m=2,n=1` in the divided branch.

Suggested bridge interface:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Unit branch for the quartic square variables. -/
def UnitGivesDividedSquareBranchStatement : Prop :=
  DividedSquareBranch 1 1 1 2 1

/-- The theorem actually needed by the N=12 assembly layer. -/
def NormalizedBadParamBridgeFromTripleParamOrUnitStatement : Prop :=
  EisensteinTriplePrimitiveParamOrUnit →
  NormalizedBadParamStatement

end MazurProof.RationalPointsN12
```

Proof obligations for this bridge:

1. From `NormalizedEisensteinBad A N S`, extract positivity and primitivity of `A,N,S`.
2. Apply the triple parametrization theorem to

   ```text
   X = A^2,
   Y = N^2,
   Z = S.
   ```

3. Prove `IsCoprime (A^2) (N^2)` from `IsCoprime A N` using the standard pow/square coprimality API.
4. Rewrite `EisensteinTriple (A^2) (N^2) S` from the quartic identity

   ```text
   S^2 = A^4 - A^2*N^2 + N^4.
   ```

5. Raw first orientation gives `EisensteinSqBranch A N S m n`.
6. Raw swapped orientation gives `EisensteinSqBranch N A S m n`.
7. Divided first orientation gives `DividedSquareBranch A N S m n`.
8. Divided swapped orientation gives `DividedSquareBranch N A S m n`.
9. Unit case gives `A=N=S=1` by positivity and square equality, then use `DividedSquareBranch 1 1 1 2 1`.

Thus the assembly bridge does **not** need the full internal conic proof. It only needs the external residual plus the unit-to-divided branch bridge.
