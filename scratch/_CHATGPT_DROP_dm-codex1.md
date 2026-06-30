# Q2713 (dm-codex1): divided-by-3 square branch audit

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Lean project context: `flt-ai`  
Target local frontier: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace: `MazurProof.RationalPointsN12`

Connector note: after retrying, the GitHub connector is writable, but the local WIP Lean files named in the prompt are still not visible on the remote `scratch` branch. This audit is therefore based on the exact local definitions supplied in the prompt, as requested.

## Executive verdict

The divided branch is **not** another raw-branch/EulerSquarePair descent. Its honest structure is different:

1. The branch forces `n` odd.
2. The non-square factor `3` in
   ```text
   3 * A^2 = (m-n)*(m+n)
   3 * N^2 = n*(2*m-n)
   ```
   goes to `m+n` in the first product and to `2*m-n` in the second product.
3. If `m` is even, the branch factors as
   ```text
   m - n     = a^2
   m + n     = 3*b^2
   n         = c^2
   2*m - n   = 3*d^2
   ```
   and this gives four integer squares in arithmetic progression:
   ```text
   c^2, b^2, d^2, a^2.
   ```
   By the checked four-squares-AP theorem, this collapses to the unit case `m=2`, `n=1`, hence `A=N=S=1` under positivity.
4. If `m` is odd, the branch factors as
   ```text
   m - n     = 2*a^2
   m + n     = 6*b^2
   n         = c^2
   2*m - n   = 3*d^2
   ```
   but then
   ```text
   a^2 + c^2 = 3*b^2
   ```
   with `c` odd, which is impossible modulo `4`.

So the divided branch is not reducible to the raw branch by rescaling, and it does not construct an `EulerSquarePair` directly. The Lean-friendly target is a **unit theorem**:

```lean
def DividedSquareBranchUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    A = 1 ∧ N = 1 ∧ S = 1
```

Then the current residual is immediate by choosing the left disjunct.

## 1. GCD, 2-adic, and 3-adic classification

Write

```text
x = m - n,
y = m + n,
u = n,
v = 2*m - n.
```

From `IsCoprime m n`:

```text
gcd(x,y) divides 2,
gcd(u,v) divides 2.
```

More Lean-friendly as Bezout facts:

```text
IsCoprime m n → every common divisor of m-n and m+n divides 2,
IsCoprime m n → every common divisor of n and 2*m-n divides 2.
```

For actual factorization one should avoid explicit `Int.gcd` and prove the casewise facts:

```text
m even, n odd  ⇒ IsCoprime (m-n) (m+n)
m odd,  n odd  ⇒ IsCoprime ((m-n)/2) ((m+n)/2)
n odd           ⇒ IsCoprime n (2*m-n)
```

where the half statements should be phrased division-free in Lean.

### The 3-adic facts

The hypothesis `(3 : ℤ) ∣ m+n` plus `IsCoprime m n` gives:

```text
3 ∤ n,
3 ∤ m,
3 ∤ (m-n),
3 ∣ (2*m-n).
```

Reason: if `3 ∣ n`, then `3 ∣ m+n` implies `3 ∣ m`, contradicting `IsCoprime m n`. Hence `n` is nonzero modulo `3`, and since `m ≡ -n (mod 3)`,

```text
m - n     ≡ -2*n ≡ n      (mod 3), so 3 ∤ (m-n),
2*m - n   ≡ -2*n - n = -3*n ≡ 0 (mod 3), so 3 ∣ (2*m-n).
```

Thus the tempting statement

```text
3 ∤ (2*m-n)
```

is false. It is forced in the opposite direction. The unit example

```text
m = 2, n = 1
```

already has

```text
m+n = 3,
2*m-n = 3,
m-n = 1,
n = 1.
```

### The 2-adic facts

The divided branch forces `n` odd. If `n` were even, coprimality would force `m` odd. Then `m-n` and `m+n` are odd, so `(m-n)*(m+n)` is odd and `A` is odd. But

```text
(m-n)*(m+n) = m^2 - n^2 ≡ 1 (mod 4),
3*A^2 ≡ 3 (mod 4),
```

contradiction.

Therefore `n` is odd, so `2*m-n` is also odd. The remaining split is by parity of `m`:

* `m` even: `m-n` and `m+n` are odd and coprime.
* `m` odd: `m-n` and `m+n` are even, and their halves are coprime.

## 2. Where the factor `3` goes

Because `3 ∤ (m-n)` and `3 ∣ (m+n)`, the explicit non-square `3` in `3*A^2` must go into `m+n`. Additional powers of `3` inside `m+n` are square powers and are absorbed into the square witness.

Because `3 ∤ n` and `3 ∣ (2*m-n)`, the explicit non-square `3` in `3*N^2` must go into `2*m-n`.

Thus the honest factor packages are exactly these.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Divided branch factor package in the `m` even case. -/
def DividedSqBranchMEvenFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = a ^ 2 ∧
    m + n = 3 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = 3 * d ^ 2

/-- Divided branch factor package in the `m` odd case. -/
def DividedSqBranchMOddFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = 2 * a ^ 2 ∧
    m + n = 6 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = 3 * d ^ 2

/-- Honest divided-branch factorization target. -/
def DividedSqBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
      (Even m ∧ DividedSqBranchMEvenFactors m n) ∨
      (Odd m ∧ DividedSqBranchMOddFactors m n)

end MazurProof.RationalPointsN12
```

To prove this factorization in Lean, use one new square-factor lemma rather than trying to reuse the raw lemma verbatim:

```lean
/-- Coprime positive product equal to `3 * square`, with the `3` known to divide
only the right factor. -/
def PosThreeSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ},
    0 < x → 0 < y →
    IsCoprime x y →
    ¬ (3 : ℤ) ∣ x →
    (3 : ℤ) ∣ y →
    3 * z ^ 2 = x * y →
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = 3 * b ^ 2
```

For the `m` odd `A`-product, apply this lemma to the coprime halves of `m-n` and `m+n`: after writing

```text
m-n = 2*x,
m+n = 2*y,
```

one first proves `A` is even, writes `A = 2*A0`, and obtains

```text
3*A0^2 = x*y,
x = a^2,
y = 3*b^2,
```

hence

```text
m-n = 2*a^2,
m+n = 6*b^2.
```

For the `N`-product, since `n` and `2*m-n` are odd and coprime, the same `PosThreeSqOfCoprimeMulSqStatement` gives

```text
n = c^2,
2*m-n = 3*d^2.
```

## 3. The divided branch is not a raw-branch rescaling

It is tempting to divide the factors carrying `3` and try to recover the raw packages, but this does not preserve the branch equations. For example in the unit case

```text
m = 2, n = 1,
m-n = 1,
m+n = 3,
2*m-n = 3,
```

there is no raw package with `m+n` and `2*m-n` themselves square/twice-square factors. Dividing `m+n` or `2*m-n` by `3` creates new quantities but not a raw branch for the same `(m,n)`.

The branch instead reduces to a four-squares-in-arithmetic-progression obstruction plus a unit exception.

## 4. Algebra in the `m` even case: four squares in AP

Assume the `m` even factor package:

```text
m - n     = a^2,
m + n     = 3*b^2,
n         = c^2,
2*m - n   = 3*d^2.
```

Then

```text
m = a^2 + c^2,
3*b^2 = a^2 + 2*c^2,
3*d^2 = 2*a^2 + c^2.
```

The four squares

```text
c^2, b^2, d^2, a^2
```

are in arithmetic progression. A Lean-friendly way to state this is the pair of midpoint identities

```text
c^2 + d^2 = 2*b^2,
b^2 + a^2 = 2*d^2.
```

These are pure linear algebra consequences of the factor package.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Algebraic AP identities from the `m` even divided-factor package. -/
theorem dividedMEvenFactors_AP_identities
    {m n a b c d : ℤ}
    (hma : m - n = a ^ 2)
    (hmb : m + n = 3 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2md : 2 * m - n = 3 * d ^ 2) :
    c ^ 2 + d ^ 2 = 2 * b ^ 2 ∧
      b ^ 2 + a ^ 2 = 2 * d ^ 2 := by
  constructor <;> nlinarith

end MazurProof.RationalPointsN12
```

If the available theorem is the integer wrapper around the checked rational AP theorem, use it in this shape:

```lean
def FourIntSquaresAPConst : Prop :=
  ∀ {a d b c : ℤ},
    a ^ 2 + b ^ 2 = 2 * d ^ 2 →
    c ^ 2 + d ^ 2 = 2 * b ^ 2 →
    a ^ 2 = d ^ 2 ∧ d ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2
```

Apply it with the ordered quadruple `(a,d,b,c)`. The two hypotheses are exactly

```text
a^2 + b^2 = 2*d^2,
c^2 + d^2 = 2*b^2.
```

After the AP theorem gives

```text
a^2 = d^2 = b^2 = c^2,
```

positivity gives `a=b=c=d`. Then

```text
m = a^2 + c^2 = 2*c^2,
n = c^2.
```

Since `IsCoprime m n`, and `n ∣ m`, `n` is a unit. With `0 < n`, this gives `n=1`, hence `c=1`, and therefore

```text
m=2, n=1, a=b=c=d=1.
```

The divided branch equations then give

```text
3*A^2 = 3,
3*N^2 = 3,
3*S = 3.
```

Using `0<A`, `0<N`, and `0<S` from `PositivePrimitiveEisensteinBadUnordered`, we get

```text
A = 1, N = 1, S = 1.
```

This is the unit branch, not a descent object.

## 5. Algebra in the `m` odd case: modular impossibility

Assume the `m` odd factor package:

```text
m - n     = 2*a^2,
m + n     = 6*b^2,
n         = c^2,
2*m - n   = 3*d^2.
```

Then

```text
m = c^2 + 2*a^2,
m+n = 2*c^2 + 2*a^2 = 6*b^2,
```

so

```text
a^2 + c^2 = 3*b^2.
```

Since the divided branch forces `n` odd and `n=c^2`, `c` is odd. But the equation

```text
a^2 + c^2 = 3*b^2
```

has no integer solutions with `c` odd. Modulo `4`:

* if `a` is even, then the left side is `1 mod 4`;
* if `a` is odd, then the left side is `2 mod 4`;
* the right side is either `0 mod 4` or `3 mod 4`.

Contradiction.

The pure algebra identity is:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Algebraic identities from the `m` odd divided-factor package. -/
theorem dividedMOddFactors_core_identities
    {m n a b c d : ℤ}
    (hma : m - n = 2 * a ^ 2)
    (hmb : m + n = 6 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2md : 2 * m - n = 3 * d ^ 2) :
    a ^ 2 + c ^ 2 = 3 * b ^ 2 ∧
      4 * a ^ 2 + c ^ 2 = 3 * d ^ 2 := by
  constructor <;> nlinarith

end MazurProof.RationalPointsN12
```

The modular contradiction should be isolated as a tiny reusable lemma:

```lean
/-- No solution to `a^2 + c^2 = 3*b^2` when `c` is odd. -/
def NoOddCForThreeSquareSumStatement : Prop :=
  ∀ {a b c : ℤ},
    Odd c →
    a ^ 2 + c ^ 2 = 3 * b ^ 2 →
    False
```

This proof is usually easiest in Lean by splitting on `Even a` and `Even b`, expanding the corresponding parity witnesses, then using `ring_nf` and `omega`.

## 6. Minimal Lean-friendly theorem statements

These are the statements I would add, in this order.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Basic divided-branch congruence package. -/
def DividedSqBranchCongruenceStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
      Odd n ∧
      ¬ (3 : ℤ) ∣ n ∧
      ¬ (3 : ℤ) ∣ (m - n) ∧
      (3 : ℤ) ∣ (m + n) ∧
      (3 : ℤ) ∣ (2 * m - n)

/-- Positive coprime product equal to `3 * square`; the nonsquare `3` is on the right. -/
def PosThreeSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ},
    0 < x → 0 < y →
    IsCoprime x y →
    ¬ (3 : ℤ) ∣ x →
    (3 : ℤ) ∣ y →
    3 * z ^ 2 = x * y →
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = 3 * b ^ 2

/-- Honest factorization of the divided branch. -/
def DividedSqBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
      (Even m ∧ DividedSqBranchMEvenFactors m n) ∨
      (Odd m ∧ DividedSqBranchMOddFactors m n)

/-- The `m` even divided package collapses to the unit case by four-squares AP. -/
def DividedMEvenFactorsUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    Even m →
    DividedSqBranchMEvenFactors m n →
    A = 1 ∧ N = 1 ∧ S = 1

/-- The `m` odd divided package is impossible modulo `4`. -/
def DividedMOddFactorsImpossibleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
    Odd m →
    DividedSqBranchMOddFactors m n →
    False

/-- Final divided branch theorem: no descent is needed; the branch is unit. -/
def DividedSquareBranchUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    A = 1 ∧ N = 1 ∧ S = 1

end MazurProof.RationalPointsN12
```

Then the current residual is just a wrapper:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

theorem dividedSquareBranchUnitOrDescendsStatement_of_unit
    (hunit : DividedSquareBranchUnitStatement) :
    DividedSquareBranchUnitOrDescendsStatement := by
  intro A N S m n hbad hbranch
  exact Or.inl (hunit hbad hbranch)

end MazurProof.RationalPointsN12
```

## 7. What not to prove

Do **not** try to prove identities involving `(A+N)^2` or `(A-N)^2`; the branch still gives only `A^2` and `N^2`, not `A*N`.

Do **not** assert `3 ∤ (2*m-n)`. It is false; the branch hypotheses force `3 ∣ (2*m-n)`.

Do **not** try to construct an `EulerSquarePair` from the divided packages. The even package gives a four-squares AP and collapses to unit; the odd package is already impossible modulo `4`. There is no non-unit Euler descent object hiding in this branch.
