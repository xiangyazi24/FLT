# Q2657 (dm-codex1): explicit descent for the primitive Eisenstein quartic

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
GitHub repo/branch: `xiangyazi24/FLT@scratch`

Target:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace MazurProof.RationalPointsN12

def IntQuarticEisensteinPrimitive : Prop :=
  ∀ {A N S : ℤ},
    IsCoprime A N → N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

def EisensteinQuarticBad (A N S : ℤ) : Prop :=
  IsCoprime A N ∧ A ≠ 0 ∧ N ≠ 0 ∧ A ^ 2 ≠ N ^ 2 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

end MazurProof.RationalPointsN12
```

The route below is independent of `RationalPointsN12`, E1/E24 finite-point theorems, and full-cover residuals.

## 1. Normalized bad solution

Use a positive ordered bad solution and descend on the larger side `N`.

```lean
namespace MazurProof.RationalPointsN12

/-- Positive ordered primitive bad solution. -/
def NormalizedEisensteinBad (A N S : ℤ) : Prop :=
  0 < A ∧ A < N ∧ 0 < S ∧ IsCoprime A N ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- A branch of the square-sided Eisenstein-conic parametrization. -/
def EisensteinSqBranch (A N S m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  A ^ 2 = (m - n) * (m + n) ∧
  N ^ 2 = n * (2 * m - n) ∧
  S = m ^ 2 - m * n + n ^ 2

/-- Unordered positive form, useful for the swapped conic branch. -/
def PositivePrimitiveEisensteinBadUnordered (A N S : ℤ) : Prop :=
  0 < A ∧ 0 < N ∧ 0 < S ∧ IsCoprime A N ∧ A ^ 2 ≠ N ^ 2 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

end MazurProof.RationalPointsN12
```

Reduction from `EisensteinQuarticBad`:

```lean
namespace MazurProof.RationalPointsN12

/-- The sign/order normalization statement to prove first. -/
def NormalizedOfBadStatement : Prop :=
  ∀ {A N S : ℤ}, EisensteinQuarticBad A N S →
    ∃ A0 N0 S0 : ℤ, NormalizedEisensteinBad A0 N0 S0

end MazurProof.RationalPointsN12
```

Proof: replace `(A,N,S)` by `(|A|,|N|,|S|)`, swap the first two coordinates if needed, and use `A^2 ≠ N^2` to get strict order.  The quartic is symmetric in `A,N` and invariant under signs.  `S ≠ 0` follows because `x^2 - x*y + y^2 > 0` for `(x,y)=(A^2,N^2)` not both zero.

## 2. Parametrization target

For a normalized solution, put `X=A^2`, `Y=N^2`.  Then

```text
S^2 = X^2 - X Y + Y^2.
```

The branch needed for descent is

```text
X = m^2 - n^2 = (m-n)(m+n),
Y = 2mn - n^2 = n(2m-n),
S = m^2 - mn + n^2,
0 < n < m,
gcd(m,n)=1.
```

The identity is purely algebraic:

```lean
namespace MazurProof.RationalPointsN12

lemma eisenstein_param_identity (m n : ℤ) :
    (m ^ 2 - m*n + n ^ 2) ^ 2 =
      ((m-n)*(m+n)) ^ 2
        - ((m-n)*(m+n)) * (n*(2*m-n))
        + (n*(2*m-n)) ^ 2 := by
  ring

/-- Parametrization statement.  The disjunction handles the symmetric branch. -/
def NormalizedBadParamStatement : Prop :=
  ∀ {A N S : ℤ}, NormalizedEisensteinBad A N S →
    ∃ m n : ℤ,
      EisensteinSqBranch A N S m n ∨ EisensteinSqBranch N A S m n

end MazurProof.RationalPointsN12
```

Lean-feasible proof choices:

* Elementary conic proof by rational slope, then normalize the primitive branch.
* Or Eisenstein-integer square extraction in `𝓞 ℚ(ζ₃)`, using the PID/UFD API.  The latter avoids the annoying `/3` conic parametrization case by choosing the sector of the square root.

Important 3-divisibility point: in the branch used above one must have `¬ (3 : ℤ) ∣ m+n`.  If `3 ∣ m+n`, then `m ≡ -n (mod 3)` and both raw factors `m^2-n^2` and `n(2m-n)` are divisible by `3`; in the square-sided primitive branch this would force `3 ∣ A` and `3 ∣ N`.  If a rational-slope proof returns the usual primitive formulas divided by `3`, do not feed that directly to the descent below; first reparametrize by the Eisenstein unit/sector argument, or add a separate `/3` branch lemma.  This is the main place a hidden false proof can enter.

## 3. GCD and square-splitting lemmas

Use local wrappers around `Int.sq_of_gcd_eq_one`, following the pattern in `Mathlib/NumberTheory/FLT/Four.lean`.

```lean
namespace MazurProof.RationalPointsN12

/-- Positive coprime product-square splitting. -/
def PosSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → IsCoprime x y → z ^ 2 = x*y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2

/-- Positive product-square splitting when both factors have exactly one factor 2. -/
def PosTwoSqOfGcdTwoMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → 2 ∣ x → 2 ∣ y →
    IsCoprime (x/2) (y/2) → z ^ 2 = x*y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2*a ^ 2 ∧ y = 2*b ^ 2

end MazurProof.RationalPointsN12
```

GCD facts for `0<n<m`, `gcd(m,n)=1`:

```text
gcd(n, 2m-n) = 1  if n is odd,
gcd(n, 2m-n) = 2  if n is even; then m is odd.

gcd(m-n, m+n) = 1  if m,n have opposite parity,
gcd(m-n, m+n) = 2  if m,n are both odd.
```

Also needed later:

```text
if a,b odd and gcd(a,b)=1, then gcd((b-a)/2, (b+a)/2)=1;
if c,d odd and gcd(c,d)=1, then gcd((d-c)/2, (d+c)/2)=1.
```

## 4. Exact descent formulas from one branch

Assume

```text
A^2 = (m-n)(m+n),
N^2 = n(2m-n),
S   = m^2 - mn + n^2,
0 < n < m,
gcd(m,n)=1.
```

### Case I: `n` even

Then `m` is odd.  Split the `N` side using gcd `2`:

```text
n       = 2 c^2,
2m - n = 2 d^2,
N       = ± 2 c d.
```

Split the `A` side.  Since `m±n` are positive odd coprime factors:

```text
m - n = a^2,
m + n = b^2,
A     = ± a b.
```

Now

```text
b^2 - a^2 = 2n = 4c^2,
(b-a)(b+a) = 4c^2.
```

Since `a,b` are odd and coprime, split the half-factors:

```text
(b-a)/2 = e^2,
(b+a)/2 = f^2,
c = e f,
0 < e < f,
gcd(e,f)=1.
```

Therefore

```text
a = f^2 - e^2,
b = f^2 + e^2,
c = e f.
```

The smaller solution is

```text
A' = e,
N' = f,
S' = |d|.
```

Algebra:

```text
d^2 = (2m-n)/2
    = m - n/2
    = (a^2+b^2)/2 - c^2
    = ((f^2-e^2)^2 + (f^2+e^2)^2)/2 - e^2 f^2
    = e^4 - e^2 f^2 + f^4.
```

Thus

```text
S'^2 = A'^4 - A'^2 N'^2 + N'^4.
```

Primitive/nontrivial/smaller:

```text
gcd(e,f)=1,
0 < e < f,
N = 2 e f |d|,
so f < N.
```

Lean theorem shape:

```lean
namespace MazurProof.RationalPointsN12

def DescentBranchNEvenStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n → 2 ∣ n →
    ∃ e f d : ℤ,
      0 < e ∧ e < f ∧ 0 < d ∧ IsCoprime e f ∧
      d ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

end MazurProof.RationalPointsN12
```

### Case II: `n` odd and `m` even — impossible

Split the two products into odd coprime square factors:

```text
n       = c^2,
2m - n = d^2,
m - n  = a^2,
m + n  = b^2.
```

Then

```text
b^2 - a^2 = 2n = 2c^2.
```

But `a,b,c` are odd, so modulo `4`:

```text
b^2 - a^2 ≡ 1 - 1 ≡ 0,
2c^2       ≡ 2,
```

contradiction.  Mod `8` is even cleaner: an odd-square difference is divisible by `8`, while `2c^2 ≡ 2 (mod 8)`.

```lean
namespace MazurProof.RationalPointsN12

def BranchNOddMEvenImpossibleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n → ¬ 2 ∣ n → 2 ∣ m → False

end MazurProof.RationalPointsN12
```

### Case III: `n` odd and `m` odd

Split the `N` side with gcd `1`:

```text
n       = c^2,
2m - n = d^2,
N       = ± c d.
```

Split the `A` side with gcd `2`:

```text
m - n = 2 a^2,
m + n = 2 b^2,
A     = ± 2 a b.
```

Then

```text
n = b^2 - a^2 = c^2,
d^2 - c^2 = (2m-n) - n = 2(m-n) = 4a^2.
```

Since `c,d` are odd and coprime, split the half-factors:

```text
(d-c)/2 = e^2,
(d+c)/2 = f^2,
a = e f,
0 < e < f,
gcd(e,f)=1.
```

Therefore

```text
c = f^2 - e^2,
d = f^2 + e^2.
```

The smaller solution is

```text
A' = e,
N' = f,
S' = |b|.
```

Algebra:

```text
b^2 = a^2 + c^2
    = e^2 f^2 + (f^2 - e^2)^2
    = e^4 - e^2 f^2 + f^4.
```

Thus

```text
S'^2 = A'^4 - A'^2 N'^2 + N'^4.
```

Primitive/nontrivial/smaller:

```text
gcd(e,f)=1,
0 < e < f,
N = |c d| = (f^2-e^2)(f^2+e^2) = f^4-e^4,
so f < N.
```

```lean
namespace MazurProof.RationalPointsN12

def DescentBranchNOddMOddStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n → ¬ 2 ∣ n → ¬ 2 ∣ m →
    ∃ e f b : ℤ,
      0 < e ∧ e < f ∧ 0 < b ∧ IsCoprime e f ∧
      b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

end MazurProof.RationalPointsN12
```

## 5. Combined branch descent

The branch theorem should be unordered: it descends relative to the branch-second coordinate.  This makes the swapped conic branch painless.

```lean
namespace MazurProof.RationalPointsN12

def DescentFromBranchUnorderedStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

def NormalizedDescentStatement : Prop :=
  ∀ {A N S : ℤ}, NormalizedEisensteinBad A N S →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

Proof of `DescentFromBranchUnorderedStatement`:

```text
if 2 ∣ n:
  use Case I with (A',N',S')=(e,f,|d|)
else if 2 ∣ m:
  contradiction by Case II
else:
  use Case III with (A',N',S')=(e,f,|b|)
```

Proof of `NormalizedDescentStatement`:

```text
obtain branch for (A,N) or (N,A).
if branch is (A,N), apply unordered branch descent and get N' < N.
if branch is (N,A), apply unordered branch descent and get N' < A, then use A < N.
```

## 6. Infinite descent wrapper

```lean
namespace MazurProof.RationalPointsN12

def NotNormalizedBadStatement : Prop :=
  ¬ ∃ A N S : ℤ, NormalizedEisensteinBad A N S

def IntQuarticEisensteinPrimitiveFromDescentStatement : Prop :=
  NormalizedOfBadStatement →
  NormalizedBadParamStatement →
  DescentFromBranchUnorderedStatement →
  IntQuarticEisensteinPrimitive

end MazurProof.RationalPointsN12
```

Minimal-counterexample proof: copy the structure of `Fermat42.exists_minimal` from `Mathlib.NumberTheory.FLT.Four`.  Let

```text
M = { q : ℕ | ∃ A N S, NormalizedEisensteinBad A N S ∧ q = N.natAbs }.
```

Choose `q0 = Nat.find`.  `NormalizedDescentStatement` gives a new normalized bad solution with `N' < N`, hence `N'.natAbs < N.natAbs`, contradicting minimality.

## 7. Can this be replaced by `not_fermat_42`?

No direct derivation.  The identity

```text
S^2 = (N^2-A^2)^2 + (A N)^2
```

gives a primitive Pythagorean triple, but neither leg is generally a fourth power or even a square.  Applying `not_fermat_42` would require extra splitting that is essentially the descent above.  It is safe to reuse the elementary proof patterns and lemmas from `FLT/Four.lean`; do not use `not_fermat_42` itself as the proof of this theorem.

## 8. Mathlib grep targets

Pinned mathlib in this repo: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.

```text
Mathlib/NumberTheory/FLT/Four.lean
  Fermat42.exists_minimal
  Fermat42.not_minimal
  not_fermat_42
  Int.sq_of_gcd_eq_one usage pattern
  Int.isCoprime_of_sq_sum
  Int.isCoprime_of_sq_sum'

Mathlib/NumberTheory/PythagoreanTriples.lean
  PythagoreanTriple
  PythagoreanTriple.coprime_classification
  PythagoreanTriple.coprime_classification'

Mathlib/RingTheory/Coprime/Lemmas.lean
  IsCoprime.mul_left / mul_right / pow
  IsCoprime.of_mul_left_left
  Int.isCoprime_iff_gcd_eq_one

Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean
  IsCyclotomicExtension.Rat.Three.Units.mem
  IsCyclotomicExtension.Rat.Three.eta_sq
  IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent

Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean
  IsCyclotomicExtension.Rat.three_pid
```

## 9. Gaps / false-step checklist

* The naive “Eisenstein square extraction immediately gives a smaller solution” is false: it produces the plus-sign quartic `a^4+a^2c^2+c^4` unless the second parity-dependent factorization is performed.
* The rational conic parametrization has a possible common-factor-`3` presentation.  For the descent above, prove a no-`/3` square-root branch via Eisenstein unit/sector choice, or add a separate `/3` branch lemma.  Do not silently divide by `3` and then reuse the formulas above.
* The hardest Lean pieces are the local gcd/parity square-splitting lemmas, not the final `ring` identities.
* No step should import or use `RationalPointsN12`, E1/E24 finite-point results, or full-cover residual classifications.
