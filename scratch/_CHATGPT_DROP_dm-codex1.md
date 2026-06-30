# Q2699 (dm-codex1): next theorem after raw square branch factor extraction

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace: `MazurProof.RationalPointsN12`

Connector status: the GitHub connector returned `404` for the target file and also for the named files `N12FourSquaresAP.lean`, `N12EulerAux.lean`, and `N12CheckedDescentBridge.lean` on `scratch`; repository code search also returned no hits for `FourSquaresAP`, `EulerAux`, or `CheckedDescentBridge`. So I cannot certify existing theorem names from the connector. The audit below is based on the exact checked interfaces in the prompt.

## Executive verdict

`RawSqBranchEvenFactors m n` or `RawSqBranchOddFactors m n` alone is **not** enough to prove the current residual conclusions as stated, because those conclusions mention `N` via `f < N`, while the raw factor packages mention only `m n`. Also, the raw packages do not store the secondary coprimality needed to split `r-c` and `r+c` into squares.

With the original `EisensteinSqBranch A N S m n`, positivity of the normalized bad object, and the factor package, the current residuals are mathematically plausible. The Lean-friendly next theorem should be a **secondary Euler split** from the raw factor package, not a direct use of `e = c, f = r`.

The tempting assignments are false:

* even case, taking `e = c`, `f = r` would require
  ```text
  b^2 = c^4 - c^2*r^2 + r^4,
  ```
  but the factor package gives only
  ```text
  b^2 = r^2 + 3*c^2.
  ```
* odd case, taking `e = a`, `f = b` would require
  ```text
  q^2 = a^4 - a^2*b^2 + b^4,
  ```
  but the factor package gives `r^2 = 3*a^2 + b^2` and `c^2 = b^2 - a^2`.

The actual formulas come from splitting `r-c` and `r+c` once more.

## 1. Even `n`: exact algebra and formulas

Rename the witnesses in `RawSqBranchEvenFactors` as `a b c r` to avoid clashing with the residual witness named `d`:

```text
0 < a, 0 < b, 0 < c, 0 < r,
m - n = a^2,
m + n = b^2,
n = 2*c^2,
2*m - n = 2*r^2.
```

Then

```text
m = c^2 + r^2,
a^2 = r^2 - c^2 = (r-c)*(r+c),
b^2 = r^2 + 3*c^2.
```

Since `a > 0`, we get `r^2 > c^2`, hence `c < r` from positivity. From the branch coprimality and parity one should prove `IsCoprime (r-c) (r+c)`. Since both factors are positive and their product is the square `a^2`, apply `posSqOfCoprimeMulSqStatement` a second time to obtain

```text
r - c = e^2,
r + c = f^2,
0 < e,
0 < f,
IsCoprime e f.
```

Then `e < f` because `f^2 - e^2 = 2*c > 0`. The residual square witness is **the old factor-root `b`**, not `r`:

```text
e^4 - e^2*f^2 + f^4
  = (r-c)^2 - (r-c)*(r+c) + (r+c)^2
  = r^2 + 3*c^2
  = b^2.
```

For the bound, the branch equation gives

```text
N^2 = n*(2*m-n) = (2*c^2)*(2*r^2) = (2*c*r)^2.
```

If `PositivePrimitiveEisensteinBadUnordered A N S` gives `0 < N`, then `N = 2*c*r`. Since `f^2 = r+c` and `0 < c < r`,

```text
r + c < 2*c*r = N,
```

and with `0 < f`, `f ≤ f^2`, so `f < N`.

Therefore the current `DescentBranchNEvenStatement` conclusion can be produced from the even factors, but only after this secondary split:

```text
residual e := secondary root of r-c,
residual f := secondary root of r+c,
residual d := b.
```

### Lean-checkable even algebra identities

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Algebra extracted from `RawSqBranchEvenFactors` after opening its witnesses.
Here `r` is the positive root in `2*m - n = 2*r^2`. -/
theorem rawEvenFactors_core_identities
    {m n a b c r : ℤ}
    (hma : m - n = a ^ 2)
    (hmb : m + n = b ^ 2)
    (hnc : n = 2 * c ^ 2)
    (h2mr : 2 * m - n = 2 * r ^ 2) :
    m = c ^ 2 + r ^ 2 ∧
      a ^ 2 = r ^ 2 - c ^ 2 ∧
      b ^ 2 = r ^ 2 + 3 * c ^ 2 := by
  have hm : m = c ^ 2 + r ^ 2 := by
    nlinarith
  constructor
  · exact hm
  constructor
  · calc
      a ^ 2 = m - n := by rw [hma]
      _ = r ^ 2 - c ^ 2 := by
        rw [hm, hnc]
        ring
  · calc
      b ^ 2 = m + n := by rw [hmb]
      _ = r ^ 2 + 3 * c ^ 2 := by
        rw [hm, hnc]
        ring

/-- The even secondary split gives the Eisenstein quartic square. -/
theorem rawEven_secondary_quartic_identity
    {b c r e f : ℤ}
    (he : r - c = e ^ 2)
    (hf : r + c = f ^ 2)
    (hb : b ^ 2 = r ^ 2 + 3 * c ^ 2) :
    b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 := by
  calc
    b ^ 2 = r ^ 2 + 3 * c ^ 2 := hb
    _ = (r - c) ^ 2 - (r - c) * (r + c) + (r + c) ^ 2 := by ring
    _ = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 := by
      rw [he, hf]
      ring

end MazurProof.RationalPointsN12
```

## 2. Odd `n`: exact algebra and formulas

Rename the witnesses in `RawSqBranchOddFactors` as `a b c r`:

```text
0 < a, 0 < b, 0 < c, 0 < r,
m - n = 2*a^2,
m + n = 2*b^2,
n = c^2,
2*m - n = r^2.
```

Then

```text
m = a^2 + b^2,
c^2 = b^2 - a^2,
r^2 = 3*a^2 + b^2,
r^2 - c^2 = 4*a^2,
r^2 + 3*c^2 = 4*b^2.
```

Since `a > 0`, `r^2 > c^2`, hence `c < r`. Since this is the odd branch, `c` and `r` are odd, so `r-c` and `r+c` are divisible by `2`. Define the positive halves

```text
x = (r-c)/2,
y = (r+c)/2.
```

Equivalently, in Lean avoid division and state

```text
r - c = 2*x,
r + c = 2*y.
```

Then

```text
x*y = ((r-c)*(r+c))/4 = (r^2-c^2)/4 = a^2.
```

With the branch coprimality one should prove `IsCoprime x y`. Apply `posSqOfCoprimeMulSqStatement` to `a^2 = x*y`, giving

```text
x = e^2,
y = f^2,
```

or, division-free,

```text
r - c = 2*e^2,
r + c = 2*f^2.
```

The residual square witness is **the old factor-root `b`**:

```text
4*(e^4 - e^2*f^2 + f^4)
  = (2*e^2)^2 - (2*e^2)*(2*f^2) + (2*f^2)^2
  = (r-c)^2 - (r-c)*(r+c) + (r+c)^2
  = r^2 + 3*c^2
  = 4*b^2,
```

hence

```text
b^2 = e^4 - e^2*f^2 + f^4.
```

For the bound,

```text
N^2 = n*(2*m-n) = c^2*r^2 = (c*r)^2.
```

With `0 < N`, `N = c*r`. Since `f^2 = (r+c)/2` and `0 < c < r`,

```text
(r+c)/2 < c*r = N,
```

so `f < N`.

Thus the current `DescentBranchNOddMOddStatement` conclusion can be produced from odd factors with formulas

```text
residual e := secondary root of (r-c)/2,
residual f := secondary root of (r+c)/2,
residual b := b.
```

### Lean-checkable odd algebra identities

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Algebra extracted from `RawSqBranchOddFactors` after opening its witnesses.
Here `r` is the positive root in `2*m - n = r^2`. -/
theorem rawOddFactors_core_identities
    {m n a b c r : ℤ}
    (hma : m - n = 2 * a ^ 2)
    (hmb : m + n = 2 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2mr : 2 * m - n = r ^ 2) :
    m = a ^ 2 + b ^ 2 ∧
      c ^ 2 = b ^ 2 - a ^ 2 ∧
      r ^ 2 = 3 * a ^ 2 + b ^ 2 ∧
      r ^ 2 - c ^ 2 = 4 * a ^ 2 ∧
      r ^ 2 + 3 * c ^ 2 = 4 * b ^ 2 := by
  have hm : m = a ^ 2 + b ^ 2 := by
    nlinarith
  have hc : c ^ 2 = b ^ 2 - a ^ 2 := by
    calc
      c ^ 2 = n := by rw [hnc]
      _ = b ^ 2 - a ^ 2 := by nlinarith
  have hr : r ^ 2 = 3 * a ^ 2 + b ^ 2 := by
    calc
      r ^ 2 = 2 * m - n := by rw [h2mr]
      _ = 3 * a ^ 2 + b ^ 2 := by
        rw [hm]
        nlinarith
  constructor
  · exact hm
  constructor
  · exact hc
  constructor
  · exact hr
  constructor
  · nlinarith
  · nlinarith

/-- The odd secondary split gives the Eisenstein quartic square.  The hypotheses
are division-free: `r-c = 2*e^2` and `r+c = 2*f^2`. -/
theorem rawOdd_secondary_quartic_identity
    {b c r e f : ℤ}
    (he : r - c = 2 * e ^ 2)
    (hf : r + c = 2 * f ^ 2)
    (hb4 : r ^ 2 + 3 * c ^ 2 = 4 * b ^ 2) :
    b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 := by
  have h4 : 4 * (e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4) = r ^ 2 + 3 * c ^ 2 := by
    calc
      4 * (e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4)
          = (2 * e ^ 2) ^ 2 - (2 * e ^ 2) * (2 * f ^ 2) + (2 * f ^ 2) ^ 2 := by ring
      _ = (r - c) ^ 2 - (r - c) * (r + c) + (r + c) ^ 2 := by
        rw [← he, ← hf]
      _ = r ^ 2 + 3 * c ^ 2 := by ring
  nlinarith

end MazurProof.RationalPointsN12
```

## 3. Lean-friendly next residuals

The current residuals are not necessarily false, but they are too coarse for the next proof step. They hide:

1. raw factor extraction;
2. secondary split of `r-c` and `r+c` or their halves;
3. conversion of the quartic triple to `NormalizedEisensteinBad`.

The next residuals should consume the checked factor packages directly.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Even raw-factor package implies the current branch-descent triple.
The output witness `q` is the `b` from `RawSqBranchEvenFactors`; the output
`e,f` come from the secondary split `r-c=e^2`, `r+c=f^2`. -/
def RawSqBranchEvenFactorsToDescentTripleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    RawSqBranchEvenFactors m n →
    ∃ e f q : ℤ,
      0 < e ∧ e < f ∧ 0 < q ∧ IsCoprime e f ∧
      q ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

/-- Odd raw-factor package implies the current branch-descent triple.
The output witness `q` is the `b` from `RawSqBranchOddFactors`; the output
`e,f` come from the secondary split `r-c=2*e^2`, `r+c=2*f^2`. -/
def RawSqBranchOddFactorsToDescentTripleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    RawSqBranchOddFactors m n →
    ∃ e f q : ℤ,
      0 < e ∧ e < f ∧ 0 < q ∧ IsCoprime e f ∧
      q ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

end MazurProof.RationalPointsN12
```

Then the existing residuals become thin parity wrappers around `rawSqBranchFactorizationStatement`.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

private lemma even_int_iff_two_dvd {n : ℤ} : Even n ↔ (2 : ℤ) ∣ n := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring

private lemma odd_int_not_two_dvd {n : ℤ} (hn : Odd n) : ¬ (2 : ℤ) ∣ n := by
  rintro ⟨k, hk⟩
  rcases hn with ⟨j, hj⟩
  rw [hk] at hj
  omega

/-- Existing even-`n` residual from the factor-package residual. -/
theorem descentBranchNEvenStatement_from_rawFactors
    (hEven : RawSqBranchEvenFactorsToDescentTripleStatement) :
    DescentBranchNEvenStatement := by
  intro A N S m n hbad hbranch hnEvenDiv
  rcases rawSqBranchFactorizationStatement hbranch with hEvenFac | hOddFac
  · exact hEven hbad hbranch hEvenFac.2
  · exact False.elim (odd_int_not_two_dvd hOddFac.1 hnEvenDiv)

/-- Existing odd-`n`, odd-`m` residual from the factor-package residual.
The `¬ 2 ∣ m` hypothesis is redundant after `rawSqBranchMParityStatement`. -/
theorem descentBranchNOddMOddStatement_from_rawFactors
    (hOdd : RawSqBranchOddFactorsToDescentTripleStatement) :
    DescentBranchNOddMOddStatement := by
  intro A N S m n hbad hbranch hnOddDiv hmOddDiv
  rcases rawSqBranchFactorizationStatement hbranch with hEvenFac | hOddFac
  · exact False.elim (hnOddDiv ((even_int_iff_two_dvd).1 hEvenFac.1))
  · exact hOdd hbad hbranch hOddFac.2

end MazurProof.RationalPointsN12
```

## 4. Secondary split statements that should be proved next

These are the real mathematical middle layer. They are more Lean-friendly than trying to prove the current branch residuals monolithically.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- The second split needed in the even branch.  This is essentially another
application of `posSqOfCoprimeMulSqStatement` to `a^2 = (r-c)*(r+c)`. -/
def RawEvenSecondarySplitStatement : Prop :=
  ∀ {a c r : ℤ},
    0 < c → c < r →
    IsCoprime (r - c) (r + c) →
    a ^ 2 = (r - c) * (r + c) →
    ∃ e f : ℤ,
      0 < e ∧ 0 < f ∧ e < f ∧ IsCoprime e f ∧
      r - c = e ^ 2 ∧ r + c = f ^ 2

/-- The second split needed in the odd branch, division-free.  The variables
`x,y` are the halves of `r-c` and `r+c`. -/
def RawOddSecondarySplitStatement : Prop :=
  ∀ {a c r x y : ℤ},
    0 < c → c < r →
    r - c = 2 * x → r + c = 2 * y →
    0 < x → 0 < y →
    IsCoprime x y →
    a ^ 2 = x * y →
    ∃ e f : ℤ,
      0 < e ∧ 0 < f ∧ e < f ∧ IsCoprime e f ∧
      x = e ^ 2 ∧ y = f ^ 2

/-- Even branch: all gcd/parity work needed to feed `RawEvenSecondarySplitStatement`.
This should be proved from `EisensteinSqBranch`, `RawSqBranchEvenFactors`, and
`rawSqBranchMParityStatement`. -/
def RawEvenSecondarySplitInputStatement : Prop :=
  ∀ {A N S m n a b c r : ℤ},
    EisensteinSqBranch A N S m n →
    0 < a → 0 < b → 0 < c → 0 < r →
    m - n = a ^ 2 → m + n = b ^ 2 →
    n = 2 * c ^ 2 → 2 * m - n = 2 * r ^ 2 →
    0 < c ∧ c < r ∧ IsCoprime (r - c) (r + c) ∧
      a ^ 2 = (r - c) * (r + c)

/-- Odd branch: all gcd/parity work needed to feed `RawOddSecondarySplitStatement`.
This should be proved from `EisensteinSqBranch`, `RawSqBranchOddFactors`, and
`rawSqBranchMParityStatement`. -/
def RawOddSecondarySplitInputStatement : Prop :=
  ∀ {A N S m n a b c r : ℤ},
    EisensteinSqBranch A N S m n →
    0 < a → 0 < b → 0 < c → 0 < r →
    m - n = 2 * a ^ 2 → m + n = 2 * b ^ 2 →
    n = c ^ 2 → 2 * m - n = r ^ 2 →
    ∃ x y : ℤ,
      0 < c ∧ c < r ∧
      r - c = 2 * x ∧ r + c = 2 * y ∧
      0 < x ∧ 0 < y ∧ IsCoprime x y ∧
      a ^ 2 = x * y

end MazurProof.RationalPointsN12
```

## 5. Corrected residuals targeting `NormalizedEisensteinBad`

If the final assembly wants `NormalizedEisensteinBad`, the best bridge is to separate “quartic triple found” from “normalized bad object built”. The bridge is probably what `N12CheckedDescentBridge.lean` should contain if it exists.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Bridge from a smaller positive primitive Eisenstein-quartic triple to the
project's normalized bad predicate.  Expected construction: `A' = e`, `N' = f`,
`S' = q`. -/
def QuarticTripleToNormalizedEisensteinBadBelowStatement : Prop :=
  ∀ {e f q N : ℤ},
    0 < e → e < f → 0 < q → IsCoprime e f →
    q ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 →
    f < N →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Even raw factors directly imply a normalized descent, after the secondary split
and the quartic-triple bridge. -/
def RawSqBranchEvenFactorsToNormalizedDescentStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    RawSqBranchEvenFactors m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Odd raw factors directly imply a normalized descent, after the secondary split
and the quartic-triple bridge. -/
def RawSqBranchOddFactorsToNormalizedDescentStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    RawSqBranchOddFactors m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

This is the clean final shape. The existing `DescentBranchNEvenStatement` and `DescentBranchNOddMOddStatement` are still usable as compatibility wrappers, but they should not be the theorem one proves directly after `rawSqBranchFactorizationStatement`.

## 6. Reuse audit for `N12FourSquaresAP`, `N12EulerAux`, `N12CheckedDescentBridge`

I could not inspect those files through the connector: direct fetches returned `404`, and code search returned no hits for their names. So I cannot honestly say “there is already theorem `X`”.

Mathematically, the reusable theorem should **not** be a four-squares-in-AP theorem at this step. The required step is an Euler-style secondary split:

* even: from
  ```text
  a^2 = (r-c)*(r+c),  b^2 = r^2 + 3*c^2
  ```
  split `r-c=e^2`, `r+c=f^2`, then prove
  ```text
  b^2 = e^4 - e^2*f^2 + f^4;
  ```
* odd: from
  ```text
  a^2 = ((r-c)/2)*((r+c)/2),  4*b^2 = r^2 + 3*c^2
  ```
  split `(r-c)/2=e^2`, `(r+c)/2=f^2`, then prove
  ```text
  b^2 = e^4 - e^2*f^2 + f^4.
  ```

So if reuse exists, I would expect it in `N12EulerAux.lean` under a theorem shaped like one of these:

```lean
def EulerEvenSecondaryDescentShape : Prop :=
  ∀ {a b c r : ℤ},
    0 < a → 0 < b → 0 < c → 0 < r → c < r →
    IsCoprime (r - c) (r + c) →
    a ^ 2 = (r - c) * (r + c) →
    b ^ 2 = r ^ 2 + 3 * c ^ 2 →
    ∃ e f : ℤ,
      0 < e ∧ e < f ∧ IsCoprime e f ∧
      b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4

def EulerOddSecondaryDescentShape : Prop :=
  ∀ {a b c r x y : ℤ},
    0 < a → 0 < b → 0 < c → 0 < r → c < r →
    r - c = 2 * x → r + c = 2 * y →
    0 < x → 0 < y → IsCoprime x y →
    a ^ 2 = x * y →
    r ^ 2 + 3 * c ^ 2 = 4 * b ^ 2 →
    ∃ e f : ℤ,
      0 < e ∧ e < f ∧ IsCoprime e f ∧
      b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4
```

`N12CheckedDescentBridge.lean`, if available, is the likely place for the `QuarticTripleToNormalizedEisensteinBadBelowStatement` bridge. `N12FourSquaresAP.lean` is probably not the right tool for this raw branch step; it is more relevant to ruling out or collapsing arithmetic progressions of squares, whereas here the required descent is the explicit split of `r±c`.

## 7. Recommended immediate implementation order

1. Prove the two algebra identity theorems above; they should be quick `ring`/`nlinarith` checks.
2. Prove `RawEvenSecondarySplitInputStatement` and `RawOddSecondarySplitInputStatement`; these are gcd/parity bookkeeping from the branch and factor packages.
3. Prove `RawEvenSecondarySplitStatement` and `RawOddSecondarySplitStatement` via `posSqOfCoprimeMulSqStatement`.
4. Prove `RawSqBranchEvenFactorsToDescentTripleStatement` and `RawSqBranchOddFactorsToDescentTripleStatement` using the explicit formulas.
5. Either keep the existing residuals as wrappers, or replace the descent-facing residuals with the normalized versions using `QuarticTripleToNormalizedEisensteinBadBelowStatement`.
