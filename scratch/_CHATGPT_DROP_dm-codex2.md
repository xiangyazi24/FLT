# Q2686 dm-codex2: N=12 Eisenstein residual audit

Scope: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`, in namespace `MazurProof.RationalPointsN12`.  This is based on the residual interfaces in the prompt; the connector-visible `main`/`scratch` refs still do not expose the target Lean file itself.

## Recommendation

Attack **raw branch descent** next, but split it before trying to prove the current all-in-one residual.  This gives the most mathematical progress because it is the first place where the now-proved positive square-factor lemmas should eliminate a major part of the descent.  It also stress-tests whether `EisensteinSqBranch` exposes the right raw-branch data before the more delicate divided-by-3 branch is attempted.

I would not attack `NormalizedBadParamStatement` first.  It is broad and mostly bookkeeping-heavy: primitive denominator clearing, gcd transport, the `3`-adic branch decision, and symmetry all interact.  A raw-branch descent proof will determine the exact extraction lemmas that the parametrization must provide.  I would also delay `DividedSquareBranchUnitOrDescendsStatement` until the raw branch skeleton is stable, since divided branch descent should reuse the same four-square/AP descent core plus extra `3`-adic normalization.

## Current statement audit

1. `DescentFromBranchUnorderedStatement` is the right mathematical target **only if** `EisensteinSqBranch` is genuinely the non-divided/raw branch and therefore excludes the trivial unit branch.  If `EisensteinSqBranch 1 1 1 m n` is admissible for some `m n`, then the current statement is too strong/false, because `NormalizedEisensteinBad A' N' S'` should force `0 < N'`, while `N' < 1` is impossible in the usual normalized-positive setting.  Either prove the no-unit lemma below or replace the current residual by the nonunit/unit-or-descends interface below.

2. The word `Unordered` is potentially misleading.  The inequality `N' < N` is measured against the **second argument of the branch orientation**, not necessarily the original normalized denominator.  This is fine for final assembly only if the swapped cases are called as `DescentFromBranchUnorderedStatement` on `(N, A, S)` and the assembly separately uses the normalized inequality, typically `A < N`, to conclude `N' < original N`.

3. `DividedSquareBranchUnitOrDescendsStatement` has the correct high-level shape.  For proof engineering, split it into a nonunit descent lemma and derive the current disjunction by `by_cases hunit : A = 1 ∧ N = 1 ∧ S = 1`.

4. `NormalizedBadParamStatement` should not be strengthened into a huge theorem carrying every positivity/coprimality/parity fact.  Keep its branch-result shape, but add branch extraction lemmas.  If `EisensteinSqBranch` does not let you prove the factorization/coprimality lemmas below, then the branch predicate is too weak as an interface for descent.

## Interface repair / compatibility layer

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Raw branch cannot be the unit solution.  Prove this if you want to keep
`DescentFromBranchUnorderedStatement` exactly as currently stated. -/
def RawSqBranchNoUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1)

/-- Safer raw-branch target: descent only after the unit case is excluded. -/
def RawSqBranchNonunitDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Symmetric with the divided branch residual, and robust if the raw branch
predicate accidentally admits the unit solution. -/
def RawSqBranchUnitOrDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Compatibility target: this is what lets the current residual be retained. -/
def RawSqBranchBridgeToCurrentStatement : Prop :=
  RawSqBranchNoUnitStatement →
  RawSqBranchNonunitDescendsStatement →
  DescentFromBranchUnorderedStatement

/-- Proof-engineering split for the divided branch. -/
def DividedSquareBranchNonunitDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    DividedSquareBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- The current divided residual follows from the nonunit version by `by_cases`. -/
def DividedSquareBranchBridgeStatement : Prop :=
  DividedSquareBranchNonunitDescendsStatement →
  DividedSquareBranchUnitOrDescendsStatement

end MazurProof.RationalPointsN12
```

## Raw branch decomposition: exact Lean-facing targets

The raw branch should be reduced to four positive square factors.  The two products to expose are

* plus product: `(A + N)^2 = (m + n) * (m + 3*n)`;
* minus product: `(A - N)^2 = (m - 3*n) * (m - n)`.

Then use the already-proved square-factor lemmas twice.  The parity cases are exact:

* if `m` and `n` have opposite parity, all four factors are odd and the relevant factor pairs are coprime, so use `PosSqOfCoprimeMulSqStatement` on both products;
* if `m` and `n` are both odd, all four factors are divisible by `2`, the halves are coprime, so use `PosTwoSqOfGcdTwoMulSqStatement` on both products;
* `m` and `n` both even must be impossible from primitivity/coprimality of the raw branch.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- First raw-branch extraction: the two products of positive factors whose
products are squares.  This should be a mostly `unfold EisensteinSqBranch` +
`ring_nf` lemma plus positivity from the branch inequalities/nonunit case. -/
def RawSqBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    EisensteinSqBranch A N S m n →
      0 < m - 3 * n ∧
      0 < m - n ∧
      0 < m + n ∧
      0 < m + 3 * n ∧
      (A - N)^2 = (m - 3 * n) * (m - n) ∧
      (A + N)^2 = (m + n) * (m + 3 * n)

/-- Second raw-branch extraction: exact parity/coprimality inputs for the two
positive square-factor lemmas.  In the odd-odd case, the coprimality is after
halving both factors. -/
def RawSqBranchParityCoprimeInputsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
      ((((Odd m ∧ Even n) ∨ (Even m ∧ Odd n)) →
          IsCoprime (m - 3 * n) (m - n) ∧
          IsCoprime (m + n) (m + 3 * n)) ∧
       ((Odd m ∧ Odd n) →
          (2 : ℤ) ∣ m - 3 * n ∧
          (2 : ℤ) ∣ m - n ∧
          (2 : ℤ) ∣ m + n ∧
          (2 : ℤ) ∣ m + 3 * n ∧
          IsCoprime ((m - 3 * n) / 2) ((m - n) / 2) ∧
          IsCoprime ((m + n) / 2) ((m + 3 * n) / 2)) ∧
       ¬ (Even m ∧ Even n))

/-- Opposite-parity square split.  This is exactly where
`PosSqOfCoprimeMulSqStatement` should be invoked twice, with `z = A - N` and
`z = A + N`. -/
def RawSqBranchOppParitySquareSplitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    EisensteinSqBranch A N S m n →
    ((Odd m ∧ Even n) ∨ (Even m ∧ Odd n)) →
    ∃ r s t u : ℤ,
      0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < u ∧
      m - 3 * n = r^2 ∧
      m - n = s^2 ∧
      m + n = t^2 ∧
      m + 3 * n = u^2

/-- Odd-odd square split.  This is exactly where
`PosTwoSqOfGcdTwoMulSqStatement` should be invoked twice, with `z = A - N` and
`z = A + N`. -/
def RawSqBranchOddOddSquareSplitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    EisensteinSqBranch A N S m n →
    Odd m ∧ Odd n →
    ∃ r s t u : ℤ,
      0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < u ∧
      m - 3 * n = 2 * r^2 ∧
      m - n = 2 * s^2 ∧
      m + n = 2 * t^2 ∧
      m + 3 * n = 2 * u^2

/-- The genuinely hard remaining descent after square-factor splitting:
from four scaled squares in arithmetic progression, construct the smaller
normalized Eisenstein bad triple.  This is the mathematical core of the raw
branch after the two square-factor lemmas have done their work. -/
def RawSqBranchAPDescentStatement : Prop :=
  ∀ {A N S m n e r s t u : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    (e = 1 ∨ e = 2) →
    0 < r → 0 < s → 0 < t → 0 < u →
    m - 3 * n = e * r^2 →
    m - n = e * s^2 →
    m + n = e * t^2 →
    m + 3 * n = e * u^2 →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- The intended proof graph for raw descent.  After these pieces are proved,
the current raw residual should be a short parity split plus calls to the AP
core. -/
def RawSqBranchDescentFromPiecesStatement : Prop :=
  RawSqBranchFactorizationStatement →
  RawSqBranchParityCoprimeInputsStatement →
  RawSqBranchOppParitySquareSplitStatement →
  RawSqBranchOddOddSquareSplitStatement →
  RawSqBranchAPDescentStatement →
  RawSqBranchNonunitDescendsStatement

end MazurProof.RationalPointsN12
```

## Proof obligations for the chosen target

For `RawSqBranchFactorizationStatement`, unfold `EisensteinSqBranch` and prove the two displayed product identities by `ring_nf`.  The positivity goals are the important part: prove `0 < m - 3*n`, `0 < m - n`, `0 < m + n`, and `0 < m + 3*n` from the branch inequalities and nonunit hypothesis.  If this cannot be done, the raw branch predicate is missing a strict-orientation/nondegeneracy field or extraction lemma.

For `RawSqBranchParityCoprimeInputsStatement`, prove the usual gcd transport facts: any common divisor of `m+n` and `m+3*n`, or of `m-3*n` and `m-n`, divides `2*m` and `2*n`.  In the opposite-parity case the factors are odd, so the possible factor `2` is eliminated and the gcd is a unit.  In the odd-odd case the original factors are all even, and the same divisibility argument after dividing by `2` gives coprime halves.  The both-even case should contradict primitive/coprime branch data.

For `RawSqBranchOppParitySquareSplitStatement`, apply the proved `PosSqOfCoprimeMulSqStatement` to the minus product with `x = m - 3*n`, `y = m - n`, `z = A - N`, and to the plus product with `x = m + n`, `y = m + 3*n`, `z = A + N`.

For `RawSqBranchOddOddSquareSplitStatement`, apply the proved `PosTwoSqOfGcdTwoMulSqStatement` to the same two products.  The hypotheses `(2 : ℤ) ∣ x`, `(2 : ℤ) ∣ y`, and `IsCoprime (x/2) (y/2)` are exactly the outputs of `RawSqBranchParityCoprimeInputsStatement`.

For `RawSqBranchAPDescentStatement`, do not mix the square-factor proof with the descent construction.  Treat the data

```lean
m - 3 * n = e * r^2
m - n     = e * s^2
m + n     = e * t^2
m + 3 * n = e * u^2
```

as the four scaled squares in arithmetic progression.  The obligation is to construct explicit `A' N' S'` satisfying `NormalizedEisensteinBad A' N' S'` and prove the strict measure bound `N' < N`.  This is now the mathematically hardest subgoal inside raw descent; the factor-square part should be routine once the two local positive square-factor lemmas are used.

## Exact next Lean target

Add the interface block above, then prove in this order:

1. `RawSqBranchFactorizationStatement`.
2. `RawSqBranchParityCoprimeInputsStatement`.
3. `RawSqBranchOppParitySquareSplitStatement` and `RawSqBranchOddOddSquareSplitStatement` using the already-proved positive square-factor lemmas.
4. `RawSqBranchAPDescentStatement`.
5. `RawSqBranchDescentFromPiecesStatement`, then either `RawSqBranchBridgeToCurrentStatement` or switch the final assembly to consume `RawSqBranchUnitOrDescendsStatement`.

This sequence gives the biggest mathematical payoff: after step 3, all remaining raw-branch difficulty is isolated in one classical four-square/AP descent statement, and the same AP core can be reused when attacking the divided-by-3 branch.
