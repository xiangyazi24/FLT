# Q2687 dm-codex2: N=12 Eisenstein quartic residual audit

Target requested: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`, namespace `MazurProof.RationalPointsN12`.

Connector note: the GitHub connector did not expose the target Lean file at the requested path on `scratch` or on the default branch, so this audit is based on the exact residual interfaces supplied in the prompt. The drop below is therefore an interface/proof-obligation proposal, not a checked edit of the target Lean file.

## Recommendation

Attack `DescentFromBranchUnorderedStatement` next, but do not attack it in its current unordered form. Split it into an ordered raw-branch descent interface plus parity-extraction lemmas.

Reason: `NormalizedBadParamStatement` is mostly factor-gcd/parity bookkeeping once the two positive square-factor lemmas are available. The divided branch is genuinely delicate because it has an exceptional unit alternative and a 3-adic case distinction. Raw branch descent is the first place where the infinite descent construction itself is tested. Proving it next gives the largest mathematical progress and will also validate whether the branch predicates carry enough data for the final assembly.

The current raw residual is asymmetric:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

def DescentFromBranchUnorderedStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

Despite the name, this is not really unordered: it promises descent below the second input `N`. That is safe only if the caller has already oriented the pair so that the second input is the descent measure. If final assembly handles the alternative `EisensteinSqBranch N A S m n` by applying the same statement to `(N,A,S)`, the conclusion becomes `N' < A`, not `N' < N`. That is fine for a `max A N` measure, or if the assembly also knows `A < N`, but it is not enough for a proof by minimal denominator `N` without an extra ordering bridge.

## Interface change I recommend

Make the orientation explicit. Keep the old residual only as a compatibility wrapper if the assembly already supplies the order.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Raw branch descent with the descent measure exposed explicitly.

This is the preferred target.  The hypothesis `A ≤ N` is the missing contract
behind the current name `DescentFromBranchUnorderedStatement`.
-/
def DescentFromBranchOrderedStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    A ≤ N →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Symmetric version, useful if final assembly descends by height rather than by
second coordinate. -/
def DescentFromBranchBelowMaxStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < max A N

end MazurProof.RationalPointsN12
```

If the final assembly minimizes the denominator coordinate, use `DescentFromBranchOrderedStatement`. If it minimizes height, use `DescentFromBranchBelowMaxStatement` and make the divided residual match the same measure.

## Lean-friendly decomposition for raw branch descent

The key is to separate branch unpacking from the actual descent construction. The branch predicate should not be forced to store positive signs for `m n`; use extraction lemmas that return positive square roots `u v`.

The raw branch should be reduced to these two parity-normalized factor packages. In the following statements the raw branch is oriented so that

`U = A^2 + N^2 - S`,

`V = (A^2 + N^2 + S) / 3`,

and the raw factor identity is `U * V = (A * N)^2`.

### 1. Odd raw branch extraction

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Odd raw branch extraction.

Proof obligation:
* derive positivity of the two branch factors;
* prove `IsCoprime U V` from primitive/unordered data;
* use `PosSqOfCoprimeMulSqStatement` on
  `x = A^2 + N^2 - S`,
  `y = (A^2 + N^2 + S) / 3`,
  `z = A * N`;
* clear the `/ 3` denominator to rewrite the second square as
  `A^2 + N^2 + S = 3 * v^2`.
-/
def RawBranchOddSquareDataStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ¬ (2 : ℤ) ∣ A * N →
    ∃ u v : ℤ,
      0 < u ∧ 0 < v ∧
        A^2 + N^2 - S = u^2 ∧
        A^2 + N^2 + S = 3 * v^2 ∧
        A * N = u * v

end MazurProof.RationalPointsN12
```

Parity in this case: `¬ (2 : ℤ) ∣ A * N` means both `A` and `N` are odd, since primitive excludes both even and the negated divisibility excludes exactly-one-even. Then `A^2 + N^2` is even and the normalized bad equation forces `S` odd, so `A^2 + N^2 ± S` are odd. The raw branch puts the factor `3` on the plus factor, and the two reduced factors `U,V` are coprime. This is exactly the input shape of `PosSqOfCoprimeMulSqStatement`.

### 2. Even raw branch extraction

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Even raw branch extraction.

Proof obligation:
* primitive data plus `(2 : ℤ) ∣ A * N` gives exactly one of `A,N` even;
* the two raw reduced factors
  `U = A^2 + N^2 - S` and
  `V = (A^2 + N^2 + S) / 3`
  are both even;
* prove `IsCoprime (U / 2) (V / 2)`;
* use `PosTwoSqOfGcdTwoMulSqStatement` on `U,V,A*N`;
* clear the `/ 3` denominator to get the displayed `6 * v^2` equation.
-/
def RawBranchEvenTwoSquareDataStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    (2 : ℤ) ∣ A * N →
    ∃ u v : ℤ,
      0 < u ∧ 0 < v ∧
        A^2 + N^2 - S = 2 * u^2 ∧
        A^2 + N^2 + S = 6 * v^2 ∧
        A * N = 2 * u * v

end MazurProof.RationalPointsN12
```

Parity in this case: primitive data excludes both `A,N` even, so `(2 : ℤ) ∣ A * N` means exactly one is even. Then `A^2 + N^2` and `S` are odd, hence the raw factors `A^2 + N^2 ± S` are even. Since `3` is odd, `V = (A^2 + N^2 + S) / 3` is even as well. The reduced half-factors are coprime, so `PosTwoSqOfGcdTwoMulSqStatement` gives `U = 2*u^2` and `V = 2*v^2`, hence the original plus factor is `6*v^2`.

### 3. Odd raw descent core

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The odd raw descent core, after all gcd/parity/square-factor bookkeeping has
been eliminated.

This is one of the two genuinely mathematical cores.  The proof should define
explicit descendants from `A,N,u,v`, prove the Eisenstein quartic identity for
the descendants, prove normalization/primitive conditions, and prove the strict
bound `N' < N` using `A ≤ N` and positivity.
-/
def RawOddDescentCoreStatement : Prop :=
  ∀ {A N S u v : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    A ≤ N →
    0 < u →
    0 < v →
    A^2 + N^2 - S = u^2 →
    A^2 + N^2 + S = 3 * v^2 →
    A * N = u * v →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

The core proof should not mention the original branch variables `m n`; signs have already been normalized to positive `u v`. The obligations are purely algebraic: descendant formula, quartic identity, primitive normalization, positivity, and the strict inequality.

### 4. Even raw descent core

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The even raw descent core, after the `2 * square` extraction.

This is the same descent construction as the odd core, but with the parity-normalized
factor equations `2*u^2` and `6*v^2`.  It should be proved separately rather than
hidden behind `ring_nf` inside the final raw descent theorem.
-/
def RawEvenDescentCoreStatement : Prop :=
  ∀ {A N S u v : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    A ≤ N →
    0 < u →
    0 < v →
    A^2 + N^2 - S = 2 * u^2 →
    A^2 + N^2 + S = 6 * v^2 →
    A * N = 2 * u * v →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

The even core is where most denominator-clearing mistakes show up. Keeping it separate prevents the proof from silently using the odd formulas in the exactly-one-even case.

### 5. Ordered raw branch assembly from the four pieces

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The small assembly theorem for raw branch descent.

This should be a short proof: split on `(2 : ℤ) ∣ A * N`, call the corresponding
extraction lemma, then call the corresponding core descent lemma.
-/
def RawBranchDescentFromParityPiecesStatement : Prop :=
  RawBranchOddSquareDataStatement →
  RawBranchEvenTwoSquareDataStatement →
  RawOddDescentCoreStatement →
  RawEvenDescentCoreStatement →
  DescentFromBranchOrderedStatement

end MazurProof.RationalPointsN12
```

This last statement is intentionally just glue. If it is not a short proof, the square-factor extraction lemmas are still too weak.

## Exact proof obligations for the recommended target

For `RawBranchOddSquareDataStatement`:

1. Define `U := A^2 + N^2 - S` and `V := (A^2 + N^2 + S) / 3`.
2. Prove `0 < U` and `0 < V` from the branch equations/normalization.
3. Prove `IsCoprime U V`. The only allowed common prime is already accounted for by the explicit raw `3` on the plus factor; parity is odd here.
4. Prove `(A * N)^2 = U * V`.
5. Apply `PosSqOfCoprimeMulSqStatement` and clear the `/ 3` equality.

For `RawBranchEvenTwoSquareDataStatement`:

1. Use primitive data to turn `(2 : ℤ) ∣ A * N` into exactly-one-even for `A,N`.
2. Prove `(2 : ℤ) ∣ U` and `(2 : ℤ) ∣ V`.
3. Prove `IsCoprime (U / 2) (V / 2)`.
4. Prove `(A * N)^2 = U * V`.
5. Apply `PosTwoSqOfGcdTwoMulSqStatement` and clear the `/ 3` equality.

For the two core descents:

1. Give explicit formulas for `A' N' S'` in terms of `A,N,u,v`.
2. Prove `NormalizedEisensteinBad A' N' S'` field by field: positivity, primitive gcd, normalized congruence/parity conditions, and the quartic equation.
3. Prove the strict inequality `N' < N`. This should be a separate inequality lemma if it needs more than `nlinarith` after positivity and order hypotheses.
4. Avoid using branch predicates inside these core proofs; all branch content should be in the extraction lemmas.

## Statements to fix or watch

1. `DescentFromBranchUnorderedStatement` is misnamed and probably too strong as written unless the second coordinate is always the chosen measure. Replace it with `DescentFromBranchOrderedStatement` or with the symmetric `DescentFromBranchBelowMaxStatement`.

2. `DividedSquareBranchUnitOrDescendsStatement` has the same orientation issue. The ordered version should be:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

def DividedSquareBranchUnitOrDescendsOrderedStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    A ≤ N →
    DividedSquareBranch A N S m n →
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        NormalizedEisensteinBad A' N' S' ∧ N' < N

end MazurProof.RationalPointsN12
```

If the assembly uses height instead of denominator, make the conclusion `N' < max A N` instead.

3. The unit alternative `(A = 1 ∧ N = 1 ∧ S = 1)` is only correct if the positive/normalized hypotheses force `0 < S`. If `S` is allowed to be negative in any residual, the correct unit alternative is either `A = 1 ∧ N = 1 ∧ S^2 = 1` or two signed cases. Given the stated positive primitive name, `S = 1` is probably intended, but the proof should expose the positivity fact explicitly.

4. `NormalizedBadParamStatement` is acceptable as a branch frontier only if each branch predicate is sign-insensitive or carries enough equations to recover positive roots. If `EisensteinSqBranch` or `DividedSquareBranch` stores linear equations involving `m n`, add local extraction lemmas that replace `m n` by positive `u v`; do not make downstream descent depend on arbitrary signs of existential branch parameters.

5. The final assembly needs an explicit bridge from `NormalizedEisensteinBad A N S` to `PositivePrimitiveEisensteinBadUnordered A N S` and the chosen order/height measure. If that bridge is not already a theorem, add it as an assembly prerequisite rather than burying it inside each residual.

## Bottom line

The next target should be raw branch descent, but with the ordered interface above. Prove the two extraction lemmas first using the already-proved square-factor lemmas, then prove the two parity-specific descent cores. After that, `RawBranchDescentFromParityPiecesStatement` should be only a parity split and two applications. This isolates the real mathematical descent from gcd/parity bookkeeping and prevents another stale/mismatched assembly layer.