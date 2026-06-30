# Q2690 (dm-codex1): adversarial audit of raw Eisenstein square branch

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace: `MazurProof.RationalPointsN12`

I am using the branch definition exactly as supplied in the prompt:

```lean
def EisensteinSqBranch (A N S m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  A ^ 2 = (m - n) * (m + n) ∧
  N ^ 2 = n * (2 * m - n) ∧
  S = m ^ 2 - m * n + n ^ 2
```

## 1. Verdict on the displayed `(A ± N)^2` identities

They are **not** raw algebraic consequences of `EisensteinSqBranch` as stated.

The proposed identities were

```lean
(A - N)^2 = (m - 3*n)*(m - n)
(A + N)^2 = (m + n)*(m + 3*n)
```

The branch gives `A^2` and `N^2`, but it gives no linear control of `A * N`. Expanding the left sides,

```text
(A - N)^2 = A^2 + N^2 - 2*A*N
(A + N)^2 = A^2 + N^2 + 2*A*N
```

and from the branch alone,

```text
A^2 + N^2
  = (m - n)*(m + n) + n*(2*m - n)
  = m^2 + 2*m*n - 2*n^2.
```

Therefore the first proposed identity would require

```text
2*A*N = n*(6*m - 5*n),
```

while the second proposed identity would require

```text
2*A*N = n*(2*m + 5*n).
```

Those are extra assertions about `A*N`; they do not follow from the two square equations. What the branch actually controls is only the square of the product:

```text
(A*N)^2 = ((m - n)*(m + n)) * (n*(2*m - n)).
```

There is also a stronger consistency check. If both displayed identities held simultaneously, then adding them and using the branch computation of `A^2 + N^2` gives

```text
2*(A^2 + N^2)
  = (m - 3*n)*(m - n) + (m + n)*(m + 3*n)
  = 2*m^2 + 6*n^2.
```

But the branch gives

```text
2*(A^2 + N^2) = 2*m^2 + 4*m*n - 4*n^2.
```

So both proposed identities force

```text
4*m*n - 4*n^2 = 6*n^2,
```

hence, since `0 < n`,

```text
2*m = 5*n.
```

Together with `IsCoprime m n` and positivity this forces `m = 5`, `n = 2`; then the branch would require

```text
A^2 = (5 - 2)*(5 + 2) = 21,
```

which is impossible over the integers. Thus the pair of identities is not just missing a small sign lemma; it is a false/too-strong descent target unless one has already proved the whole branch contradictory by some other means.

A separate sign-symmetry obstruction points the same way: the branch is invariant under replacing `A` by `-A` or `N` by `-N`, but `(A + N)^2` and `(A - N)^2` swap under such a sign change. The right-hand sides differ by

```text
(m + n)*(m + 3*n) - (m - 3*n)*(m - n) = 8*m*n,
```

which is positive under the branch inequalities. So the branch data cannot canonically assign those two different values to the two signed sums.

## 2. Correct product-square factors to split

The honest square products already present in the branch are exactly these:

```text
A^2 = (m - n)*(m + n)
N^2 = n*(2*m - n)
```

The positivity needed by the existing positive square-factor lemmas is available directly:

```text
0 < m - n      from n < m
0 < m + n      from 0 < n < m
0 < n          by hypothesis
0 < 2*m - n    from n < m
```

The gcds are controlled only up to the factor `2`:

```text
gcd(m - n, m + n) ∣ 2
gcd(n, 2*m - n) ∣ 2
```

Moreover `m` is forced odd: from `A^2 = m^2 - n^2`, if `m` were even then coprimality would make `n` odd, giving `A^2 ≡ -1 ≡ 3 mod 4`, impossible.

So the correct factor split is parity-based:

| parity of `n` | split from `A^2 = (m-n)*(m+n)` | split from `N^2 = n*(2*m-n)` | lemmas used |
|---|---|---|---|
| `Even n` | `m - n = a^2`, `m + n = b^2` because the two factors are coprime | `n = 2*c^2`, `2*m - n = 2*d^2` because the two factors have gcd `2` | `PosSqOfCoprimeMulSqStatement` for the `A` product; `PosTwoSqOfGcdTwoMulSqStatement` for the `N` product |
| `Odd n` | `m - n = 2*a^2`, `m + n = 2*b^2` because the two factors have gcd `2` | `n = c^2`, `2*m - n = d^2` because the two factors are coprime | `PosTwoSqOfGcdTwoMulSqStatement` for the `A` product; `PosSqOfCoprimeMulSqStatement` for the `N` product |

This is the replacement raw-branch decomposition compatible with the actual hypotheses. It does not mention `A + N` or `A - N`.

## 3. Corrected Lean Prop signatures for the next residuals

Here is the shape I would use. The `_corrected` suffix is intentional to avoid colliding with any currently-added false residual while auditing; when replacing the bad residual, rename the corrected version back to the project’s expected name.

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Factors obtained in the `n` even case. -/
def RawSqBranchEvenFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = a ^ 2 ∧
    m + n = b ^ 2 ∧
    n = 2 * c ^ 2 ∧
    2 * m - n = 2 * d ^ 2

/-- Factors obtained in the `n` odd case. -/
def RawSqBranchOddFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = 2 * a ^ 2 ∧
    m + n = 2 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = d ^ 2

/-- Cheap parity residual useful before applying the gcd-1/gcd-2 split lemmas. -/
def RawSqBranchMParityStatement : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
    Odd m

/-- Honest replacement for the false `(A ± N)^2` factorization residual. -/
def RawSqBranchFactorizationStatement_corrected : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
      (Even n ∧ RawSqBranchEvenFactors m n) ∨
      (Odd n ∧ RawSqBranchOddFactors m n)

/-- The next hard residual: do the actual descent/contradiction from the honest factors. -/
def RawSqBranchDescentFromFactorsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
      ((Even n ∧ RawSqBranchEvenFactors m n) ∨
       (Odd n ∧ RawSqBranchOddFactors m n)) →
    False

end MazurProof.RationalPointsN12
```

If the existing positive-square lemmas return sign-free square roots rather than positive roots, weaken the two factor package definitions by deleting the `0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧` prefix. The positive-root version is mathematically available because every factor being split is strictly positive; one obtains positive roots by replacing roots with their absolute values.

The important structural correction is that the residual should split the products already known to be squares:

```text
(m - n)*(m + n)
n*(2*m - n)
```

not the unsupported products involving `m - 3*n` and `m + 3*n`.

## 4. Small Lean-checkable identities that definitely follow

A useful identity involving `A^2`, `N^2`, `S`, `m`, and `n` is:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- The raw branch controls the sum of the two known squares; no `A*N` term appears. -/
theorem EisensteinSqBranch_A_sq_add_N_sq_eq_S
    {A N S m n : ℤ} (h : EisensteinSqBranch A N S m n) :
    A ^ 2 + N ^ 2 = S + 3 * m * n - 3 * n ^ 2 := by
  rcases h with ⟨_, _, _, hA, hN, hS⟩
  rw [hA, hN, hS]
  ring

end MazurProof.RationalPointsN12
```

And the exact statement of what is known about `A*N` is only its square:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- The branch controls `(A*N)^2`, not the sign or a linear formula for `A*N`. -/
theorem EisensteinSqBranch_A_mul_N_sq
    {A N S m n : ℤ} (h : EisensteinSqBranch A N S m n) :
    (A * N) ^ 2 = ((m - n) * (m + n)) * (n * (2 * m - n)) := by
  rcases h with ⟨_, _, _, hA, hN, _⟩
  rw [mul_pow, hA, hN]

end MazurProof.RationalPointsN12
```

I have not used or needed any identity involving `(A + N)^2` or `(A - N)^2`; those require extra control of `A*N` that the branch does not provide.
