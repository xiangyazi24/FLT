# Q2714 dm-codex2: divided branch vs RationalPointsN12 half-factor infrastructure

Target requested: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, especially the pythagorean quartic half-factor lemmas, and the local WIP divided branch in `N12QuarticEisenstein.lean`.

## Connector audit status

I could not confirm the exact Lean statements of the named theorems from the connected repo. The connector has write access, and the `scratch` branch exists, but the requested file path

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
```

was not present at that path on either `scratch` or `main` through `fetch_file`. Code search for the exact names also returned no hits. Therefore I am **not** claiming checked `#check` output for the listed APIs below. Where I refer to existing names, I treat them as theorem roles inferred from the names in the prompt; the Lean code blocks are proposed bridge/interface statements to add once the real imported file is visible.

## Executive answer

The existing pythagorean quartic half-factor infrastructure is probably reusable only as an **upstream half-factor interface for the original Eisenstein quartic in `(A,N,S)`**, not as a direct proof of the divided branch residual.

The divided branch should first be reparametrized by the integral linear change

```text
u = (m+n)/3,
v = (2*m-n)/3,
```

which is valid because `3 ∣ m+n` and, modulo `3`, `2*m-n = 2*(m+n)-3*n` is also divisible by `3`. Then

```text
m = u+v,
n = 2*u-v,
m-n = 2*v-u,
```

and `DividedSquareBranch` becomes the denominator-free crossed-square system

```text
0 < u, 0 < v, 0 < 2*u-v, 0 < 2*v-u,
IsCoprime u v,
A^2 = u * (2*v-u),
N^2 = v * (2*u-v),
S = u^2 - u*v + v^2.
```

That crossed-square system is the right next bridge target. It cleanly exposes what the existing `r*s = 3*m^2*n^2` split sees, and what it does **not** see.

## 1. Existing theorem roles that look reusable

Because I could not confirm exact signatures from the repo, the following are **not asserted APIs**. They are the theorem roles suggested by the names and by the standard identity

```text
(m^2+n^2)^2 - (m^4 - m^2*n^2 + n^4) = 3*m^2*n^2.
```

The likely reusable roles are:

1. `pythagoreanQuarticRhs`: expected to be the Eisenstein quartic RHS, morally

```lean
pythagoreanQuarticRhs m n = m^4 - m^2*n^2 + n^4
```

2. `pythagoreanQuarticCenter`: expected to be the Pythagorean center, morally

```lean
pythagoreanQuarticCenter m n = m^2 + n^2
```

3. `pythagorean_quartic_half_factorization_of_opposite_mod`: expected to package a factorization of

```text
(center - b) * (center + b) = 3*m^2*n^2
```

or a half-factor variant when parity forces `center ± b` to be even.

4. `pythagorean_quartic_half_factor_gcd_dvd_three`, `..._gcd_eq_one_or_three`, `..._gcd_eq_one`: expected to prove that the two half factors are coprime except possibly for the controlled factor `3`.

5. `pythagorean_quartic_half_factor_split` and `..._signed_split_of_nonzero`: expected to turn the product/gcd information into square-vs-`3*square` alternatives, with signs/nonzero hypotheses handled.

6. `kubert_cover_pythagorean_half_factors`: likely the highest-level wrapper. It may be directly useful if it returns raw square-factor data or an `EulerSquarePair`-style package from a hypothesis of the form

```lean
b^2 = pythagoreanQuarticRhs m n
```

plus positivity/coprimality/nonzero hypotheses. It is **not** directly usable for `DividedSquareBranch` unless it can be instantiated at `(m,n,b) = (A,N,S)` and returns data in the exact descent interface expected downstream.

## 2. Can `DividedSquareBranch` be transformed into `b^2 = pythagoreanQuarticRhs m n`?

There are two different transformations; only one is likely the existing pythagorean infrastructure.

### 2a. Original Eisenstein quartic: yes, with `(m,n,b) = (A,N,S)`

If `pythagoreanQuarticRhs x y` is the Eisenstein quartic `x^4 - x^2*y^2 + y^4`, then the residual hypothesis

```lean
PositivePrimitiveEisensteinBadUnordered A N S
```

should already imply

```lean
S^2 = pythagoreanQuarticRhs A N
```

independently of the divided branch. This is the input shape for the half-factor infrastructure.

The corresponding half factors are

```text
r = A^2 + N^2 - S,
s = A^2 + N^2 + S,
r*s = 3*A^2*N^2.
```

Under the divided branch, these factors have the following exact forms:

```text
A^2 + N^2 - S = n * (m-n),
3 * (A^2 + N^2 + S) = (m+n) * (2*m-n),
```

and, using `3 ∣ m+n`, equivalently

```text
A^2 + N^2 + S = ((m+n) * (2*m-n)) / 3.
```

So the half-factor infrastructure can recognize the original quartic, but it sees only the product split in `(A,N,S)`. It does not by itself prove the crossed square decomposition of the four branch factors.

### 2b. Branch quartic in the branch parameters: yes, but likely not the same RHS

Multiplying the two divided branch square equations gives

```text
(3*A*N)^2 = n * (m-n) * (m+n) * (2*m-n).
```

This is a quartic in the branch parameters `(m,n)`, but it is not the standard Eisenstein quartic `m^4 - m^2*n^2 + n^4`. It can be written as

```text
n * (m-n) * (m+n) * (2*m-n)
  = (m^2 - m*n + n^2)^2 - (m^2 - 2*m*n)^2.
```

Thus, with `b = 3*A*N` and center `m^2 - m*n + n^2`, the branch equation is a different Pythagorean-style quartic. Existing lemmas named around `pythagoreanQuarticRhs` are reusable here only if that RHS was defined for this four-linear-factor quartic rather than for the Eisenstein quartic. The `r*s = 3*m^2*n^2` clue strongly suggests it was the original Eisenstein quartic, not this branch quartic.

## 3. Is the `r*s = 3*m^2*n^2` split the divided-by-3 sector?

It is the **same upstream identity**, but not the same Lean object as the divided branch.

For the original quartic in variables `(A,N)`:

```text
(A^2+N^2-S) * (A^2+N^2+S) = 3*A^2*N^2.
```

This is the `r*s = 3*m^2*n^2` phenomenon, with variable names `(m,n)` in the old theorem corresponding to `(A,N)` in the WIP residual.

The divided branch is a crossed refinement of this split. Define

```text
u = (m+n)/3,
v = (2*m-n)/3.
```

Then

```text
m = u+v,
n = 2*u-v,
m-n = 2*v-u,
```

and the divided branch equations become

```text
A^2 = u * (2*v-u),
N^2 = v * (2*u-v),
S = u^2 - u*v + v^2.
```

The original half factors become

```text
A^2 + N^2 - S = (2*u-v) * (2*v-u),
A^2 + N^2 + S = 3*u*v.
```

So the existing split sees

```text
r = (2*u-v) * (2*v-u),
s = 3*u*v,
r*s = 3*A^2*N^2,
```

whereas the divided branch square equations are crossed:

```text
A^2 = u * (2*v-u),
N^2 = v * (2*u-v).
```

That is why the half-factor split is not automatically a proof of `DividedSquareBranchUnitOrDescendsStatement`. It reduces the problem if it returns usable raw square-factor data; otherwise, the genuinely new hard part is the crossed-square descent.

## 4. Minimal new bridge theorem statements

These are the bridge statements I would add. They avoid depending on unconfirmed exact signatures of the existing pythagorean theorems, but they are designed to connect to them once the file is visible.

```lean
import Mathlib.Tactic
-- In the actual repo, replace/extend this with:
-- import FLT.Assumptions.MazurProof.RationalPointsN12
-- import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Denominator-free linear reparametrization of the divided branch.

This is the first bridge to prove.  It removes all `/ 3` noise from the divided branch.
The intended witnesses are
`u = (m+n)/3` and `v = (2*m-n)/3`.
-/
def DividedSquareBranchReparamStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
      ∃ u v : ℤ,
        0 < u ∧ 0 < v ∧ 0 < 2*u - v ∧ 0 < 2*v - u ∧
        IsCoprime u v ∧
        m = u + v ∧ n = 2*u - v ∧
        A^2 = u * (2*v - u) ∧
        N^2 = v * (2*u - v) ∧
        S = u^2 - u*v + v^2

/-- Divided branch as a crossed half-factor split for the original Eisenstein quartic.

This is the direct connection to the `r*s = 3*m^2*n^2` infrastructure, after
renaming the old theorem's variables `(m,n)` to the WIP variables `(A,N)`.
-/
def DividedSquareBranchHalfFactorBridgeStatement : Prop :=
  ∀ {A N S u v : ℤ},
    0 < u → 0 < v → 0 < 2*u - v → 0 < 2*v - u →
    A^2 = u * (2*v - u) →
    N^2 = v * (2*u - v) →
    S = u^2 - u*v + v^2 →
      A^2 + N^2 - S = (2*u - v) * (2*v - u) ∧
      A^2 + N^2 + S = 3*u*v ∧
      (A^2 + N^2 - S) * (A^2 + N^2 + S) = 3*A^2*N^2

/-- Adapter from the normalized bad tuple to the pythagorean quartic API.

Use this only if `pythagoreanQuarticRhs` is confirmed to be
`x^4 - x^2*y^2 + y^4`.  The proof should simply unfold the bad tuple's quartic
identity and the RHS definition.
-/
def PositivePrimitiveBadToPythagoreanQuarticStatement : Prop :=
  ∀ {A N S : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
      S^2 = pythagoreanQuarticRhs A N

/-- The real hard bridge: crossed divided square pair gives the divided residual.

This is equivalent in difficulty to the divided branch residual, but much more
Lean-friendly because all divisibility by `3` has been absorbed into `u,v` and all
positivity hypotheses are explicit.
-/
def CrossedDividedSquarePairUnitOrDescendsStatement : Prop :=
  ∀ {A N S u v : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    0 < u → 0 < v → 0 < 2*u - v → 0 < 2*v - u →
    IsCoprime u v →
    A^2 = u * (2*v - u) →
    N^2 = v * (2*u - v) →
    S = u^2 - u*v + v^2 →
      (A = 1 ∧ N = 1 ∧ S = 1) ∨
        ∃ A' N' S' : ℤ,
          NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Small assembly bridge from the reparametrized crossed system back to the current residual. -/
def DividedResidualFromCrossedBridgeStatement : Prop :=
  DividedSquareBranchReparamStatement →
  CrossedDividedSquarePairUnitOrDescendsStatement →
  DividedSquareBranchUnitOrDescendsStatement

end MazurProof.RationalPointsN12
```

### Proof obligations for `DividedSquareBranchReparamStatement`

Unpack

```lean
hdiv : DividedSquareBranch A N S m n
```

and set

```text
u = (m+n)/3,
v = (2*m-n)/3.
```

Obligations:

1. `3 ∣ 2*m-n` from `3 ∣ m+n`:

```text
2*m - n = 2*(m+n) - 3*n.
```

2. `m = u+v` and `n = 2*u-v` by linear algebra over `ℤ` after clearing denominators.

3. Positivity:

```text
0 < m+n      -> 0 < u,
0 < 2*m-n    -> 0 < v,
0 < n        -> 0 < 2*u-v,
0 < m-n      -> 0 < 2*v-u.
```

4. Coprimality:

```text
IsCoprime m n → IsCoprime u v
```

because any common divisor of `u,v` divides `m = u+v` and `n = 2*u-v`.

5. Square equations:

```text
3*A^2 = (m-n)*(m+n) = (2*v-u)*(3*u),
3*N^2 = n*(2*m-n)   = (2*u-v)*(3*v),
```

then cancel the nonzero factor `3`.

6. Center equation:

```text
3*S = m^2 - m*n + n^2
    = 3*(u^2 - u*v + v^2).
```

### Proof obligations for `DividedSquareBranchHalfFactorBridgeStatement`

These are pure `ring_nf` consequences of the crossed system:

```text
A^2 + N^2 - S
= u*(2v-u) + v*(2u-v) - (u^2-uv+v^2)
= (2u-v)*(2v-u),

A^2 + N^2 + S
= u*(2v-u) + v*(2u-v) + (u^2-uv+v^2)
= 3uv.
```

Then multiply the two identities and rewrite with

```text
A^2*N^2 = u*v*(2v-u)*(2u-v).
```

## 5. What this says about reuse

The best route is:

1. Prove `DividedSquareBranchReparamStatement`.
2. Prove `DividedSquareBranchHalfFactorBridgeStatement`.
3. Try to instantiate the existing half-factor split theorem with `(m,n,b) = (A,N,S)`.
4. If the existing split returns raw branch data, add a wrapper from that data to the already-closed raw descent path.
5. If the existing split only returns existential `r,s` with product `3*A^2*N^2`, it is too weak for the divided residual; prove `CrossedDividedSquarePairUnitOrDescendsStatement` directly.

In other words, the half-factor infrastructure can reduce bookkeeping and expose the product split, but the mathematically hardest missing theorem is still the crossed-square descent/unit theorem unless `kubert_cover_pythagorean_half_factors` already proves a no-nontrivial-solution theorem for `S^2 = pythagoreanQuarticRhs A N` in the exact normalized positive primitive setting.

## Suspicious or too-weak current statements

1. Any theorem that returns only

```lean
∃ r s, r*s = 3*m^2*n^2
```

is too weak for this task unless it also returns the definitional equalities tying `r,s` to `center ± b` or to the half factors, plus positivity/sign and gcd information.

2. `pythagorean_quartic_half_factor_gcd_eq_one` may be too specialized if it assumes a parity/mod condition that is not stable under the divided reparametrization. The crossed variables `u,v,2*u-v,2*v-u` need separate parity handling.

3. `kubert_cover_pythagorean_half_factors` is only directly useful if its conclusion is close to either an existing raw branch package, an `EulerSquarePair`, or a contradiction/unit alternative. If it is stated in terms of a cover map or rational-point existence without exposing integer square-factor data, it will need a wrapper theorem.

4. `DividedSquareBranchUnitOrDescendsStatement` has the same orientation risk as the raw residual: it concludes `N' < N`. If final assembly applies it to a swapped branch `DividedSquareBranch N A S m n`, the result is `N' < A`, not `N' < N`. This is fine only if the assembly measure is symmetric, such as `max A N`, or if the caller orients `A ≤ N` before using the residual.

Recommended orientation-safe variant:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Divided residual with descent below a symmetric height. -/
def DividedSquareBranchUnitOrDescendsBelowMaxStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        NormalizedEisensteinBad A' N' S' ∧ N' < max A N

end MazurProof.RationalPointsN12
```

## Bottom line

The next mathematically hardest Lean target for this divided sector is **not** to call the existing pythagorean half-factor split directly. It is to prove the denominator-free crossed-square bridge

```lean
DividedSquareBranchReparamStatement
```

and then the crossed descent/unit theorem

```lean
CrossedDividedSquarePairUnitOrDescendsStatement
```

or to show that `kubert_cover_pythagorean_half_factors` already implies that crossed theorem through a thin wrapper. The decisive algebraic substitutions are

```text
u = (m+n)/3,
v = (2*m-n)/3,
A^2 = u*(2*v-u),
N^2 = v*(2*u-v),
S = u^2-u*v+v^2,
A^2+N^2-S = (2*u-v)*(2*v-u),
A^2+N^2+S = 3*u*v.
```
