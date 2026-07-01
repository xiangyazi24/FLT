# Q2726 (dm-codex1): normalized Eisenstein parametrization route

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Lean project context: `flt-ai`  
Target frontier: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Target statement:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

#check NormalizedBadParamStatement
```

## Connector status

I retried the GitHub connector after the follow-up. The connector can read the repo and can write `scratch/_CHATGPT_DROP_dm-codex1.md`, but the local WIP Lean files named in the prompt are still not visible through the connector:

* `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean` returned `404 Not Found` on `scratch`.
* Code search for `NormalizedBadParamStatement`, `EisensteinTriple`, `EisensteinParam`, and `eisensteinTriple_factor_identity` returned no results.
* The remote `scratch` branch exists and this file is writable.

So I cannot honestly confirm exact theorem signatures from the repo. Below, **existing name references are not confirmed APIs**; the route is the mathematically correct Lean-facing proof design from the definitions and identity in the prompt.

## Executive route

The proof of `NormalizedBadParamStatement` should not factor `A + N` or `A - N`. The correct starting point is the conic/Eisenstein-triple factor identity for

```text
X = A^2,   Y = N^2,   Z = S,
Z^2 = X^2 - X*Y + Y^2.
```

Use the identity, oriented at the `Y` side,

```text
U = 2*Z - (2*X - Y),
V = 2*Z + (2*X - Y),
U*V = 3*Y^2.
```

For the normalized square-side case this is exactly

```text
(2*S - (2*A^2 - N^2)) * (2*S + (2*A^2 - N^2)) = 3*N^4.
```

A primitive positive triple forces a square split of this product in exactly two ways:

```text
raw:      U = 3*r^2,   V = s^2,
divided:  U = r^2,    V = 3*s^2.
```

The raw split gives the ordinary branch after setting

```text
n = r,
2*m - n = s,
m = (r + s)/2.
```

The divided split gives the divided-by-3 branch after setting

```text
n = r,
(2*m - n)/3 = s,
2*m - n = 3*s,
m = (r + 3*s)/2.
```

The same argument with `X` and `Y` swapped gives the two square-side orientations accepted by `NormalizedBadParamStatement`:

```text
EisensteinSqBranch A N S m n,
EisensteinSqBranch N A S m n,
DividedSquareBranch A N S m n,
DividedSquareBranch N A S m n.
```

In fact the `Y`-oriented factor identity alone usually gives either the `(A,N)` raw/divided branch. The swapped disjuncts are still useful because they match symmetric parametrization lemmas and make the target robust.

## 1. Exact parametrization theorem needed

A minimal generic theorem should be stated for a primitive positive Eisenstein triple, then specialized to `X=A^2`, `Y=N^2`, `Z=S`.

Suggested Prop interfaces:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Primitive positive integer solution of `Z^2 = X^2 - X*Y + Y^2`. -/
def PrimitivePositiveEisensteinTriple (X Y Z : ℤ) : Prop :=
  0 < X ∧ 0 < Y ∧ 0 < Z ∧
  IsCoprime X Y ∧
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

/-- Undivided Eisenstein parametrization. -/
def EisensteinRawParam (X Y Z m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  X = (m - n) * (m + n) ∧
  Y = n * (2 * m - n) ∧
  Z = m ^ 2 - m * n + n ^ 2

/-- Divided-by-3 Eisenstein parametrization. -/
def EisensteinDividedParam (X Y Z m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧ (3 : ℤ) ∣ m + n ∧
  3 * X = (m - n) * (m + n) ∧
  3 * Y = n * (2 * m - n) ∧
  3 * Z = m ^ 2 - m * n + n ^ 2
```

The theorem needed is:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Target converse parametrization for primitive positive Eisenstein triples.
The unit branch is included for the full primitive-positive theorem; it is
excluded later by normalized hypotheses such as `A < N` or `A^2 ≠ N^2`. -/
theorem primitivePositiveEisensteinTriple_param_or_unit
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ,
        EisensteinRawParam X Y Z m n ∨
        EisensteinRawParam Y X Z m n ∨
        EisensteinDividedParam X Y Z m n ∨
        EisensteinDividedParam Y X Z m n := by
  sorry
```

For `NormalizedBadParamStatement`, specialize this with

```text
X = A^2,
Y = N^2,
Z = S.
```

The unit branch gives `A^2 = N^2 = 1`; with normalized `0 < A < N`, or with the local `A^2 ≠ N^2` hypothesis, it is impossible. Therefore the remaining disjunction is exactly the target branch disjunction.

A direct square-side wrapper is also reasonable:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Square-side version of the primitive parametrization. This is the closest
mathematical shape to `NormalizedBadParamStatement`. -/
theorem primitivePositiveSquareEisenstein_param_or_unit
    {A N S : ℤ}
    (hA : 0 < A) (hN : 0 < N) (hS : 0 < S)
    (hcop : IsCoprime A N)
    (heq : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ m n : ℤ,
        EisensteinSqBranch A N S m n ∨
        EisensteinSqBranch N A S m n ∨
        DividedSquareBranch A N S m n ∨
        DividedSquareBranch N A S m n := by
  sorry
```

This is the theorem that should feed the final normalized statement.

## 2. Where the raw and divided branches come from

Let

```text
X = A^2,
Y = N^2,
Z = S,
U = 2*Z - (2*X - Y),
V = 2*Z + (2*X - Y).
```

The given identity is

```text
U*V = 3*Y^2.
```

Since `X,Y,Z` are positive and satisfy the triple equation,

```text
(2*Z)^2 - (2*X - Y)^2 = 3*Y^2 > 0,
```

so `U > 0` and `V > 0`.

### Raw split

Suppose

```text
U = 3*r^2,
V = s^2,
0 < r,
0 < s,
2 ∣ r + s,
s > r.
```

Set

```text
n = r,
m = (r + s)/2.
```

Then

```text
2*m - n = s,
m - n = (s - r)/2,
m + n = (s + 3*r)/2.
```

The identities recovered from `U+V=4Z`, `V-U=2*(2X-Y)`, and `Y=r*s` are

```text
Y = n * (2*m - n),
X = (m - n) * (m + n),
Z = m^2 - m*n + n^2.
```

For `X=A^2`, `Y=N^2`, this is exactly

```text
A^2 = (m - n) * (m + n),
N^2 = n * (2*m - n),
S   = m^2 - m*n + n^2.
```

That is `EisensteinSqBranch A N S m n`.

### Divided split

Suppose

```text
U = r^2,
V = 3*s^2,
0 < r,
0 < s,
2 ∣ r + s,
3*s > r.
```

Set

```text
n = r,
m = (r + 3*s)/2.
```

Then

```text
2*m - n = 3*s,
m - n = (3*s - r)/2,
m + n = 3*(r + s)/2.
```

In particular,

```text
3 ∣ m + n.
```

The recovered identities are

```text
3*Y = n * (2*m - n),
3*X = (m - n) * (m + n),
3*Z = m^2 - m*n + n^2.
```

For `X=A^2`, `Y=N^2`, this is exactly

```text
3*A^2 = (m - n) * (m + n),
3*N^2 = n * (2*m - n),
3*S   = m^2 - m*n + n^2,
3 ∣ m+n.
```

That is `DividedSquareBranch A N S m n`.

### Swapped square-side orientation

The equation is symmetric in `X` and `Y`. Applying the same construction to

```text
X' = Y,
Y' = X,
Z' = Z
```

uses the factor identity

```text
(2*Z - (2*Y - X)) * (2*Z + (2*Y - X)) = 3*X^2.
```

This gives the swapped branches:

```text
EisensteinSqBranch N A S m n,
DividedSquareBranch N A S m n.
```

There is also an explicit parameter symmetry. If

```text
RawParam X Y Z m n
```

then

```text
RawParam Y X Z m (m-n)
```

because

```text
m - (m-n) = n,
m + (m-n) = 2*m - n,
(m-n) * (2*m - (m-n)) = (m-n) * (m+n).
```

The divided branch has the same symmetry: if `3 ∣ m+n`, then for `n' = m-n`,

```text
m+n' = 2*m-n = 2*(m+n) - 3*n,
```

so `3 ∣ m+n'` as well, and the divided formulas swap the two sides.

## 3. Gcd, parity, and positivity assumptions needed

The primitive-positive input should be exactly:

```text
0 < X, 0 < Y, 0 < Z,
IsCoprime X Y,
Z^2 = X^2 - X*Y + Y^2.
```

For the normalized square case, use:

```text
X = A^2,
Y = N^2,
Z = S,
0 < A, 0 < N, 0 < S,
IsCoprime A N.
```

Then prove `IsCoprime (A^2) (N^2)` as a small preliminary lemma.

For the factor identity, the necessary local facts are:

```text
U = 2*Z - (2*X - Y),
V = 2*Z + (2*X - Y),
U > 0,
V > 0,
U*V = 3*Y^2,
U+V = 4*Z,
V-U = 2*(2*X-Y).
```

The gcd/valuation facts that make the square split true are:

```text
If an odd prime p ≠ 3 divides both U and V, then p divides X and Y.
If 3 divides both U and V, then 3 divides X and Y.
If 2 divides both U and V, then gcd(U,V) has exactly a factor 4 at 2.
```

Equivalently, for primitive triples:

```text
if Y is odd,  gcd(U,V) = 1,
if Y is even, gcd(U,V) = 4.
```

The `gcd = 4` case is real and must not be thrown away. Example:

```text
X = 5, Y = 8, Z = 7.
U = 2*7 - (2*5 - 8) = 12,
V = 2*7 + (2*5 - 8) = 16,
gcd(U,V) = 4.
```

This triple is primitive and comes from the raw parameters `m=3`, `n=2`.

From `U*V = 3*Y^2` and the primitive gcd facts, every prime exponent in `U` and `V` is even except for the single nonsquare factor `3`, which lies in exactly one of `U,V`. Therefore:

```text
U = 3*r^2, V = s^2
```

or

```text
U = r^2, V = 3*s^2.
```

Parity needed to define `m` is automatic. Since `U` and `V` have the same parity (`U+V=4Z`), the positive square roots `r,s` have the same parity, so

```text
2 ∣ r+s.
```

For raw:

```text
m = (r+s)/2,
n = r.
```

The inequality `n < m` is equivalent to `r < s`, and this follows from `X > 0` because

```text
X = (s-r)*(s+3*r)/4.
```

For divided:

```text
m = (r+3*s)/2,
n = r.
```

The inequality `n < m` is equivalent to `r < 3*s`, and this follows from `X > 0` because

```text
X = (3*s-r)*(s+r)/4.
```

The branch coprimality `IsCoprime m n` follows from primitive `IsCoprime X Y` and the branch formulas. In the raw case, any common divisor of `m,n` divides both

```text
X = (m-n)*(m+n),
Y = n*(2*m-n),
```

so it divides `gcd(X,Y)`. In the divided case, handle the prime `3` separately: if `3 ∣ m` and `3 ∣ n`, then both `X` and `Y` are divisible by `3` because the divided numerators are divisible by `9`, contradicting primitive `IsCoprime X Y`; primes other than `3` are easier because they divide `X` and `Y` directly.

The divided branch condition `3 ∣ m+n` is not an assumption; it is produced by the divided split:

```text
m+n = 3*(r+s)/2.
```

The raw branch condition `3 ∤ m+n` is not needed for `EisensteinSqBranch`, but for a primitive raw triple it follows automatically: if `3 ∣ m+n`, then `X`, `Y`, and `Z` are all divisible by `3`.

## 4. What may already exist in the repo

I could not confirm the file or symbols through the connector. Based on the names in the prompt:

* `EisensteinTriple` probably packages `Z^2 = X^2 - X*Y + Y^2`, possibly with positivity or primitiveness.
* `EisensteinParam` probably packages the raw parametrization
  `X = m^2-n^2`, `Y = 2*m*n-n^2`, `Z = m^2-m*n+n^2`.
* `eisensteinParam_triple` likely proves the forward direction: parameters produce a triple.
* `eisensteinTriple_factor_identity` is the key starting lemma:
  `(2*Z - (2*X-Y))*(2*Z + (2*X-Y)) = 3*Y^2`.

If the local WIP already has a theorem like one of these, it is essentially the missing theorem:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

-- Possible existing/target shape, not confirmed from the connected repo.
theorem positivePrimitiveEisensteinTriple_param_or_unit
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ,
        EisensteinRawParam X Y Z m n ∨
        EisensteinRawParam Y X Z m n ∨
        EisensteinDividedParam X Y Z m n ∨
        EisensteinDividedParam Y X Z m n := by
  sorry
```

If only `eisensteinParam_triple` exists, it is the wrong direction for this frontier. The frontier needs the converse parametrization plus square-side specialization.

If only a raw converse exists, it is too weak. The primitive triple

```text
X = 8, Y = 3, Z = 7
```

satisfies

```text
7^2 = 8^2 - 8*3 + 3^2,
IsCoprime 8 3,
```

and is not raw. It is the divided case from `m=5`, `n=1`:

```text
3*8 = (5-1)*(5+1),
3*3 = 1*(2*5-1),
3*7 = 5^2 - 5*1 + 1^2,
3 ∣ 5+1.
```

If a half-factor theorem assumes `gcd(U,V)=1`, it is false for even `Y`; the example `(X,Y,Z)=(5,8,7)` has `gcd(U,V)=4`.

## 5. Lean implementation DAG

### Layer 0: primitive-square boilerplate

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- `IsCoprime A N` lifts to the square sides. -/
theorem IsCoprime.sq_sq_int {A N : ℤ}
    (h : IsCoprime A N) : IsCoprime (A ^ 2) (N ^ 2) := by
  sorry

/-- Normalized bad data gives a primitive positive Eisenstein triple on
`X=A^2`, `Y=N^2`, `Z=S`. -/
theorem NormalizedEisensteinBad.to_primitiveTriple
    {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    PrimitivePositiveEisensteinTriple (A ^ 2) (N ^ 2) S := by
  sorry
```

### Layer 1: factor identity and positivity

Use the existing `eisensteinTriple_factor_identity` if available. Add generic wrappers:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- The two half factors are positive. -/
theorem eisensteinTriple_halfFactors_pos
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    0 < 2 * Z - (2 * X - Y) ∧
    0 < 2 * Z + (2 * X - Y) := by
  sorry

/-- Product identity, oriented at the `Y` side. Use the existing
`eisensteinTriple_factor_identity` here if it has this shape. -/
theorem eisensteinTriple_halfFactors_mul
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y)) = 3 * Y ^ 2 := by
  sorry
```

### Layer 2: gcd and square split

This is the arithmetic heart. Keep it independent of `A,N,S`.

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Common divisors of the half factors are only the harmless `2`-adic part;
the possible common `3` is excluded by primitiveness. -/
theorem eisensteinTriple_halfFactors_gcd_eq_one_or_four
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    Nat.gcd
      (Int.natAbs (2 * Z - (2 * X - Y)))
      (Int.natAbs (2 * Z + (2 * X - Y))) = 1 ∨
    Nat.gcd
      (Int.natAbs (2 * Z - (2 * X - Y)))
      (Int.natAbs (2 * Z + (2 * X - Y))) = 4 := by
  sorry

/-- Square split of `U*V = 3*Y^2` under the primitive half-factor gcd facts. -/
theorem eisensteinTriple_halfFactors_square_split
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ (2 : ℤ) ∣ r + s ∧
      ((2 * Z - (2 * X - Y) = 3 * r ^ 2 ∧
        2 * Z + (2 * X - Y) = s ^ 2 ∧
        Y = r * s ∧
        r < s) ∨
       (2 * Z - (2 * X - Y) = r ^ 2 ∧
        2 * Z + (2 * X - Y) = 3 * s ^ 2 ∧
        Y = r * s ∧
        r < 3 * s)) := by
  sorry
```

Notes for this layer:

* Work in `Nat` valuations if the project has stronger support there.
* Convert back to `ℤ` only after obtaining positive square roots.
* Do not state `gcd = 1` alone; `gcd = 4` is necessary.

### Layer 3: construct raw/divided parameters from the split

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Raw square split gives raw Eisenstein parameters. -/
theorem rawParam_of_halfFactors_rawSplit
    {X Y Z r s : ℤ}
    (hr : 0 < r) (hs : 0 < s)
    (hpar : (2 : ℤ) ∣ r + s)
    (hrs : r < s)
    (hU : 2 * Z - (2 * X - Y) = 3 * r ^ 2)
    (hV : 2 * Z + (2 * X - Y) = s ^ 2)
    (hY : Y = r * s)
    (hprim : IsCoprime X Y) :
    ∃ m n : ℤ, EisensteinRawParam X Y Z m n := by
  -- set `n = r`, `m = (r+s)/2`
  sorry

/-- Divided square split gives divided Eisenstein parameters. -/
theorem dividedParam_of_halfFactors_dividedSplit
    {X Y Z r s : ℤ}
    (hr : 0 < r) (hs : 0 < s)
    (hpar : (2 : ℤ) ∣ r + s)
    (hrs : r < 3 * s)
    (hU : 2 * Z - (2 * X - Y) = r ^ 2)
    (hV : 2 * Z + (2 * X - Y) = 3 * s ^ 2)
    (hY : Y = r * s)
    (hprim : IsCoprime X Y) :
    ∃ m n : ℤ, EisensteinDividedParam X Y Z m n := by
  -- set `n = r`, `m = (r+3*s)/2`
  sorry
```

### Layer 4: generic primitive parametrization

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Generic primitive-positive parametrization. -/
theorem primitivePositiveEisensteinTriple_param_or_unit
    {X Y Z : ℤ}
    (h : PrimitivePositiveEisensteinTriple X Y Z) :
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ,
        EisensteinRawParam X Y Z m n ∨
        EisensteinRawParam Y X Z m n ∨
        EisensteinDividedParam X Y Z m n ∨
        EisensteinDividedParam Y X Z m n := by
  -- Apply `eisensteinTriple_halfFactors_square_split h`.
  -- Convert raw split to `EisensteinRawParam X Y Z`.
  -- Convert divided split to `EisensteinDividedParam X Y Z`.
  -- Swapped disjuncts are optional here; they can be filled by symmetry or left unused.
  sorry
```

The unit branch can be proven separately as a degenerate lemma if the square split lands in `r=s=1` and `X=Y`, or simply included as a convenient disjunct in a stronger theorem. In the normalized target it is impossible.

### Layer 5: square-side wrapper matching existing branch definitions

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Translate generic raw parameters on square sides into the local raw branch. -/
theorem rawParam_sqSides_iff_branch
    {A N S m n : ℤ} :
    EisensteinRawParam (A ^ 2) (N ^ 2) S m n ↔
      EisensteinSqBranch A N S m n := by
  sorry

/-- Translate generic divided parameters on square sides into the local divided branch. -/
theorem dividedParam_sqSides_iff_branch
    {A N S m n : ℤ} :
    EisensteinDividedParam (A ^ 2) (N ^ 2) S m n ↔
      DividedSquareBranch A N S m n := by
  sorry
```

### Layer 6: final normalized statement

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Final frontier: normalized bad square-side triple has one of the four
accepted square branches. -/
theorem normalizedBadParamStatement_checked :
    NormalizedBadParamStatement := by
  intro A N S hbad
  have htri : PrimitivePositiveEisensteinTriple (A ^ 2) (N ^ 2) S :=
    NormalizedEisensteinBad.to_primitiveTriple hbad
  rcases primitivePositiveEisensteinTriple_param_or_unit htri with hunit | hparam
  · -- Contradict normalized `A < N` or `A^2 ≠ N^2`.
    -- From `hunit`, get `A = 1` and `N = 1`, hence contradiction.
    exfalso
    sorry
  · rcases hparam with ⟨m, n, hcases⟩
    refine ⟨m, n, ?_⟩
    -- Convert each generic `RawParam`/`DividedParam` disjunct to the local
    -- `EisensteinSqBranch`/`DividedSquareBranch` disjunct.
    sorry
```

## 6. Common false shortcuts to avoid

1. **Do not use `A+N` or `A-N` product shortcuts.** The factor identity controls

```text
2*S ± (2*A^2 - N^2),
```

not `A ± N`.

2. **Do not drop the divided branch.** The primitive triple `(8,3,7)` is divided, not raw.

3. **Do not assert `gcd(U,V)=1`.** The even primitive triple `(5,8,7)` gives `gcd(U,V)=4`.

4. **Do not assume the swapped orientation is mathematically different.** It is the same conic parametrization under `n ↦ m-n`, but including both orientations makes the final statement match the downstream branch closures.

5. **Do not make the unit branch disappear silently.** For the full primitive-positive theorem, `(1,1,1)` is real. For normalized `0<A<N`, it is excluded and should be discharged explicitly.

## 7. Minimal final theorem set

The smallest Lean-checkable set that should unlock `NormalizedBadParamStatement` is:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

#check eisensteinTriple_factor_identity

-- New/target lemmas:
#check IsCoprime.sq_sq_int
#check NormalizedEisensteinBad.to_primitiveTriple
#check eisensteinTriple_halfFactors_pos
#check eisensteinTriple_halfFactors_gcd_eq_one_or_four
#check eisensteinTriple_halfFactors_square_split
#check rawParam_of_halfFactors_rawSplit
#check dividedParam_of_halfFactors_dividedSplit
#check primitivePositiveEisensteinTriple_param_or_unit
#check rawParam_sqSides_iff_branch
#check dividedParam_sqSides_iff_branch
#check normalizedBadParamStatement_checked
```

If local WIP already has `EisensteinTriple`/`EisensteinParam`, reuse those names rather than introducing duplicates. The key missing theorem is the **converse primitive parametrization with both raw and divided cases**; `eisensteinParam_triple` alone is only the forward direction and will not prove the frontier.
