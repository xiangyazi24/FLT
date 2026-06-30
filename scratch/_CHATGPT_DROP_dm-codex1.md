# Q2721 (dm-codex1): RationalPointsN12 half-factor audit for the divided-by-3 branch

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target file requested for inspection: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`  
Local WIP frontier from prompt: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`

## Connector status and scope of this audit

I attempted to inspect the requested file through the GitHub connector.

Confirmed connector facts:

* `README.md`, `FLT.lean`, and `FLT/Assumptions/Mazur.lean` are readable on the connected repo default branch.
* `FLT/Assumptions/MazurProof/RationalPointsN12.lean` returned `404 Not Found` on `main`.
* The same path returned `404 Not Found` on `scratch`.
* Connector code search for the listed symbols returned no results.
* The remote `scratch` branch exists and `scratch/_CHATGPT_DROP_dm-codex1.md` is writable.

Therefore I cannot honestly quote exact existing theorem statements from `RationalPointsN12.lean`. In the sections below, anything labelled **confirmed** is derived from the definitions in the prompt and elementary algebra. Anything labelled **target** is a Lean-facing bridge statement that should be checked against the local WIP file once that file is available in the branch. I do not claim those target statements are existing APIs.

## Executive answer

The divided branch does **not** directly provide a hypothesis of the form

```text
b^2 = pythagoreanQuarticRhs m n
```

for the original branch variables `m n`. Its native algebra is instead

```text
3*A^2 = (m-n)*(m+n),
3*N^2 = n*(2*m-n),
3*S   = m^2 - m*n + n^2.
```

The forced factor `3` goes into `m+n` in the first product and into `2*m-n` in the second product. After the honest parity split, two cases die mod `4`; the sole survivor is

```text
m - n   = a^2,
m + n   = 3*b^2,
n       = c^2,
2*m - n = 3*d^2,
```

and this is exactly four positive squares in arithmetic progression:

```text
c^2, b^2, d^2, a^2.
```

So the reusable mathematical object is not a raw-branch `EulerSquarePair` immediately. It is a `NoNonconstantFourSquaresAP` residual, or a bridge from four-square AP to whatever `RationalPointsN12.lean` proves via the pythagorean/Ljunggren quartic.

If the existing `RationalPointsN12.lean` half-factor infrastructure ultimately proves the standard no-nonconstant-four-squares-in-AP obstruction, then it is useful. But it is one bridge away: the variables in the `pythagoreanQuarticRhs` theorem would be new parameters obtained from the four-square AP, not the original divided-branch `m n`.

## 1. Existing theorem inventory: what can and cannot be confirmed

Because the requested file is not visible through the connector, I cannot confirm exact statement shapes for these names:

```text
pythagoreanQuarticRhs
pythagoreanQuarticCenter
pythagorean_quartic_half_factorization_of_opposite_mod
pythagorean_quartic_half_factor_gcd_dvd_three
pythagorean_quartic_half_factor_gcd_eq_one_or_three
pythagorean_quartic_half_factor_gcd_eq_one
pythagorean_quartic_half_factor_split
pythagorean_quartic_half_factor_signed_split_of_nonzero
kubert_cover_pythagorean_half_factors
```

The names strongly suggest the usual half-factor route for a pythagorean/Ljunggren quartic: from a square value of a quartic, introduce a center, factor a difference of squares, prove the half-factor gcd is `1` or `3`, then split the two factors into square packages. A typical mathematical shape is

```text
B^2 = pythagoreanQuarticRhs u v
```

plus primitive/opposite-parity/nonzero hypotheses, leading to half factors `r s` with a product such as

```text
r * s = 3 * u^2 * v^2.
```

That is a **target role**, not a confirmed API. The directly reusable theorem, if present, would be whichever existing result exposes the conclusion as one of the following:

```text
No nonconstant four integer squares are in arithmetic progression.
```

or

```text
Every primitive pythagorean-quartic square solution is the unit/degenerate one.
```

A theorem that only starts from `B^2 = pythagoreanQuarticRhs u v` is not directly reusable until a new bridge constructs such `u v B` from the divided branch's middle parity package.

## 2. Confirmed algebra from `DividedSquareBranch`

From the prompt:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

-- Prompt-local definition, repeated here only for reference.
def DividedSquareBranch_ref (A N S m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧ (3 : ℤ) ∣ m + n ∧
  3 * A ^ 2 = (m - n) * (m + n) ∧
  3 * N ^ 2 = n * (2 * m - n) ∧
  3 * S = m ^ 2 - m * n + n ^ 2
```

Write

```text
x = m - n,
y = m + n,
z = n,
w = 2*m - n.
```

From `0 < n` and `n < m`, all four are positive. From `IsCoprime m n`:

```text
gcd(x,z) = 1,
gcd(y,z) = 1,
gcd(x,w) = 1,
gcd(x,y) ∣ 2,
gcd(z,w) = gcd(n,2).
```

The `3`-adic facts forced by `3 ∣ m+n` and `IsCoprime m n` are:

```text
3 ∤ n,
3 ∤ m,
3 ∤ (m-n),
3 ∣ (m+n),
3 ∣ (2*m-n).
```

The tempting statement `3 ∤ (2*m-n)` is false. In fact the opposite is forced, because

```text
2*m - n = 2*(m+n) - 3*n.
```

The cross-gcd is exact:

```text
gcd(m+n, 2*m-n) = 3.
```

Reason: a common divisor of `m+n` and `2*m-n` divides

```text
(m+n) + (2*m-n) = 3*m,
2*(m+n) - (2*m-n) = 3*n,
```

and any prime other than `3` would divide both `m` and `n`. Since both factors are divisible by `3`, the gcd is exactly `3`.

The square equations refine the location of the nonsquare `3`:

```text
v_3(m+n)    = 1 + 2*v_3(A),
v_3(2*m-n) = 1 + 2*v_3(N),
min(v_3(m+n), v_3(2*m-n)) = 1.
```

So the nonsquare `3` in `3*A^2` goes to `m+n`, and the nonsquare `3` in `3*N^2` goes to `2*m-n`. Extra powers of `3` may occur, but only as square powers beyond the first.

A small counterexample to the false shortcut `3 ∤ (2*m-n)` is the unit branch:

```text
m = 2, n = 1, A = 1, N = 1, S = 1.
```

Then

```text
3 ∣ m+n = 3,
3 ∣ 2*m-n = 3,
3 ∤ m-n = 1,
3*A^2 = 1*3,
3*N^2 = 1*3,
3*S   = 4 - 2 + 1 = 3.
```

This unit is excluded by `PositivePrimitiveEisensteinBadUnordered` because that hypothesis contains `A^2 ≠ N^2`, but it is exactly the explicit unit exception in `DividedSquareBranchUnitOrDescendsStatement`.

## 3. Can the branch become `b^2 = pythagoreanQuarticRhs m n`?

### Directly, with the original `m n`: no confirmed route

The branch gives the Eisenstein-center identity

```text
(m^2 - m*n + n^2)^2
  = (m^2 - n^2)^2
    - (m^2 - n^2)*(2*m*n - n^2)
    + (2*m*n - n^2)^2.
```

Using

```text
m^2 - n^2     = 3*A^2,
2*m*n - n^2   = 3*N^2,
m^2 - m*n+n^2 = 3*S,
```

this becomes the already-known Eisenstein quartic

```text
S^2 = A^4 - A^2*N^2 + N^4.
```

That is not a pythagorean/Ljunggren quartic square in the original `m n`. In particular, the branch supplies square factorizations of two linear products; it does not supply a new `B` with

```text
B^2 = pythagoreanQuarticRhs m n.
```

### Denominator-free normalization: useful but not raw and not Kubert directly

Since `3 ∣ m+n` and `3 ∣ 2*m-n`, introduce `p q` by

```text
m+n     = 3*p,
2*m - n = 3*q.
```

Then exactly

```text
m     = p + q,
n     = 2*p - q,
m - n = 2*q - p,
S     = p^2 - p*q + q^2,
A^2   = p * (2*q - p),
N^2   = q * (2*p - q).
```

This is often the cleanest Lean bridge because it removes literal division by `3`. But it is still not the raw branch. The raw branch has factors like

```text
A^2 = (M-N)*(M+N),
N^2 = N*(2*M-N),
```

whereas the reduced divided branch has the crossed form

```text
A^2 = p*(2*q-p),
N^2 = q*(2*p-q).
```

No linear renaming of `p q` turns both equations into the raw branch with the same positivity hypotheses.

## 4. Which split is the divided-by-3 sector?

The honest factorization of the divided branch has three parity sectors.

### Sector E: `m` odd, `n` even

```text
m - n     = a^2,
m + n     = 3*b^2,
n         = 2*c^2,
2*m - n   = 6*d^2,
A         = a*b,
N         = 2*c*d.
```

The identities are

```text
a^2 + c^2 = 3*d^2,
b^2       = c^2 + d^2.
```

This sector is impossible mod `4`: `a` is odd, so `a^2+c^2` is `1` or `2` mod `4`, while `3*d^2` is `0` or `3` mod `4`.

### Sector M: `m` even, `n` odd — the real residual

```text
m - n     = a^2,
m + n     = 3*b^2,
n         = c^2,
2*m - n   = 3*d^2,
A         = a*b,
N         = c*d.
```

The identities are

```text
a^2 + 2*c^2 = 3*b^2,
2*a^2 + c^2 = 3*d^2.
```

Equivalently,

```text
c^2, b^2, d^2, a^2
```

are four squares in arithmetic progression:

```text
b^2 - c^2 = d^2 - b^2,
d^2 - b^2 = a^2 - d^2.
```

This is the sector that should be connected to `RationalPointsN12.lean` if that file proves a pythagorean/Ljunggren quartic obstruction.

### Sector O: `m` odd, `n` odd

```text
m - n     = 2*a^2,
m + n     = 6*b^2,
n         = c^2,
2*m - n   = 3*d^2,
A         = 2*a*b,
N         = c*d.
```

The identities are

```text
a^2 + c^2 = 3*b^2,
a^2 + b^2 = d^2.
```

This sector is impossible mod `4`: `c` is odd, so `a^2+c^2` is `1` or `2` mod `4`, while `3*b^2` is `0` or `3` mod `4`.

### Relation to the `r*s = 3*m^2*n^2` split

The split

```text
r * s = 3 * m^2 * n^2
```

is not the same as the original divided-branch allocation of the prime `3`. In the divided branch, the first-order allocation is

```text
3 goes into m+n,
3 goes into 2*m-n.
```

The `r*s = 3*m^2*n^2` half-factor split is the standard difference-of-squares split attached to a pythagorean/Ljunggren quartic. It becomes relevant only after the middle sector has been converted to four squares in AP and then parametrized into the quartic variables used by `RationalPointsN12.lean`.

So the answer is:

* Same prime and same classical obstruction at the residual level.
* Different variables and different first algebraic step.
* A bridge theorem is needed; do not feed the original divided-branch `m n` directly to `pythagoreanQuarticRhs` or `kubert_cover_*` unless the local file has an explicitly matching theorem.

## 5. Minimal new bridge statements

These are target statements. Place them in the namespace where the local `DividedSquareBranch` and `PositivePrimitiveEisensteinBadUnordered` live. The imports assume the local WIP file exists.

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
-- If available on the local WIP branch, also import:
-- import FLT.Assumptions.MazurProof.RationalPointsN12

/-- Four integer squares in arithmetic progression, written without division. -/
def FourSquaresAP (r s t u : ℤ) : Prop :=
  s ^ 2 - r ^ 2 = t ^ 2 - s ^ 2 ∧
  t ^ 2 - s ^ 2 = u ^ 2 - t ^ 2

/-- The residual theorem needed after the divided-branch split. -/
def NoNonconstantFourSquaresAP : Prop :=
  ∀ {r s t u : ℤ},
    0 < r → 0 < s → 0 < t → 0 < u →
    FourSquaresAP r s t u →
    r = s ∧ s = t ∧ t = u

/-- Denominator-free form of the divided branch after setting
`m+n = 3*p` and `2*m-n = 3*q`. -/
def DividedReducedBranch (A N S p q : ℤ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < 2 * q - p ∧ 0 < 2 * p - q ∧
  IsCoprime p q ∧
  A ^ 2 = p * (2 * q - p) ∧
  N ^ 2 = q * (2 * p - q) ∧
  S = p ^ 2 - p * q + q ^ 2

/-- Middle parity square package for the divided branch. -/
def DividedMiddlePackage (A N S m n a b c d : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
  m - n = a ^ 2 ∧
  m + n = 3 * b ^ 2 ∧
  n = c ^ 2 ∧
  2 * m - n = 3 * d ^ 2 ∧
  A = a * b ∧
  N = c * d ∧
  3 * S = m ^ 2 - m * n + n ^ 2
```

Core bridge targets:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
-- import FLT.Assumptions.MazurProof.RationalPointsN12

/-- Extract the denominator-free reduced branch. -/
theorem dividedSquareBranch_to_reduced
    {A N S m n : ℤ}
    (hpos : PositivePrimitiveEisensteinBadUnordered A N S)
    (hbr : DividedSquareBranch A N S m n) :
    ∃ p q : ℤ,
      m + n = 3 * p ∧
      2 * m - n = 3 * q ∧
      m = p + q ∧
      n = 2 * p - q ∧
      DividedReducedBranch A N S p q := by
  sorry

/-- The two non-middle parity sectors are contradictory by mod `4`; the
middle sector yields a four-square AP package. -/
theorem dividedSquareBranch_middlePackage_or_contradiction
    {A N S m n : ℤ}
    (hpos : PositivePrimitiveEisensteinBadUnordered A N S)
    (hbr : DividedSquareBranch A N S m n) :
    ∃ a b c d : ℤ,
      DividedMiddlePackage A N S m n a b c d ∧
      FourSquaresAP c b d a := by
  sorry

/-- The middle package is constant if no four nonconstant positive squares are
in arithmetic progression. -/
theorem dividedMiddlePackage_unit_of_noFourSquaresAP
    (hAP : NoNonconstantFourSquaresAP)
    {A N S m n a b c d : ℤ}
    (hpos : PositivePrimitiveEisensteinBadUnordered A N S)
    (hpkg : DividedMiddlePackage A N S m n a b c d)
    (hap : FourSquaresAP c b d a) :
    A = 1 ∧ N = 1 ∧ S = 1 := by
  sorry

/-- Final divided branch close, using the AP obstruction rather than a new
descent object. -/
theorem dividedSquareBranch_unit_of_noFourSquaresAP
    (hAP : NoNonconstantFourSquaresAP)
    {A N S m n : ℤ}
    (hpos : PositivePrimitiveEisensteinBadUnordered A N S)
    (hbr : DividedSquareBranch A N S m n) :
    A = 1 ∧ N = 1 ∧ S = 1 := by
  sorry

/-- Immediate wrapper for the WIP statement. This proves the left disjunct;
it does not need to construct a new descent triple. -/
theorem dividedSquareBranchUnitOrDescends_of_noFourSquaresAP
    (hAP : NoNonconstantFourSquaresAP) :
    DividedSquareBranchUnitOrDescendsStatement := by
  intro A N S m n hpos hbr
  exact Or.inl (dividedSquareBranch_unit_of_noFourSquaresAP hAP hpos hbr)
```

If the local `RationalPointsN12.lean` has a theorem that closes the pythagorean/Ljunggren quartic, add this bridge rather than trying to rewrite the original divided branch into that theorem:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.RationalPointsN12

/-- Target bridge: expose the pythagorean-quartic/Kubert work as the exact AP
obstruction needed by the divided branch. Fill in the proof using the actual
local theorem names and hypotheses from `RationalPointsN12.lean`. -/
theorem noNonconstantFourSquaresAP_of_kubertPythagoreanHalfFactors :
    NoNonconstantFourSquaresAP := by
  sorry
```

If the existing endpoint is instead phrased as an `EulerSquarePair` descent, use this bridge shape:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
-- import the file that defines `EulerSquarePair` and its descent theorem

/-- Target bridge from the AP residual to the already checked Euler descent.
Use the actual local `EulerSquarePair` fields; this shape deliberately avoids
any false `A±N` shortcut. -/
theorem fourSquaresAP_constant_or_eulerSquarePair
    {c b d a : ℤ}
    (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) (ha : 0 < a)
    (hap : FourSquaresAP c b d a) :
    (c = b ∧ b = d ∧ d = a) ∨
      ∃ P Q, EulerSquarePair P Q := by
  sorry
```

The key implementation detail is that the signs of `A` and `N` are not determined by the square equations alone. Use `PositivePrimitiveEisensteinBadUnordered` to get `0 < A` and `0 < N` before concluding `A = a*b` and `N = c*d`. Without positivity, the unit branch also permits `A = -1` or `N = -1` at the level of `DividedSquareBranch` alone.

## 6. Suspicious or too-weak points to check in `RationalPointsN12.lean`

Since I could not fetch the file, these are audit checks rather than accusations.

1. **Repository visibility is stale.** The requested file is absent from both `main` and `scratch` through the connector. Before relying on these theorem names in CI, push the local WIP branch containing `RationalPointsN12.lean` or merge it into the working branch.

2. **`gcd_eq_one` may be too specialized.** A half-factor proof that first shows `gcd = 1 ∨ gcd = 3` and then has a theorem named `gcd_eq_one` needs careful hypothesis checking. The divided branch has a forced common factor `3` between the original factors `m+n` and `2*m-n`. If a bridge to the quartic lands in the `gcd = 3` case, a theorem that only exposes `gcd = 1` will be too weak or inapplicable.

3. **`signed_split_of_nonzero` may not provide positivity.** For the divided branch, the final unit proof needs positive square roots so that `A = a*b` and `N = c*d`, not merely `A^2 = (a*b)^2`. If the existing split is signed, add a normalization lemma using `0 < A`, `0 < N`, and positivity of the linear factors.

4. **`kubert_cover_pythagorean_half_factors` may be too monolithic.** If it proves only a final rational-points statement, expose a small corollary with the exact shape `NoNonconstantFourSquaresAP`. That is the minimal reusable interface for the divided branch.

5. **Avoid original-variable reuse.** Any theorem requiring `B^2 = pythagoreanQuarticRhs m n` should not be fed the original divided-branch `m n` unless the local file contains a proved lemma doing exactly that. The honest bridge changes variables via the middle square package/four-square AP.

## 7. Recommended Lean route

Use the following route, in this order:

```text
DividedSquareBranch
  → prove 3 ∤ n, 3 ∤ m, 3 ∤ (m-n), 3 ∣ (2*m-n), gcd(m+n,2*m-n)=3
  → introduce p,q with m+n=3p and 2m-n=3q
  → get A^2=p*(2q-p), N^2=q*(2p-q), S=p^2-pq+q^2
  → split by parity
  → mod-4 contradiction for m odd/n even
  → mod-4 contradiction for m odd/n odd
  → middle package m even/n odd
  → obtain c^2,b^2,d^2,a^2 in AP
  → apply `NoNonconstantFourSquaresAP`
  → constant AP
  → coprimality forces a=b=c=d=1
  → m=2, n=1, A=1, N=1, S=1
  → `Or.inl` for `DividedSquareBranchUnitOrDescendsStatement`
```

This route is Lean-friendly because each step is local and checkable: integer divisibility/gcd lemmas, parity cases, two small mod-4 contradictions, one exposed AP obstruction, and final unit normalization. It avoids the false shortcuts through `A+N` or `A-N` and does not pretend that the divided branch is the raw branch under rescaling.
