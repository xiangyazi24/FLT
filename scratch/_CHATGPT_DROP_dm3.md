# Q1955 (dm2): rational-point files for N=12, N=14, N=16

## Caveat about the requested file

I could not fetch

```text
FLT/Assumptions/MazurProof/RationalPointsC20.lean
```

from branch `ai-scratch`: the GitHub connector returned `Not Found`.  The directory

```text
FLT/Assumptions/MazurProof
```

exists on `ai-scratch`, and the branch compare shows related files such as

```text
FLT/Assumptions/MazurProof/DescentBridgeN12.lean
FLT/Assumptions/MazurProof/DescentBridgeN14.lean
FLT/Assumptions/MazurProof/DescentBridgeN16.lean
scratch/Descent20a4.lean
scratch/DenominatorQuartic.lean
scratch/DescentN14.lean
scratch/DescentN16.lean
```

but not `RationalPointsC20.lean`.  So the answer below is based on the method you described, plus the available C20/N10, N14, and N16 scratch files.

## Executive summary

The C20/N10 proof architecture does generalize, but not uniformly as a single copy-paste file.

The shared skeleton is:

1. normalize a rational point as

   ```text
   u = X / Z^2,
   w = Y / Z^3,
   Z > 0,
   gcd X Z = 1;
   ```

2. clear denominators to an integral homogeneous equation;
3. split off coprime factors of a square;
4. reduce nonintegral denominator cases to one or more binary quartics;
5. rule out those quartics by descent or a squeeze/local obstruction;
6. reduce to integer `u`;
7. finish by the integer-point lemma for the curve.

The curve-specific parts are the factorization of the cleared homogeneous equation and the resulting binary quartics.  In particular:

```text
N=10 / C20:  Y^2 = X * (X^2 + X Z^2 - Z^4)
N=12:        Y^2 = (X - Z^2) * (X - 2 Z^2) * (X + 2 Z^2)
N=14:        Y^2 = X * (X^2 + X Z^2 - 2 Z^4)
N=16:        Y^2 = X * (X^2 - X Z^2 - Z^4)
```

N10 and N16 are the cleanest pair: they are the same denominator-descent family with the sign of the middle term changed.

N14 is still close to N10, but the gcd of the two factors can be `2`, so the proof splits into odd/even numerator cases.

N12 is different: its cubic has three rational roots, and the direct denominator equation is a triple product.  For the Kubert square obstruction, the cleaner quartic is the 2-cover

```text
Q12(X,Z,Y):  Y^2 = (X^2 + Z^2) * (3 X^2 - Z^2)
            = 3 X^4 + 2 X^2 Z^2 - Z^4.
```

Also: the current `DescentBridgeN12.lean` degenerate set

```lean
u = -2 ∨ u = 1 ∨ u = 2
```

is too small if it is meant to describe **all** rational points on

```text
w^2 = u^3 - u^2 - 4u + 4.
```

That curve also has rational affine points at

```text
u = 0, 4.
```

The correct all-rational-`u` conclusion is at least

```lean
u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4
```

with `u = -2,1,2` the three 2-torsion roots and `u = 0,4` the extra non-2-torsion x-coordinates.  If the Kubert obstruction only sees the cover `u = 3*t^2+1`, then the downstream finite check should be stated on the cover, not as “all points have u in {-2,1,2}”.

---

## 1. Steps that generalize to all four curves

### A. Rational denominator normalization

For every curve in this family, the equation is integral Weierstrass of the form

```text
w^2 = cubic(u),
```

so a rational point can be normalized as

```text
u = X / Z^2,
w = Y / Z^3,
Z > 0,
gcd X Z = 1.
```

This step should be factored into a common helper file, e.g.

```text
RationalPointNormalization.lean
```

or inside a shared namespace in the Mazur proof directory.  The output should be a structure containing `X Y Z`, positivity of `Z`, coprimality, and the cleared denominator equation.

### B. Cleared denominator equation

After normalization, each curve has an integral equation

```text
Y^2 = homogeneous_cubic(X,Z).
```

The proof of this is always `ring_nf`/`nlinarith` after substituting `u = X/Z^2`, `w = Y/Z^3`.

### C. Coprime factorization of a square

The common lemma shape is:

```lean
import Mathlib

namespace MazurProof.Common

/-- Schematic: if two coprime integer factors multiply to a square,
then each is a signed square.  In project code you can use the existing
`Int.sq_of_isCoprime` API directly. -/
example {a b y : ℤ} (hcop : IsCoprime a b) (h : a * b = y ^ 2) :
    ∃ r : ℤ, a = r ^ 2 ∨ a = -r ^ 2 := by
  exact Int.sq_of_isCoprime hcop h

end MazurProof.Common
```

This is exactly the pattern used in the available scratch files for N10, N14, and N16.

### D. The descent wrapper

The denominator contradiction should remain a common strong-induction wrapper:

```lean
import Mathlib

namespace MazurProof.Common

/-- Schematic denominator descent package.  Instantiate `BadQuartic` separately
for N10, N12, N14, N16. -/
axiom descent_step_for_quartic
    (BadQuartic : ℤ → ℤ → ℤ → Prop)
    (x z y : ℤ)
    (hz : 2 ≤ z)
    (hcop : Int.gcd x z = 1)
    (h : BadQuartic x z y) :
    ∃ x' z' y' : ℤ,
      2 ≤ z' ∧
      Int.gcd x' z' = 1 ∧
      BadQuartic x' z' y' ∧
      z'.natAbs < z.natAbs

end MazurProof.Common
```

In actual files, do **not** leave this as one axiom.  The point is architectural: put the strong induction once, and prove separate `descent_step` lemmas for the specific quartics.

### E. Integer endpoint

Once `Z = 1`, every file reduces to an integer theorem:

```text
N10: w^2 = u^3 + u^2 - u       -> u ∈ {-1,0,1}
N12: w^2 = u^3 - u^2 - 4u + 4  -> u ∈ {-2,0,1,2,4}
N14: w^2 = u^3 + u^2 - 2u      -> u ∈ {-2,0,1}
N16: w^2 = u^3 - u^2 - u       -> u ∈ {-1,0,1} as a harmless superset, or exactly u=0
```

The existing scratch files already have the integer squeeze style for N10, N14, and N16.  N12 is better handled by a finite rational-point certificate or by a separate integer enumeration plus descent for nonintegral denominators.

---

## 2. Steps that are curve-specific

### N10 / C20

Curve:

```text
E10: w^2 = u^3 + u^2 - u.
```

Normalization gives

```text
Y^2 = X * (X^2 + X Z^2 - Z^4).
```

Since

```text
gcd(X, X^2 + X Z^2 - Z^4) = 1
```

under `gcd X Z = 1`, the product-square step gives `X = ±a^2`.  In the positive branch the denominator quartic is

```text
B^2 = a^4 + Z^2 a^2 - Z^4.
```

This is the C20/N10 binary quartic already isolated in `scratch/DenominatorQuartic.lean`:

```text
t^2 = p^4 + p^2 q^2 - q^4.
```

### N12

Curve:

```text
E12: w^2 = u^3 - u^2 - 4u + 4
     = (u - 1)(u - 2)(u + 2).
```

Normalization gives

```text
Y^2 = (X - Z^2) * (X - 2 Z^2) * (X + 2 Z^2).
```

This is not the same two-factor pattern as N10.  The pairwise gcds are bounded by small constants:

```text
gcd(X - Z^2,  X - 2 Z^2) divides 1,
gcd(X - Z^2,  X + 2 Z^2) divides 3,
gcd(X - 2Z^2, X + 2 Z^2) divides 4.
```

So a direct denominator proof has several `2`- and `3`-adic cases.

For the Kubert square obstruction, use the cleaner 2-cover quartic:

```text
Y^2 = (T^2 + D^2) * (3 T^2 - D^2)
    = 3 T^4 + 2 D^2 T^2 - D^4.
```

The map to the elliptic curve is

```text
u = (3 T^2 + D^2) / D^2,
w = 3 T Y / D^3.
```

For `D = 1`, the obvious solutions are `T = ±1`, `Y = ±2`, giving `u = 4`, `w = ±6`.  These are genuine rational points on E12, so they must be listed as allowed/cuspidal/degenerate for the exact rational-point theorem.

Recommended theorem targets:

```lean
import Mathlib

namespace MazurProof.N12

/-- Exact rational u-coordinate conclusion for E12. -/
axiom rational_u_N12
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

/-- Quartic-cover form used by the Kubert square obstruction. -/
def N12Quartic (T D Y : ℤ) : Prop :=
  Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)

/-- The nontrivial denominator-descent theorem for the N12 cover. -/
axiom no_nontrivial_N12_quartic_denominator
    (T D Y : ℤ)
    (hD : 2 ≤ D)
    (hcop : Int.gcd T D = 1)
    (h : N12Quartic T D Y) :
    False

end MazurProof.N12
```

If the downstream obstruction only produces points on the cover, `no_nontrivial_N12_quartic_denominator` plus a finite check at `D=1` may be easier than proving the full elliptic-curve rational-point classification.

### N14

Curve:

```text
E14: w^2 = u^3 + u^2 - 2u
     = u(u + 2)(u - 1).
```

Normalization gives

```text
Y^2 = X * (X^2 + X Z^2 - 2 Z^4).
```

The gcd is not always `1`; it divides `2`:

```text
gcd(X, X^2 + X Z^2 - 2 Z^4) ∣ 2.
```

Therefore the denominator proof splits by parity of `X`.

Odd numerator, positive branch:

```text
X = a^2,
B^2 = a^4 + Z^2 a^2 - 2 Z^4.
```

Even numerator, positive branch: write `X = 2M`, `Y = 2Y1`; then

```text
Y1^2 = M * (2 M^2 + M Z^2 - Z^4).
```

With `M = a^2`, the quartic is

```text
B^2 = 2 a^4 + Z^2 a^2 - Z^4.
```

For completeness over all rational points, negative interval branches should also be included.  They are the sign-reflected variants:

```text
B^2 = -a^4 + Z^2 a^2 + 2 Z^4       -- odd numerator, negative branch
B^2 = -2 a^4 + Z^2 a^2 + Z^4       -- even numerator, negative branch
```

Recommended theorem targets:

```lean
import Mathlib

namespace MazurProof.N14

/-- Exact rational u-coordinate conclusion for E14. -/
axiom rational_u_N14
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u) :
    u = -2 ∨ u = 0 ∨ u = 1

/-- Odd numerator, positive branch. -/
def N14QuarticOddPos (a D B : ℤ) : Prop :=
  B ^ 2 = a ^ 4 + D ^ 2 * a ^ 2 - 2 * D ^ 4

/-- Even numerator, positive branch. -/
def N14QuarticEvenPos (a D B : ℤ) : Prop :=
  B ^ 2 = 2 * a ^ 4 + D ^ 2 * a ^ 2 - D ^ 4

/-- Odd numerator, negative branch. -/
def N14QuarticOddNeg (a D B : ℤ) : Prop :=
  B ^ 2 = -a ^ 4 + D ^ 2 * a ^ 2 + 2 * D ^ 4

/-- Even numerator, negative branch. -/
def N14QuarticEvenNeg (a D B : ℤ) : Prop :=
  B ^ 2 = -2 * a ^ 4 + D ^ 2 * a ^ 2 + D ^ 4

end MazurProof.N14
```

The existing `scratch/DescentN14.lean` proves the integer case with exactly this parity split: odd `u` gives the `a^4+a^2-2` equation, and even `u` gives the `2a^4+a^2-1` equation.

### N16

Curve:

```text
E16: w^2 = u^3 - u^2 - u
     = u(u^2 - u - 1).
```

Normalization gives

```text
Y^2 = X * (X^2 - X Z^2 - Z^4).
```

Here the gcd is again clean:

```text
gcd(X, X^2 - X Z^2 - Z^4) = 1
```

under `gcd X Z = 1`.  The positive branch gives

```text
X = a^2,
B^2 = a^4 - Z^2 a^2 - Z^4.
```

This is the N16 quartic from Q1935:

```text
s^4 - D^2 s^2 - D^4 = t^2.
```

Recommended theorem target:

```lean
import Mathlib

namespace MazurProof.N16

/-- A harmless superset conclusion matching the current bridge style. -/
axiom rational_u_N16_superset
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1

/-- Sharper statement, if desired: the only affine rational u-coordinate is `0`. -/
axiom rational_u_N16_exact
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = 0

/-- N16 denominator quartic. -/
def N16Quartic (a D B : ℤ) : Prop :=
  B ^ 2 = a ^ 4 - D ^ 2 * a ^ 2 - D ^ 4

/-- The N16 denominator-descent theorem. -/
axiom no_nontrivial_N16_quartic_denominator
    (a D B : ℤ)
    (hD : 2 ≤ D)
    (hcop : Int.gcd a D = 1)
    (h : N16Quartic a D B) :
    False

end MazurProof.N16
```

N16 is the best candidate for reusing the N10 binary quartic descent: use a sign parameter

```text
ε =  1  for N10,
ε = -1  for N16,
```

and prove the common family

```text
B^2 = a^4 + ε D^2 a^2 - D^4.
```

Do not try to reuse the final N10 rational-point theorem by quadratic twist; reuse the descent internals sign-parametrically.

---

## 3. Ring-check snippets for the curve-specific equations

These are the algebraic identities I would put near the beginning of the new files so every coefficient is checked by Lean.

```lean
import Mathlib

namespace MazurProof.RationalPointEquationChecks

/-- N10 / C20 denominator equation. -/
example (X Z : ℤ) :
    X ^ 3 + X ^ 2 * Z ^ 2 - X * Z ^ 4 =
      X * (X ^ 2 + X * Z ^ 2 - Z ^ 4) := by
  ring

/-- N12 denominator equation. -/
example (X Z : ℤ) :
    X ^ 3 - X ^ 2 * Z ^ 2 - 4 * X * Z ^ 4 + 4 * Z ^ 6 =
      (X - Z ^ 2) * (X - 2 * Z ^ 2) * (X + 2 * Z ^ 2) := by
  ring

/-- N12 Kubert-cover quartic maps to E12. -/
example (T D Y : ℤ)
    (hY : Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2)) :
    (3 * T * Y) ^ 2 =
      (3 * T ^ 2 + D ^ 2) ^ 3 -
      (3 * T ^ 2 + D ^ 2) ^ 2 * D ^ 2 -
      4 * (3 * T ^ 2 + D ^ 2) * D ^ 4 +
      4 * D ^ 6 := by
  rw [show (3 * T * Y) ^ 2 = 9 * T ^ 2 * Y ^ 2 by ring]
  rw [hY]
  ring

/-- N14 denominator equation. -/
example (X Z : ℤ) :
    X ^ 3 + X ^ 2 * Z ^ 2 - 2 * X * Z ^ 4 =
      X * (X ^ 2 + X * Z ^ 2 - 2 * Z ^ 4) := by
  ring

/-- N14 even-numerator reduction. -/
example (M Z : ℤ) :
    (2 * M) ^ 3 + (2 * M) ^ 2 * Z ^ 2 - 2 * (2 * M) * Z ^ 4 =
      4 * M * (2 * M ^ 2 + M * Z ^ 2 - Z ^ 4) := by
  ring

/-- N16 denominator equation. -/
example (X Z : ℤ) :
    X ^ 3 - X ^ 2 * Z ^ 2 - X * Z ^ 4 =
      X * (X ^ 2 - X * Z ^ 2 - Z ^ 4) := by
  ring

/-- N10/N16 sign-parametric denominator quartic family. -/
def SignedQuartic (eps a D B : ℤ) : Prop :=
  B ^ 2 = a ^ 4 + eps * D ^ 2 * a ^ 2 - D ^ 4

example (a D B : ℤ) :
    SignedQuartic 1 a D B ↔ B ^ 2 = a ^ 4 + D ^ 2 * a ^ 2 - D ^ 4 := by
  unfold SignedQuartic
  norm_num

example (a D B : ℤ) :
    SignedQuartic (-1) a D B ↔ B ^ 2 = a ^ 4 - D ^ 2 * a ^ 2 - D ^ 4 := by
  unfold SignedQuartic
  norm_num

end MazurProof.RationalPointEquationChecks
```

---

## Suggested file plan

### `RationalPointsCommon.lean`

Put these shared components here:

```text
normalized rational point structure;
clear-denominator helper;
gcd lemmas for normalized numerator/denominator;
product-of-coprime-factors-is-square wrappers;
strong-induction denominator descent wrapper.
```

### `RationalPointsN12.lean`

Use one of two approaches:

1. Full elliptic-curve rational-point classification:

   ```lean
   theorem rational_u_N12 :
       w^2 = u^3 - u^2 - 4u + 4 →
       u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4
   ```

   This is mathematically clean but requires handling the triple product or importing a rank-zero/torsion certificate for curve `24.a1`.

2. Kubert-cover-only proof:

   ```lean
   theorem n12_kubert_cover_solutions :
       q^2 = (t^2+1)(3t^2-1) →
       t = 1 ∨ t = -1  -- with q = ±2, depending on exact statement
   ```

   This is probably easier and more directly aligned with the obstruction construction.

### `RationalPointsN14.lean`

Target:

```lean
theorem rational_u_N14
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - 2 * u) :
    u = -2 ∨ u = 0 ∨ u = 1
```

Use denominator normalization, then split by parity of numerator.  The required quartics are:

```text
B^2 =  a^4 + D^2 a^2 - 2D^4
B^2 =  2a^4 + D^2 a^2 - D^4
B^2 = -a^4 + D^2 a^2 + 2D^4
B^2 = -2a^4 + D^2 a^2 + D^4
```

The existing integer proof in `scratch/DescentN14.lean` is the `D=1` version of the first two positive cases.

### `RationalPointsN16.lean`

Target, either exact or superset:

```lean
theorem rational_u_N16_exact
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = 0
```

or

```lean
theorem rational_u_N16_superset
    (u w : ℚ)
    (h : w ^ 2 = u ^ 3 - u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1
```

The denominator quartic is:

```text
B^2 = a^4 - D^2 a^2 - D^4.
```

This should share most of the N10 descent after introducing the sign parameter `ε`.

---

## Practical warning for the bridge files

The current bridge-style axioms for N14 and N16 match harmless finite `u`-sets:

```text
N14: {-2,0,1}
N16: {-1,0,1}  -- over-approximation; exact is likely {0}
```

But the N12 bridge set

```text
{-2,1,2}
```

cannot be the set of all rational `u` on

```text
w^2 = u^3 - u^2 - 4u + 4,
```

because `(u,w)=(0,±2)` and `(4,±6)` are rational points.  So for N12, either enlarge the finite set to

```text
{-2,0,1,2,4}
```

or state the downstream theorem on the Kubert-cover variables `(t,q)` instead of all elliptic-curve points.
