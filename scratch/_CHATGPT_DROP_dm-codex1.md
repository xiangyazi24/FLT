# Q2359 (dm-codex1): roadmap for `EisensteinQuarticSquareClassification`

## Executive summary

The theorem needed by the checked Lean frontier is exactly the affine rational-point classification for

```text
C : y^2 = x^4 - x^2 + 1 = Phi_12(x).
```

A clean target is:

```text
C(Q)_affine = {(0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)}.
```

Then the homogeneous integer theorem follows immediately by taking `x = m / n` and `y = c / n^2` when `n != 0`; if `n = 0` this is already one of the allowed alternatives.

I would not call this the standard Ljunggren 1942 theorem. The name “Ljunggren equation” most commonly refers to `X^2 + 1 = 2 Y^4`, or more generally Ljunggren's 1942 paper `Zur Theorie der Gleichung X^2 + 1 = D Y^4`. Your equation is better described as the square-value/rational-point computation for the cyclotomic quartic `Phi_12(x) = x^4 - x^2 + 1`, equivalently a finite rational-point computation on the conductor-24 elliptic curve

```text
E24 : V^2 = U^3 - U^2 - 4*U + 4.
```

That elliptic curve is the genus-one modular curve model with Weierstrass coefficients `[0, -1, 0, -4, 4]`, often appearing as the `X_0(24)` model. The exact affine rational point set needed is

```text
E24(Q)_affine =
  {(-2, 0), (1, 0), (2, 0), (0, 2), (0, -2), (4, 6), (4, -6)}.
```

Together with the point at infinity this is an 8-point group, torsion isomorphic to `Z/2Z × Z/4Z`.

## Exact birational maps

Use the affine genus-one quartic

```text
C : y^2 = x^4 - x^2 + 1
```

and the Weierstrass model

```text
E24 : V^2 = U^3 - U^2 - 4*U + 4.
```

For `x != 0`, the map `C -> E24` is:

```text
U = 2*(y + 1) / x^2
V = 2*((y + 1)^2 - x^4) / x^3
```

Equivalently, if `X = (y + 1)/x^2` and `Y = x*(X^2 - 1)`, then `U = 2X`, `V = 2Y`. The relation becomes

```text
V^2 = U^3 - U^2 - 4*U + 4.
```

For `V != 0`, the inverse `E24 -> C` is:

```text
x = 2*(U - 1) / V
y = 2*U*(U - 1)^2 / V^2 - 1
```

Checking the finite list:

```text
(U, V) = (4,  6)  -> (x, y) = ( 1,  1)
(U, V) = (4, -6)  -> (x, y) = (-1,  1)
(U, V) = (0,  2)  -> (x, y) = (-1, -1)
(U, V) = (0, -2)  -> (x, y) = ( 1, -1)
```

The missing affine quartic points are exactly `x = 0`, namely `(0, 1)` and `(0, -1)`. The `V = 0` points on `E24`, namely `(-2,0)`, `(1,0)`, `(2,0)`, correspond to the exceptional projective/base-point behavior and are not images of affine `C` points with `x != 0`.

Therefore the finite `E24(Q)` theorem implies

```text
∀ x y : Q, y^2 = x^4 - x^2 + 1 -> x = 0 or x = 1 or x = -1.
```

That is the only rational-point input the current integer theorem needs.

## Ranking proof routes by Lean formalization cost

### 1. Recommended: rational quartic -> explicit `E24` finite-point theorem

This is the shortest integration path for the current file. Prove the elementary rational maps once, isolate the hard theorem as `E24_affine_rational_points`, then derive `C(Q)` and the integer classification.

Formalization cost: low for the bridge; medium for the finite elliptic-curve theorem if proved by the special 2-isogeny descent below.

### 2. Prove `E24(Q)` by a special 2-isogeny descent plus Nagell-Lutz

Shift `E24` by `X = U - 1`, `Y = V`. This gives

```text
E1 : Y^2 = X^3 + 2*X^2 - 3*X = X*(X - 1)*(X + 3).
```

The 2-isogenous curve, using the standard formula for `Y^2 = X^3 + a*X^2 + b*X` with `a = 2`, `b = -3`, is

```text
E2 : Y^2 = X^3 - 4*X^2 + 16*X.
```

The isogeny with kernel `{O, (0,0)}` is, for `X != 0`,

```text
phi(X, Y) = (Y^2 / X^2, Y*(-3 - X^2) / X^2).
```

The 2-isogeny descent uses the usual squareclass map:

```text
alpha_E1(O)       = 1
alpha_E1((0, 0))  = -3
alpha_E1((X, Y))  = X mod Q*^2, if X != 0
```

For `E1`, the possible squareclasses are `1`, `-1`, `3`, `-3`; all occur. The covering equation for squareclass `d`, with `d*e = -3`, is

```text
N^2 = d*M^4 + 2*M^2*Z^2 + e*Z^4.
```

Witnesses:

```text
d =  1, e = -3: M = 1, Z = 0, N = 1
d = -3, e =  1: M = 0, Z = 1, N = 1
d = -1, e =  3: M = 1, Z = 1, N = 2
d =  3, e = -1: M = 1, Z = 1, N = 2
```

For `E2`, the possible squareclasses are `1`, `-1`, `2`, `-2`. The covering equation is

```text
N^2 = d*M^4 - 4*M^2*Z^2 + (16/d)*Z^4.
```

Only `d = 1` occurs. The cases `d = -1` and `d = -2` are negative for nonzero `(M,Z)`. The case `d = 2` is ruled out by congruences for coprime integers `M,Z`:

```text
N^2 = 2*M^4 - 4*M^2*Z^2 + 8*Z^4.
```

If `M` is odd and `Z` is even, the right side is `2 mod 8`. If `M` and `Z` are both odd, it is `6 mod 8`. If `M` is even, coprimality forces `Z` odd, and the right side is `8 mod 16`. All are impossible for a square.

Thus the descent images have sizes `4` and `1`; the 2-isogeny rank formula gives rank `0` for `E1`, hence for `E24`.

Then use Nagell-Lutz on the integral model `E1`. Its discriminant is `2304 = 2^8 * 3^2`. Since rank is zero, every rational point is torsion; Nagell-Lutz gives integral coordinates and either `Y = 0` or `Y^2 | 2304`. A finite integer check on

```text
Y^2 = X*(X - 1)*(X + 3)
```

gives

```text
E1(Q)_affine = {(-3,0), (0,0), (1,0), (-1,2), (-1,-2), (3,6), (3,-6)}.
```

Shifting back by `U = X + 1` gives the `E24` list above.

Formalization cost: medium. This is the most honest route that still avoids modular curves and avoids a full general Mordell-Weil formalization beyond the special 2-isogeny descent certificate.

### 3. Direct infinite descent on the quartic

There should be an Eisenstein-integer descent behind the statement, because

```text
m^4 - m^2*n^2 + n^4 = Norm_Z[omega](m^2 + n^2*omega).
```

For primitive nonzero `(m,n)`, one analyzes coprime conjugate Eisenstein factors and shows that a square norm forces a smaller solution unless `m^2 = n^2`. This is mathematically attractive but Lean-expensive unless `Z[omega]` is already available as a Euclidean domain/UFD with the needed coprimality and unit lemmas.

Formalization cost: medium-high to high, depending on existing Eisenstein-integer infrastructure.

### 4. Modular curve route

One can identify the Weierstrass curve above with the genus-one model of `X_0(24)`. The rational points are the eight cusps. This is conceptually close to the surrounding Mazur material, but it is not the shortest way to close the current theorem unless the repository already has a checked `X_0(24)(Q)` result.

Formalization cost: high if developed from scratch.

## Recommended Lean theorem interfaces

The following block is intended as a Lean-friendly dependency outline, not as a finished proof file. The declarations are stated as `Prop` interfaces to avoid introducing axioms or `sorry`s.

```lean
import Mathlib

namespace FLT.RationalPointsN12Roadmap

/-- Affine quartic `C : y^2 = x^4 - x^2 + 1` over `Q`. -/
def C12 (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- Weierstrass model birational to `C12`. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- Shifted model `X = U - 1`, useful for the 2-isogeny descent. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- 2-isogenous curve to `E1`. -/
def E2 (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 - 4 * X ^ 2 + 16 * X

/-- Forward map `C12 -> E24`, valid when `x != 0`. -/
def C12_to_E24_U (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

def C12_to_E24_V (x y : ℚ) : ℚ :=
  2 * ((y + 1) ^ 2 - x ^ 4) / x ^ 3

/-- Inverse map `E24 -> C12`, valid when `V != 0`. -/
def E24_to_C12_x (U V : ℚ) : ℚ :=
  2 * (U - 1) / V

def E24_to_C12_y (U V : ℚ) : ℚ :=
  2 * U * (U - 1) ^ 2 / V ^ 2 - 1

/-- The exact finite affine point set of `E24`. -/
def E24AffinePointSet (U V : ℚ) : Prop :=
  (U = -2 ∧ V = 0) ∨
  (U = 1 ∧ V = 0) ∨
  (U = 2 ∧ V = 0) ∨
  (U = 0 ∧ V = 2) ∨
  (U = 0 ∧ V = -2) ∨
  (U = 4 ∧ V = 6) ∨
  (U = 4 ∧ V = -6)

/-- Hard finite rational-point theorem to prove by 2-isogeny descent + Nagell-Lutz. -/
def E24AffineRationalPointsStatement : Prop :=
  ∀ {U V : ℚ}, E24 U V -> E24AffinePointSet U V

/-- Equivalent quartic rational-point theorem; this is the direct input for the integer theorem. -/
def C12RatXClassificationStatement : Prop :=
  ∀ {x y : ℚ}, C12 x y -> x = 0 ∨ x = 1 ∨ x = -1

/-- The homogeneous integer classification wanted by the current file. -/
def EisensteinQuarticSquareClassificationStatement : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 ->
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

end FLT.RationalPointsN12Roadmap
```

For the actual repository file, I would expose these as theorems in this order:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN12

-- 1. Algebraic map checks.
-- theorem C12_to_E24_of_ne_zero
--     {x y : ℚ} (hx : x ≠ 0) (hC : y ^ 2 = x ^ 4 - x ^ 2 + 1) :
--     (C12_to_E24_V x y) ^ 2 =
--       (C12_to_E24_U x y) ^ 3 - (C12_to_E24_U x y) ^ 2 -
--         4 * (C12_to_E24_U x y) + 4

-- theorem E24_to_C12_of_V_ne_zero
--     {U V : ℚ} (hV : V ≠ 0)
--     (hE : V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4) :
--     (E24_to_C12_y U V) ^ 2 =
--       (E24_to_C12_x U V) ^ 4 - (E24_to_C12_x U V) ^ 2 + 1

-- theorem C12_to_E24_V_ne_zero
--     {x y : ℚ} (hx : x ≠ 0) (hC : y ^ 2 = x ^ 4 - x ^ 2 + 1) :
--     C12_to_E24_V x y ≠ 0

-- 2. Hard finite EC theorem.
-- theorem E24_affine_rational_points
--     {U V : ℚ}
--     (hE : V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4) :
--     E24AffinePointSet U V

-- 3. Quartic rational points.
-- theorem C12_rat_x_classification
--     {x y : ℚ} (hC : y ^ 2 = x ^ 4 - x ^ 2 + 1) :
--     x = 0 ∨ x = 1 ∨ x = -1

-- 4. Integer bridge into the existing definition.
-- theorem eisensteinQuarticSquareClassification_of_C12_rat
--     (hC : ∀ {x y : ℚ},
--       y ^ 2 = x ^ 4 - x ^ 2 + 1 -> x = 0 ∨ x = 1 ∨ x = -1) :
--     EisensteinQuarticSquareClassification
```

## Machine-checkable subgoals in dependency order

1. Define `C12` and `E24` over `ℚ`.
2. Prove the forward map identity `C12_to_E24_of_ne_zero` by field simplification after clearing denominators using `hx : x != 0`.
3. Prove `C12_to_E24_V_ne_zero`. The only possible zero would force `(y+1)^2 = x^4`; combined with `y^2 = x^4 - x^2 + 1`, it forces `x = 0`, contradiction.
4. Prove the inverse map identity `E24_to_C12_of_V_ne_zero` by clearing denominators with `hV : V != 0`.
5. Prove the finite elliptic-curve theorem `E24_affine_rational_points`.
6. From steps 2, 3, and 5, prove that any `C12` point with `x != 0` has `x = 1 ∨ x = -1`; the `x = 0` case is immediate.
7. Derive `C12_rat_x_classification`.
8. Prove the integer bridge: if `n = 0`, return `n = 0`; otherwise set

   ```text
   x = (m : Q) / (n : Q)
   y = (c : Q) / (n : Q)^2
   ```

   and obtain a `C12` point by dividing the homogeneous equation by `n^4`.
9. Convert `x = 0`, `x = 1`, `x = -1` back to integer alternatives:

   ```text
   (m : Q) / n = 0  -> m = 0
   (m : Q) / n = 1  -> m = n -> m^2 = n^2
   (m : Q) / n = -1 -> m = -n -> m^2 = n^2
   ```

10. Package as

   ```lean
   theorem eisensteinQuarticSquareClassification_checked :
       EisensteinQuarticSquareClassification :=
     eisensteinQuarticSquareClassification_of_C12_rat C12_rat_x_classification
   ```

## Sanity checks and false stronger statements to avoid

Do not prove “no Eisenstein quartic residuals”. Diagonal and axis examples exist:

```text
m = 0, n = k, c = ±k^2
n = 0, m = k, c = ±k^2
m = n = k, c = ±k^2
m = -n = k, c = ±k^2
```

For example,

```text
1^4 - 1^2*1^2 + 1^4 = 1
```

so `(m,n,c) = (1,1,±1)` are genuine residuals. The correct conclusion is exactly

```text
m = 0 ∨ n = 0 ∨ m^2 = n^2.
```

No coprimality hypothesis is needed for the classification itself. Nonprimitive diagonal solutions simply scale, e.g. `(m,n,c) = (2,2,±4)`.

Also keep the sign of `c` unrestricted. The equation only determines `c^2`; the point sets over `Q` contain both `y = 1` and `y = -1`.

Finally, when using the birational map, do not forget the exceptional affine quartic points with `x = 0`. They are exactly the reason the rational theorem should state `x = 0 ∨ x = 1 ∨ x = -1`, not just `x^2 = 1`.

## Bottom line for the current Lean frontier

The theorem currently named

```lean
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 ->
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2
```

should be proved through the rational theorem

```lean
∀ {x y : ℚ}, y ^ 2 = x ^ 4 - x ^ 2 + 1 -> x = 0 ∨ x = 1 ∨ x = -1
```

and that rational theorem should be proved through the explicit finite point theorem for

```text
E24 : V^2 = U^3 - U^2 - 4U + 4.
```

This gives a small, auditable algebraic bridge in `RationalPointsN12.lean`, while leaving exactly one classical arithmetic theorem to formalize in a separate file: the 8 rational points on the conductor-24 elliptic curve above.
