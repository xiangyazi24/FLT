# Q1936 (dm3): N=12 Kubert square obstruction curve

## Executive answer

For the curve

```text
E12 : w^2 = u^3 - u^2 - 4*u + 4,
```

the LMFDB label is

```text
24.a1
```

Equivalently, its Cremona label is `24a1`.  In Cremona/ecdata notation the entry is conductor `24`, isogeny class `A`, curve number `1`, with Weierstrass coefficients

```text
[0, -1, 0, -4, 4]
```

and rank `0`, torsion order `8`.

The Mordell-Weil group over `ℚ` is

```text
E12(ℚ) ≃ ℤ/4ℤ × ℤ/2ℤ
```

or equivalently `ℤ/2ℤ × ℤ/4ℤ`.  It is rank `0`.

The affine rational points are exactly

```text
(-2, 0),
( 1, 0),
( 2, 0),
( 0, 2),
( 0,-2),
( 4, 6),
( 4,-6).
```

Together with the point at infinity `O`, this gives all eight rational points.

## Why this is the right curve label

The curve is already in generalized Weierstrass form

```text
y^2 = x^3 + a2*x^2 + a4*x + a6
```

with

```text
a1 = 0,
a2 = -1,
a3 = 0,
a4 = -4,
a6 = 4.
```

So its `a`-invariants are

```text
[0, -1, 0, -4, 4].
```

The Cremona/ecdata entry for `[0,-1,0,-4,4]` is

```text
24 A 1 [0,-1,0,-4,4] rank 0 torsion 8
```

which corresponds to LMFDB label `24.a1`.

## Factorization and torsion structure

The cubic factors as

```text
u^3 - u^2 - 4*u + 4 = (u - 1) * (u - 2) * (u + 2).
```

Therefore the three nonzero rational `2`-torsion points are

```text
(-2, 0), (1, 0), (2, 0).
```

There are also rational points

```text
P  = (0, 2),
-P = (0,-2),
Q  = (4, 6),
-Q = (4,-6).
```

Using the group law on

```text
y^2 = x^3 - x^2 - 4*x + 4,
```

one has

```text
2*(0, 2) = (2, 0),
```

so `(0,2)` has order `4`.  Since the curve has full rational `2`-torsion and a point of order `4`, the torsion subgroup contains `ℤ/4ℤ × ℤ/2ℤ`, which has order `8`.  The database entry says the torsion order is exactly `8`, so the torsion subgroup is precisely

```text
E12(ℚ)_tors ≃ ℤ/4ℤ × ℤ/2ℤ.
```

Since the rank is `0`, this is the whole Mordell-Weil group.

## Relation to the Kubert square obstruction

Starting from

```text
q^2 = (t^2 + 1) * (3*t^2 - 1),
```

set

```text
u = 3*t^2 + 1,
w = 3*t*q.
```

Then

```text
w^2 = 9*t^2*q^2
    = 9*t^2*(t^2 + 1)*(3*t^2 - 1)
    = (3*t^2 + 1)^3 - (3*t^2 + 1)^2 - 4*(3*t^2 + 1) + 4
    = u^3 - u^2 - 4*u + 4.
```

Equivalently,

```text
u^3 - u^2 - 4*u + 4 = (u - 1)*(u - 2)*(u + 2)
```

and, under `u = 3*t^2 + 1`, this becomes

```text
(3*t^2)*(3*t^2 - 1)*(3*t^2 + 3)
  = 9*t^2*(3*t^2 - 1)*(t^2 + 1).
```

So the substitution is exactly the advertised genus-one obstruction map.

## Lift back to `(t,q)`

The rational points on `E12` have `u`-coordinates

```text
-2, 0, 1, 2, 4.
```

For points coming from the square obstruction, one must also have

```text
u = 3*t^2 + 1.
```

Checking the listed rational points:

* `u = -2` gives `t^2 = -1`, impossible over `ℚ`.
* `u = 0` gives `t^2 = -1/3`, impossible over `ℚ`.
* `u = 1` gives `t = 0`, but the original equation gives `q^2 = -1`, impossible over `ℚ`.
* `u = 2` gives `t^2 = 1/3`, impossible over `ℚ`.
* `u = 4` gives `t^2 = 1`, and the original equation gives `q^2 = 4`.

Thus the only rational solutions to the square obstruction itself are the obvious finite set

```text
t =  1, q =  2,
t =  1, q = -2,
t = -1, q =  2,
t = -1, q = -2.
```

These map to the two elliptic-curve points `(u,w) = (4,6)` and `(4,-6)`, depending on the sign of `t*q`.  In the Kubert parametrization these should be checked against the usual excluded/cuspidal/degenerate parameter values.  In particular, one should not state that the square obstruction has no rational solutions without those exclusions: it has the four solutions above.

## Is rank zero plus torsion enough for Lean?

Mathematically, yes.  The same strategy as the `N = 10` use of `20.a4` works here:

1. identify the obstruction curve as `24.a1`;
2. use the rank computation `rank E12(ℚ) = 0`;
3. use the torsion computation `E12(ℚ)_tors ≃ ℤ/4ℤ × ℤ/2ℤ`;
4. exhibit the eight points listed above;
5. conclude that there are no other rational points.

For Lean 4, however, the database statement is not itself a proof unless it is imported as a trusted theorem/certificate.  The formal theorem you want downstream is more like:

```text
Every rational point on w^2 = u^3 - u^2 - 4*u + 4 is one of
O, (-2,0), (1,0), (2,0), (0,±2), (4,±6).
```

Once that theorem is available, the obstruction argument is just a finite case split on the eight points, plus the equations `u = 3*t^2 + 1` and `w = 3*t*q`.

A practical Lean architecture is therefore:

```lean
import Mathlib

/-- The N=12 obstruction curve RHS. -/
def E12RHS (u : ℚ) : ℚ := u ^ 3 - u ^ 2 - 4 * u + 4

example : E12RHS (-2) = 0 := by norm_num [E12RHS]
example : E12RHS (1) = 0 := by norm_num [E12RHS]
example : E12RHS (2) = 0 := by norm_num [E12RHS]
example : E12RHS 0 = 2 ^ 2 := by norm_num [E12RHS]
example : E12RHS 0 = (-2) ^ 2 := by norm_num [E12RHS]
example : E12RHS 4 = 6 ^ 2 := by norm_num [E12RHS]
example : E12RHS 4 = (-6) ^ 2 := by norm_num [E12RHS]

example {t q : ℚ}
    (hq : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    (3 * t * q) ^ 2 =
      (3 * t ^ 2 + 1) ^ 3 - (3 * t ^ 2 + 1) ^ 2 -
        4 * (3 * t ^ 2 + 1) + 4 := by
  ring_nf at hq ⊢
  nlinarith [hq]
```

Then either prove or import a certificate theorem with the shape:

```lean
-- Schematic, not using a particular project-local point type.
-- theorem E12_rat_points_complete (P : E12.Point ℚ) :
--   P = O ∨
--   P = affine (-2) 0 ∨ P = affine 1 0 ∨ P = affine 2 0 ∨
--   P = affine 0 2 ∨ P = affine 0 (-2) ∨
--   P = affine 4 6 ∨ P = affine 4 (-6) := ...
```

The `rank 0 + torsion` computation is exactly the right mathematical certificate to justify this enumeration, just as for `N = 10`; the only formalization issue is how that certificate is represented inside Lean.
