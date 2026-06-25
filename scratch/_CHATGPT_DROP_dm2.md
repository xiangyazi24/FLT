# Q259 (dm2): Explicit general-Weierstrass `addX` cofactor `Q₂`

The cofactor from Q257 is

```text
addX([X,Y,1], [φ₂,ω₂,ψ₂]) - ψ₁²·φ₃ = Q₂ · F_W
```

for

```text
F_W = Y² + a₁XY + a₃Y - X³ - a₂X² - a₄X - a₆.
```

## Compact factorization

Let

```text
ψ₂   = 2Y + a₁X + a₃
Ψ₂Sq = 4X³ + (a₁² + 4a₂)X² + (2a₁a₃ + 4a₄)X + (a₃² + 4a₆).
```

Then

```text
Q₂ = 2 · ψ₂² · Ψ₂Sq.
```

Equivalently,

```text
Q₂ = 2*(X*a1 + 2*Y + a3)^2*
       (4*X^3 + X^2*a1^2 + 4*X^2*a2 + 2*X*a1*a3 + 4*X*a4 + a3^2 + 4*a6)
```

## Expanded polynomial

```text
Q₂ = 8*X^5*a1^2 + 32*X^4*Y*a1 + 2*X^4*a1^4 + 8*X^4*a1^2*a2 + 16*X^4*a1*a3 + 32*X^3*Y^2 + 8*X^3*Y*a1^3 + 32*X^3*Y*a1*a2 + 32*X^3*Y*a3 + 8*X^3*a1^3*a3 + 8*X^3*a1^2*a4 + 16*X^3*a1*a2*a3 + 8*X^3*a3^2 + 8*X^2*Y^2*a1^2 + 32*X^2*Y^2*a2 + 24*X^2*Y*a1^2*a3 + 32*X^2*Y*a1*a4 + 32*X^2*Y*a2*a3 + 12*X^2*a1^2*a3^2 + 8*X^2*a1^2*a6 + 16*X^2*a1*a3*a4 + 8*X^2*a2*a3^2 + 16*X*Y^2*a1*a3 + 32*X*Y^2*a4 + 24*X*Y*a1*a3^2 + 32*X*Y*a1*a6 + 32*X*Y*a3*a4 + 8*X*a1*a3^3 + 16*X*a1*a3*a6 + 8*X*a3^2*a4 + 8*Y^2*a3^2 + 32*Y^2*a6 + 8*Y*a3^3 + 32*Y*a3*a6 + 2*a3^4 + 8*a3^2*a6
```

## Lean syntax, preferred compact version

This is the version I would use in Lean.  It is much smaller and should expand by `ring_nf` when needed.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {K : Type*} [CommRing K]

/-- General-Weierstrass `addX` cofactor for the `m = 2` division-polynomial identity. -/
def addX_m2_Q₂ (W : WeierstrassCurve K) : K[X][Y] :=
  (2 : K[X][Y]) *
    (C (C W.a₁ * X + C W.a₃) + (2 : K[X][Y]) * Y) ^ 2 *
      C ((4 : K[X]) * X ^ 3
        + C (W.a₁ ^ 2 + 4 * W.a₂) * X ^ 2
        + C (2 * W.a₁ * W.a₃ + 4 * W.a₄) * X
        + C (W.a₃ ^ 2 + 4 * W.a₆))

end Affine
end WeierstrassCurve
```

This is exactly

```lean
2 * ψ₂^2 * W.Ψ₂Sq
```

with `ψ₂ = C (C W.a₁ * X + C W.a₃) + 2 * Y` and `W.Ψ₂Sq` expanded.

## Lean syntax, expanded by `Y`-degree

If you want a fully expanded expression but not a single huge flat sum, this is grouped as

```text
C(q0) + C(q1) * Y + C(q2) * Y^2.
```

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {K : Type*} [CommRing K]

/-- Expanded general-Weierstrass `addX` cofactor for `m = 2`, grouped by powers of `Y`. -/
def addX_m2_Q₂_expanded (W : WeierstrassCurve K) : K[X][Y] :=
  C (
      C (8 * W.a₁ ^ 2) * X ^ 5
    + C (2 * W.a₁ ^ 4 + 8 * W.a₁ ^ 2 * W.a₂ + 16 * W.a₁ * W.a₃) * X ^ 4
    + C (8 * W.a₁ ^ 3 * W.a₃ + 8 * W.a₁ ^ 2 * W.a₄
        + 16 * W.a₁ * W.a₂ * W.a₃ + 8 * W.a₃ ^ 2) * X ^ 3
    + C (12 * W.a₁ ^ 2 * W.a₃ ^ 2 + 8 * W.a₁ ^ 2 * W.a₆
        + 16 * W.a₁ * W.a₃ * W.a₄ + 8 * W.a₂ * W.a₃ ^ 2) * X ^ 2
    + C (8 * W.a₁ * W.a₃ ^ 3 + 16 * W.a₁ * W.a₃ * W.a₆
        + 8 * W.a₃ ^ 2 * W.a₄) * X
    + C (2 * W.a₃ ^ 4 + 8 * W.a₃ ^ 2 * W.a₆))
  + C (
      C (32 * W.a₁) * X ^ 4
    + C (8 * W.a₁ ^ 3 + 32 * W.a₁ * W.a₂ + 32 * W.a₃) * X ^ 3
    + C (24 * W.a₁ ^ 2 * W.a₃ + 32 * W.a₁ * W.a₄
        + 32 * W.a₂ * W.a₃) * X ^ 2
    + C (24 * W.a₁ * W.a₃ ^ 2 + 32 * W.a₁ * W.a₆
        + 32 * W.a₃ * W.a₄) * X
    + C (8 * W.a₃ ^ 3 + 32 * W.a₃ * W.a₆)) * Y
  + C (
      C (32 : K) * X ^ 3
    + C (8 * W.a₁ ^ 2 + 32 * W.a₂) * X ^ 2
    + C (16 * W.a₁ * W.a₃ + 32 * W.a₄) * X
    + C (8 * W.a₃ ^ 2 + 32 * W.a₆)) * Y ^ 2

end Affine
end WeierstrassCurve
```

## Useful simp equality

After defining both, this should close by `ring_nf`:

```lean
lemma addX_m2_Q₂_eq_expanded (W : WeierstrassCurve K) :
    addX_m2_Q₂ W = addX_m2_Q₂_expanded W := by
  rw [addX_m2_Q₂, addX_m2_Q₂_expanded]
  ring_nf
```
