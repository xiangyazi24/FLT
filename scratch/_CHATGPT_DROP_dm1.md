# Q2051 (dm1): Concrete line and vertical functions in `W.FunctionField`

Date: 2026-06-28.

This is the concrete Lean 4 layer for Miller line functions using Mathlib's affine Weierstrass coordinate ring API.

Important type correction from Q2045: the function-field type is

```lean
W.FunctionField
```

not `W.Affine.FunctionField K`.  In Mathlib,

```lean
W.CoordinateRing = AdjoinRoot W.polynomial
W.FunctionField = FractionRing W.CoordinateRing
```

The code below is written for the **short Weierstrass** subfamily

```text
y^2 = x^3 + a4*x + a6
```

represented in Mathlib by an affine Weierstrass curve `W : WeierstrassCurve.Affine K` with

```lean
W.a₁ = 0, W.a₂ = 0, W.a₃ = 0
```

The definitions do not require these equalities as arguments, but the tangent/secant formulas are mathematically intended under that short-curve assumption.

## Lean 4 code

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Concrete Miller line functions for short Weierstrass curves

For a short Weierstrass curve

  y^2 = x^3 + a4*x + a6,

this file defines vertical, tangent, and secant line functions as elements of

  W.FunctionField = FractionRing W.CoordinateRing.

The point-at-infinity cases are normalized to `1`, which is convenient for the
Miller-loop identity cases.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
namespace ShortMillerFunctions

universe u

variable {K : Type u} [Field K]
variable (W : Affine K)

/-- Predicate saying that a Mathlib affine Weierstrass curve is in short form. -/
def IsShort : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0

/-- Embed a coordinate-ring function into the function field. -/
noncomputable def crToFF (f : W.CoordinateRing) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField f

/--
The coordinate-ring element

  `Y - (ℓ * (X - x₀) + y₀)`.

This is the affine line through `(x₀,y₀)` with slope `ℓ`, before embedding into
the function field.
-/
noncomputable def affineLineCR (x₀ y₀ ℓ : K) : W.CoordinateRing :=
  CoordinateRing.YClass W (linePolynomial x₀ y₀ ℓ)

/--
The function-field element

  `Y - (ℓ * (X - x₀) + y₀)`.
-/
noncomputable def affineLineFF (x₀ y₀ ℓ : K) : W.FunctionField :=
  crToFF W (affineLineCR W x₀ y₀ ℓ)

/--
The short-Weierstrass tangent slope

  `(3*x^2 + a4) / (2*y)`.

This is the usual slope for `y^2 = x^3 + a4*x + a6` when `2*y ≠ 0`.
-/
noncomputable def tangentSlope (x y : K) : K :=
  (3 * x ^ 2 + W.a₄) / (2 * y)

/--
The short-Weierstrass secant slope

  `(y₂ - y₁) / (x₂ - x₁)`.

This is used only in the branch `x₁ ≠ x₂`.
-/
noncomputable def secantSlope (x₁ y₁ x₂ y₂ : K) : K :=
  (y₂ - y₁) / (x₂ - x₁)

/--
The vertical line through a point, as a function-field element.

For `P = (x_P,y_P)`, this is `X - x_P`.  For the point at infinity, it is
normalized to `1`.
-/
noncomputable def verticalLine : W.Point → W.FunctionField
  | 0 => 1
  | .some x _ _ => crToFF W (CoordinateRing.XClass W x)

/--
The formal short-Weierstrass tangent-line formula at a point.

For `P = (x_P,y_P)`, this is

  `Y - y_P - ((3*x_P^2 + a4)/(2*y_P)) * (X - x_P)`.

For the point at infinity, it is normalized to `1`.

This definition is exactly the formula branch.  If `2*y_P = 0`, Lean's field
inverse convention makes the slope expression total, but mathematically the
tangent is vertical.  Use `tangentLine` below for the Miller-safe total tangent.
-/
noncomputable def tangentLineFormula : W.Point → W.FunctionField
  | 0 => 1
  | .some x y _ => affineLineFF W x y (tangentSlope W x y)

/--
The Miller-safe tangent line at a point.

For an affine point with `2*y_P ≠ 0`, this is the usual short-Weierstrass tangent
line

  `Y - y_P - ((3*x_P^2 + a4)/(2*y_P)) * (X - x_P)`.

For an affine point with `2*y_P = 0`, the tangent is vertical, so this returns
`X - x_P`.  For the point at infinity, it is normalized to `1`.
-/
noncomputable def tangentLine (P : W.Point) : W.FunctionField := by
  classical
  cases P with
  | zero =>
      exact 1
  | some x y h =>
      by_cases hy : 2 * y = 0
      · exact verticalLine W (.some x y h)
      · exact affineLineFF W x y (tangentSlope W x y)

/--
The secant line through two points, as a function-field element.

Normalization and branch convention:

* if either point is `O`, return `1`;
* if the two affine points have the same coordinates, return the tangent line;
* if the two affine points have the same `x` but different `y`, return the
  vertical line `X - x`;
* otherwise return the ordinary secant line through the two affine points.
-/
noncomputable def secantLine (P Q : W.Point) : W.FunctionField := by
  classical
  exact
    match P, Q with
    | 0, _ => 1
    | _, 0 => 1
    | .some x₁ y₁ h₁, .some x₂ y₂ _h₂ =>
        if hsame : x₁ = x₂ ∧ y₁ = y₂ then
          tangentLine W (.some x₁ y₁ h₁)
        else if hx : x₁ = x₂ then
          crToFF W (CoordinateRing.XClass W x₁)
        else
          affineLineFF W x₁ y₁ (secantSlope x₁ y₁ x₂ y₂)

/-! ## Small simp lemmas for the normalized identity cases. -/

@[simp]
theorem verticalLine_zero : verticalLine W 0 = 1 :=
  rfl

@[simp]
theorem tangentLineFormula_zero : tangentLineFormula W 0 = 1 :=
  rfl

@[simp]
theorem tangentLine_zero : tangentLine W 0 = 1 := by
  simp [tangentLine]

@[simp]
theorem secantLine_zero_left (Q : W.Point) : secantLine W 0 Q = 1 := by
  simp [secantLine]

@[simp]
theorem secantLine_zero_right (P : W.Point) : secantLine W P 0 = 1 := by
  cases P <;> simp [secantLine]

end ShortMillerFunctions
end Affine
end WeierstrassCurve
```

## Notes for the next layer

The three requested functions are the concrete names:

```lean
WeierstrassCurve.Affine.ShortMillerFunctions.verticalLine W P
-- type: W.FunctionField

WeierstrassCurve.Affine.ShortMillerFunctions.tangentLine W P
-- type: W.FunctionField

WeierstrassCurve.Affine.ShortMillerFunctions.secantLine W P Q
-- type: W.FunctionField
```

Inside the namespace from the code block, just write:

```lean
verticalLine W P

tangentLine W P

secantLine W P Q
```

The implementation uses:

```lean
CoordinateRing.XClass W x
CoordinateRing.YClass W (linePolynomial x y ℓ)
algebraMap W.CoordinateRing W.FunctionField
```

so the functions really are elements of `FractionRing W.CoordinateRing`.

For Miller's correction factor, the next definition should be:

```lean
noncomputable def gFunction (P Q : W.Point) : W.FunctionField :=
  secantLine W P Q / verticalLine W (P + Q)
```

with the caveat that the numerator should be the tangent line when `P = Q`; the `secantLine` above already handles that by branching to `tangentLine` when the affine coordinates agree.
