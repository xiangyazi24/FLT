# Q2093 (dm2): Constructing `x - a` in `WeierstrassCurve.Affine.FunctionField`

Date: 2026-06-28.

## Answer

Yes: for the Miller-function layer, the coordinate-ring element representing the affine function `x - a` should be built as the class of the **inner** polynomial `X - C a`, embedded as a constant polynomial in the **outer** `Y` variable.

In the Mathlib API at the FLT-pinned Mathlib revision, you should normally use the already-packaged definition:

```lean
WeierstrassCurve.Affine.CoordinateRing.XClass W a
```

This has type:

```lean
W.CoordinateRing
```

and it is defined by Mathlib as:

```lean
noncomputable def XClass (x : R) : W'.CoordinateRing :=
  mk W' <| C <| X - C x
```

So the clean exact term for the function-field element `x - a` is:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (WeierstrassCurve.Affine.CoordinateRing.XClass W a)
```

or, inside `namespace WeierstrassCurve.Affine`, simply:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.XClass W a)
```

## Minimal Lean snippet

This is the snippet I would put near the start of `MillerFunction.lean` to sanity-check the exact term.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F]
variable (W : Affine F) (a : F)

/-- The coordinate-ring class of the affine function `x - a`. -/
def xMinusA_coord : W.CoordinateRing :=
  CoordinateRing.XClass W a

/-- The same element, expanded without using `XClass`. -/
def xMinusA_coord_expanded : W.CoordinateRing :=
  CoordinateRing.mk W
    (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a))

/-- The function-field element `x - a`. -/
def xMinusA_fun : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.XClass W a)

/-- The same function-field element, expanded all the way to `CoordinateRing.mk`. -/
def xMinusA_fun_expanded : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W
      (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a)))

end Affine
end WeierstrassCurve
```

If Lean has trouble inferring the source and target of `algebraMap`, use the fully qualified version:

```lean
def xMinusA_fun_fully_explicit
    {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) (a : F) :
    WeierstrassCurve.Affine.FunctionField W :=
  algebraMap
    (WeierstrassCurve.Affine.CoordinateRing W)
    (WeierstrassCurve.Affine.FunctionField W)
    (WeierstrassCurve.Affine.CoordinateRing.XClass W a)
```

## Why not `AdjoinRoot.mk (Polynomial.X - Polynomial.C a)`?

That expression is not the right shape.

Mathlib has:

```lean
abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing
```

and the natural quotient map is packaged as:

```lean
noncomputable abbrev CoordinateRing.mk : R[X][Y] →+* W'.CoordinateRing :=
  AdjoinRoot.mk W'.polynomial
```

The polynomial passed to `CoordinateRing.mk W` lives in:

```lean
F[X][Y]
```

that is, a polynomial in the outer variable `Y` whose coefficients are polynomials in the inner variable `X`.

Therefore:

* the affine `x` coordinate is the **inner** `Polynomial.X : F[X]`;
* to view `X - C a : F[X]` as an element of `F[X][Y]`, you must wrap it in the **outer** `Polynomial.C`;
* the outer `Polynomial.X : F[X][Y]` is the `Y` variable, not the affine `x` coordinate.

So the expanded coordinate-ring expression is:

```lean
CoordinateRing.mk W
  (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a))
```

Equivalently, using the raw `AdjoinRoot` map:

```lean
(AdjoinRoot.mk W.polynomial)
  (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a))
```

But I recommend `CoordinateRing.XClass W a`, because it is exactly the API Mathlib already provides for this element.

## Related API for Miller functions

Mathlib also provides the analogous `Y`-side class:

```lean
CoordinateRing.YClass W p
```

where `p : F[X]`. It represents the class of:

```lean
Y - C p
```

in `W.CoordinateRing`.

So for a horizontal/line-style expression `Y - p(X)` in the function field, use:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.YClass W p)
```

For a constant affine `y`-value `b : F`, use `p := Polynomial.C b`:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.YClass W (Polynomial.C b))
```

For the Miller vertical-line denominator through `x = a`, use:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.XClass W a)
```

## Practical recommendation for `MillerFunction.lean`

Define small wrappers, so the later Miller-loop code does not repeatedly expose the `AdjoinRoot`/`FractionRing` plumbing:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F]
variable (W : Affine F)

/-- Coordinate-ring class of the vertical line `x = a`, i.e. the function `x - a`. -/
def verticalCoord (a : F) : W.CoordinateRing :=
  CoordinateRing.XClass W a

/-- Function-field vertical line `x - a`. -/
def verticalFunction (a : F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (verticalCoord W a)

/-- Coordinate-ring class of `Y - p(X)`. -/
def yMinusPolynomialCoord (p : F[X]) : W.CoordinateRing :=
  CoordinateRing.YClass W p

/-- Function-field element `Y - p(X)`. -/
def yMinusPolynomialFunction (p : F[X]) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (yMinusPolynomialCoord W p)

end Affine
end WeierstrassCurve
```

Then the Miller-function code can use:

```lean
verticalFunction W a
```

for the vertical denominator `x - a`, and:

```lean
yMinusPolynomialFunction W p
```

for a numerator/line term `Y - p(X)`.

## Bottom line

The exact Lean term you want is:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.XClass W a)
```

The expanded version is:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.mk W
    (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a)))
```

Do **not** use bare `Polynomial.X - Polynomial.C a` at the outer `F[X][Y]` level: outer `Polynomial.X` is the `Y` variable. For affine `x - a`, use `C (X - C a)`, or better, Mathlib's `CoordinateRing.XClass W a`.
