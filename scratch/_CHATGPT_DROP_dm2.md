# Q2118 dm2: `evalAtPoint` for an elliptic-curve function field

Date: 2026-06-28.

## Answer

A mathematically correct evaluator for an elliptic-curve `FunctionField` is **not** a total ring-hom-valued map

```lean
def evalAtPoint (W : Affine K) (f : FunctionField W) (x_P y_P : K) : K
```

without extra hypotheses.  There are two obstructions:

1. `(x_P,y_P)` must satisfy the curve equation.  Otherwise the quotient relation in
   `CoordinateRing W = AdjoinRoot W.polynomial` is not respected.
2. A function-field element is a fraction.  Its denominator may vanish at the point, so evaluation has a pole.

The right Lean API is therefore:

* first define coordinate-ring evaluation using `AdjoinRoot.liftHom`, requiring the curve-equation proof;
* then define function-field evaluation from an explicit numerator/denominator representative whose denominator is nonzero at the point;
* optionally define a totalized convenience function returning `0` outside its domain.

Below is the concrete code shape.

## Coordinate-ring evaluation

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {K : Type*} [Field K]
variable (W : Affine K)

/-- Evaluate a polynomial in the outer `Y` variable, with coefficients in `K[X]`,
at `(x,y)`.  In notation, this evaluates an element of `K[X][Y]`. -/
def evalBivariateAt (x y : K) : K[X][X] →+* K :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom x) y

/-- The proposition that `(x,y)` lies on `W`.  This is the exact condition needed
for the evaluation map to descend through `AdjoinRoot W.polynomial`. -/
def SatisfiesEquation (x y : K) : Prop :=
  evalBivariateAt (W := W) x y W.polynomial = 0

/-- Evaluation of coordinate-ring elements at an affine point `(x,y)` satisfying
`W.polynomial(x,y)=0`. -/
def evalCoordAtPoint (x y : K) (hxy : W.SatisfiesEquation x y) :
    W.CoordinateRing →+* K :=
  AdjoinRoot.liftHom W.polynomial (evalBivariateAt (W := W) x y) hxy
```

Depending on the exact pinned Mathlib API, the last line may need one of these equivalent orderings:

```lean
  AdjoinRoot.liftHom (evalBivariateAt (W := W) x y) y hxy
  AdjoinRoot.liftHom W.polynomial (evalBivariateAt (W := W) x y) hxy
```

The intended term is the same: lift the ring hom from `K[X][Y]` to `K` through the quotient by `W.polynomial`.

If you have a genuine affine point `P : W.Point`, then the proof `hxy` is just `P.2` after simplification:

```lean
def evalCoordAtAffinePoint (P : W.Point) : W.CoordinateRing →+* K :=
  evalCoordAtPoint W P.x P.y (by
    simpa [SatisfiesEquation, evalBivariateAt,
      WeierstrassCurve.Affine.equation_iff] using P.2)
```

The field names may be `P.x`, `P.y` or projection names from the pinned API; adjust locally.

## Regular function-field evaluation from an explicit representative

For the function field, use a representative with denominator nonzero at the point.

```lean
/-- A representative of a function-field element that is regular at `(x,y)`. -/
structure RegularRepAt (x y : K) (hxy : W.SatisfiesEquation x y)
    (f : W.FunctionField) where
  num : W.CoordinateRing
  den : W.CoordinateRing
  den_ne_zero_at : evalCoordAtPoint W x y hxy den ≠ 0
  eq_frac :
    f = algebraMap W.CoordinateRing W.FunctionField num /
          algebraMap W.CoordinateRing W.FunctionField den

/-- Evaluation of a function-field element at `(x,y)`, given a representative whose
denominator does not vanish at `(x,y)`. -/
def evalAtPointRegular (x y : K) (hxy : W.SatisfiesEquation x y)
    (f : W.FunctionField) (r : RegularRepAt W x y hxy f) : K :=
  evalCoordAtPoint W x y hxy r.num / evalCoordAtPoint W x y hxy r.den
```

This is the clean theorem-proving API.  Later lemmas should prove that the value is independent of the chosen regular representative.

## Totalized convenience definition with the requested signature

If the file really needs exactly

```lean
def evalAtPoint (W : Affine K) (f : FunctionField W) (x_P y_P : K) : K
```

then it must make arbitrary choices at non-curve points and poles.  This version returns `0` if `(x,y)` is not on the curve or if no denominator-nonvanishing representative is provided by the chosen witness search.

```lean
/-- A totalized evaluator.  On genuine regular points it agrees with regular
function-field evaluation; outside that domain it returns `0` by convention. -/
def evalAtPoint (f : W.FunctionField) (x y : K) : K :=
  if hxy : W.SatisfiesEquation x y then
    if hrep : ∃ num den : W.CoordinateRing,
        (evalCoordAtPoint W x y hxy den ≠ 0) ∧
        f = algebraMap W.CoordinateRing W.FunctionField num /
              algebraMap W.CoordinateRing W.FunctionField den then
      let num : W.CoordinateRing := Classical.choose hrep
      let hrep1 : ∃ den : W.CoordinateRing,
          (evalCoordAtPoint W x y hxy den ≠ 0) ∧
          f = algebraMap W.CoordinateRing W.FunctionField num /
                algebraMap W.CoordinateRing W.FunctionField den :=
        Classical.choose_spec hrep
      let den : W.CoordinateRing := Classical.choose hrep1
      evalCoordAtPoint W x y hxy num / evalCoordAtPoint W x y hxy den
    else
      0
  else
    0
```

This is intentionally only a **totalized** evaluator.  The value at poles is a convention, not a mathematical evaluation.

## Recommended use in `MillerFunction.lean`

For Miller functions and Weil pairing work, use `evalAtPointRegular`, not the totalized `evalAtPoint`, in theorems.  The proof obligations you want are exactly:

```lean
hxy : W.SatisfiesEquation x y
hden : evalCoordAtPoint W x y hxy den ≠ 0
```

These are the conditions that prevent invalid evaluation at non-points and poles.

end Affine
end WeierstrassCurve
```
