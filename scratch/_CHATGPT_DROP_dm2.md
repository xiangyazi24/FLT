# Q2046 (dm2): Miller evaluation at an affine point

Date: 2026-06-28.

Question: for `W : WeierstrassCurve.Affine K`, how should we evaluate elements of

```lean
W.CoordinateRing = K[X][Y] / (W.polynomial)
W.FunctionField = FractionRing W.CoordinateRing
```

at an affine point `P = (xP, yP)`?

## Short answer

Mathlib has the bivariate polynomial evaluation API and a quotient-at-point equivalence, but I did **not** find a named direct map

```lean
W.CoordinateRing →+* K
```

such as `CoordinateRing.eval`.  The correct direct definition is to use `AdjoinRoot.lift`, because

```lean
W.CoordinateRing = AdjoinRoot W.polynomial
```

and `W.Equation xP yP` is exactly the statement that `W.polynomial` vanishes at `(xP,yP)`.

For the fraction field, there is **no total evaluation homomorphism**

```lean
W.FunctionField →+* K
```

at a point.  Evaluation of a rational function is partial: a representative `num / den` may be evaluated only when `den(P) ≠ 0`.

## Relevant Mathlib API

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
```

In `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, Mathlib defines:

```lean
abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing
```

and wraps the quotient map as:

```lean
CoordinateRing.mk W
-- type: K[X][Y] →+* W.CoordinateRing
```

For bivariate polynomials, `Mathlib.Algebra.Polynomial.Bivariate` provides:

```lean
Polynomial.evalEval x y p
-- p(x,y)

Polynomial.evalEvalRingHom x y
-- type: K[X][Y] →+* K
```

and the key bridge:

```lean
Polynomial.eval₂_evalRingHom
-- eval₂ (Polynomial.evalRingHom x) = Polynomial.evalEval x
```

Mathlib also has a nearby quotient API:

```lean
CoordinateRing.XYIdeal W x ypoly
CoordinateRing.quotientXYIdealEquiv
```

where

```lean
CoordinateRing.quotientXYIdealEquiv
  (h : (W.polynomial.eval ypoly).eval x = 0) :
  (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x ypoly) ≃ₐ[K] K
```

This is useful, but it is an equivalence after quotienting by the maximal ideal
`⟨X - x, Y - ypoly(X)⟩`; it is not itself a named direct evaluation map from `W.CoordinateRing` to `K`.

## Recommended direct coordinate-ring evaluation map

Use `AdjoinRoot.lift`.  This is the cleanest definition.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
namespace MillerEval

universe u

variable {K : Type u} [Field K]
variable (W : Affine K)
variable {xP yP : K}

/-- Evaluation of coordinate-ring functions at the affine point `(xP,yP)`. -/
noncomputable def evalCR (hP : W.Equation xP yP) : W.CoordinateRing →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom xP) yP (by
    -- Goal:
    --   W.polynomial.eval₂ (Polynomial.evalRingHom xP) yP = 0
    -- while `hP` is:
    --   W.polynomial.evalEval xP yP = 0
    simpa [WeierstrassCurve.Affine.Equation, Polynomial.eval₂_evalRingHom] using hP)

/-- Evaluation commutes with the quotient map. -/
@[simp]
theorem evalCR_mk (hP : W.Equation xP yP) (p : K[X][Y]) :
    evalCR W hP (CoordinateRing.mk W p) = p.evalEval xP yP := by
  simp [evalCR, Polynomial.eval₂_evalRingHom]

/-- The class of `X - a` evaluates to `xP - a`. -/
@[simp]
theorem evalCR_XClass (hP : W.Equation xP yP) (a : K) :
    evalCR W hP (CoordinateRing.XClass W a) = xP - a := by
  simp [evalCR, CoordinateRing.XClass, Polynomial.eval₂_evalRingHom, Polynomial.evalEval]

/-- The class of `Y - g(X)` evaluates to `yP - g(xP)`. -/
@[simp]
theorem evalCR_YClass (hP : W.Equation xP yP) (g : K[X]) :
    evalCR W hP (CoordinateRing.YClass W g) = yP - g.eval xP := by
  simp [evalCR, CoordinateRing.YClass, Polynomial.eval₂_evalRingHom, Polynomial.evalEval]

/-- Explicit `a(X) + b(X)Y` constructor. -/
noncomputable def mkPQ (p q : K[X]) : W.CoordinateRing :=
  CoordinateRing.mk W (C p + C q * (Y : K[X][Y]))

/-- Evaluation of `a(X) + b(X)Y` at `(xP,yP)`. -/
@[simp]
theorem evalCR_mkPQ (hP : W.Equation xP yP) (p q : K[X]) :
    evalCR W hP (mkPQ W p q) = p.eval xP + q.eval xP * yP := by
  simp [mkPQ, evalCR, Polynomial.eval₂_evalRingHom, Polynomial.evalEval]

end MillerEval
end Affine
end WeierstrassCurve
```

The theorem `evalCR_mkPQ` is the Lean version of the rule

```text
(a(X) + b(X)Y)(xP,yP) = a(xP) + b(xP)yP.
```

## Alternative definition via `quotientXYIdealEquiv`

This is also mathematically clean, but slightly heavier in Lean.  It factors evaluation as

```text
F[W] → F[W] / ⟨X - xP, Y - yP⟩ ≃ F.
```

Skeleton:

```lean
noncomputable def evalCRViaQuotient
    {K : Type u} [Field K]
    (W : WeierstrassCurve.Affine K)
    {xP yP : K} (hP : W.Equation xP yP) :
    W.CoordinateRing →ₐ[K] K :=
  ((CoordinateRing.quotientXYIdealEquiv
      (W' := W) (x := xP) (y := (C yP : K[X]))
      (by
        -- Goal: (W.polynomial.eval (C yP)).eval xP = 0
        -- This is the same as `W.polynomial.evalEval xP yP = 0`.
        simpa [WeierstrassCurve.Affine.Equation, Polynomial.evalEval] using hP)).toAlgHom).comp
    (Ideal.Quotient.mkₐ K (CoordinateRing.XYIdeal W xP (C yP : K[X])))
```

I would use the `AdjoinRoot.lift` definition first.  It gives the direct simp lemma on `CoordinateRing.mk W p` immediately.

## Why there is no total function-field evaluation map

`W.FunctionField` is a localization/fraction ring of `W.CoordinateRing`.  A homomorphism out of a localization exists only when every localized denominator maps to a unit.  For `FractionRing W.CoordinateRing`, the denominators are all nonzero elements of `W.CoordinateRing`.

At the point `(xP,yP)`, the nonzero coordinate-ring element

```lean
CoordinateRing.XClass W xP    -- the class of X - xP
```

is nonzero by

```lean
CoordinateRing.XClass_ne_zero xP
```

but it evaluates to zero:

```lean
by simpa using evalCR_XClass (W := W) hP xP
-- evalCR W hP (CoordinateRing.XClass W xP) = 0
```

Therefore the coordinate-ring evaluation map cannot be extended to a ring homomorphism

```lean
W.FunctionField →+* K
```

because the fraction field inverts `X - xP`, while evaluation at `P` sends `X - xP` to `0`.

## Recommended representation for partial rational-function evaluation

For Miller evaluation, do not try to define a total evaluator on `W.FunctionField`.  Instead, carry an explicit numerator and denominator and require the denominator to be nonzero at the evaluation point.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
namespace MillerEval

universe u

variable {K : Type u} [Field K]
variable (W : Affine K)
variable {xP yP : K}

/-- Evaluation of an explicit fraction `num / den` at an affine point. -/
noncomputable def evalFractionAt
    (hP : W.Equation xP yP)
    (num den : W.CoordinateRing)
    (hdenP : evalCR W hP den ≠ 0) : K :=
  evalCR W hP num / evalCR W hP den

/-- A presentation of a rational function that is evaluable at `(xP,yP)`. -/
structure FractionPresentationAt
    (hP : W.Equation xP yP)
    (f : W.FunctionField) where
  num : W.CoordinateRing
  den : W.CoordinateRing
  den_ne_zero : den ≠ 0
  den_eval_ne_zero : evalCR W hP den ≠ 0
  eq_mk :
    f = IsLocalization.mk' W.FunctionField num
      ⟨den, mem_nonZeroDivisors_iff_ne_zero.mpr den_ne_zero⟩

namespace FractionPresentationAt

/-- Evaluate a rational function from a denominator-nonvanishing presentation. -/
noncomputable def value
    {hP : W.Equation xP yP} {f : W.FunctionField}
    (s : FractionPresentationAt W hP f) : K :=
  evalCR W hP s.num / evalCR W hP s.den

end FractionPresentationAt
end MillerEval
end Affine
end WeierstrassCurve
```

Later, prove independence of presentation.  The proof path is:

1. Use `IsLocalization.mk'_eq_iff_eq'` to turn equality of two fractions into a cross-multiplication equality in `W.CoordinateRing`.
2. Apply `evalCR W hP`, a ring homomorphism, to that equality.
3. Divide by the two nonzero evaluated denominators.

A statement to add later:

```lean
theorem FractionPresentationAt.value_eq
    {K : Type u} [Field K]
    (W : WeierstrassCurve.Affine K)
    {xP yP : K} {hP : W.Equation xP yP}
    {f : W.FunctionField}
    (s t : FractionPresentationAt W hP f) :
    s.value W = t.value W := by
  -- Use `s.eq_mk`, `t.eq_mk`, `IsLocalization.mk'_eq_iff_eq'`,
  -- then apply `evalCR W hP` and field division.
  sorry
```

## A deliberately simple Miller-loop policy

For the current Miller layer, keep the evaluated loop separate from the symbolic function-field loop.

Symbolic functions:

```lean
lineCR     : W.CoordinateRing
verticalCR : W.CoordinateRing
lineFF     : W.FunctionField := algebraMap _ _ lineCR
verticalFF : W.FunctionField := algebraMap _ _ verticalCR
```

Evaluated functions:

```lean
lineValue     := evalCR W hP lineCR
verticalValue := evalCR W hP verticalCR
```

Then each Miller step should require:

```lean
hvertical : verticalValue ≠ 0
```

and multiply the accumulator by:

```lean
lineValue / verticalValue
```

This avoids pretending that evaluation is a total map on `K(E)`.  It also matches the mathematics: rational functions are evaluated at points only away from their poles.

## API checklist

Use these names:

```lean
CoordinateRing.mk W
CoordinateRing.XClass W x
CoordinateRing.YClass W g
CoordinateRing.XClass_ne_zero
CoordinateRing.YClass_ne_zero
CoordinateRing.quotientXYIdealEquiv
CoordinateRing.XYIdeal

Polynomial.evalEval
Polynomial.evalEvalRingHom
Polynomial.eval₂_evalRingHom
Polynomial.aevalAeval
Polynomial.coe_aevalAeval_eq_evalEval

AdjoinRoot.lift
AdjoinRoot.lift_mk
AdjoinRoot.liftAlgHom

IsLocalization.mk'
IsLocalization.mk'_eq_iff_eq'
IsFractionRing.div_surjective
```
