# Q2110 dm2: MillerFunction.lean sorry-reduction attempt

Date: 2026-06-28.

I attempted to read:

```text
FLT/Assumptions/MazurProof/MillerFunction.lean
```

on branch `ai-scratch` in `xiangyazi24/FLT`.  The GitHub connector returned `404 Not Found`.  Repo search also found no hits for:

```text
MillerFunction
verticalFunction
evalAtPoint
lineFunction
weilPairing_add_left
weilPairing_pow_eq_one
```

The `main..ai-scratch` file list visible to the connector does not include `MillerFunction.lean`.  So I could not patch the exact file or verify exact field names.  Below is the correct coding guidance for the reported holes.

## Classification of the 8 reported holes

The pairing property stubs are genuinely hard unless they are currently declared as axioms/fields in an abstract interface:

```text
weilPairing_pow_eq_one
weilPairing_add_left
weilPairing_add_right
weilPairing_self
weilPairing_nondegenerate
```

These are the real Weil-pairing theorems.  They require Miller divisors or a divisor-theoretic Weil pairing construction.  They cannot be proved just from the definitions of `verticalFunction` and `lineFunction`.

The simp lemmas for vertical/line wrappers should be closable if the definitions are wrappers around `CoordinateRing.XClass`, `CoordinateRing.YClass`, and `algebraMap`.

The requested `evalAtPoint` is subtler: evaluation is easy on the coordinate ring, but not total on the function field.  A `FunctionField` element is a fraction.  Evaluation at a point is only defined when the denominator does not vanish at the point.  Therefore a total function

```lean
W.FunctionField → F
```

is mathematically wrong unless it returns an option/subtype or assumes a nonzero denominator evaluation.

## Safe coordinate-ring evaluation

For a polynomial in the outer `Y` variable with coefficients in `F[X]`, evaluation at an affine point should be:

```lean
noncomputable def evalBivariateAtPoint
    {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F)
    (P : W.Point) : F[X][X] → F :=
  fun f => f.eval₂ (Polynomial.eval P.x) P.y
```

The exact point projections may be `P.x`/`P.y` or different names in the pinned API.  Adapt those names locally.

The coordinate-ring map should be a ring hom induced from that evaluator.  The proof obligation is exactly that the Weierstrass equation polynomial evaluates to zero at `P`:

```lean
noncomputable def evalCoordAtPoint
    {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F)
    (P : W.Point) : W.CoordinateRing →+* F :=
  AdjoinRoot.liftHom _ (evalBivariateAtPoint W P) (by
    -- prove W.polynomial evaluates to 0 using P.property / P.2
    -- usually: simpa [WeierstrassCurve.Affine.Equation] using P.2
    sorry)
```

This is the right theorem boundary for `evalAtPoint`: close the quotient-well-defined part by the point equation.  Do not define total evaluation on `W.FunctionField` without a denominator-nonvanishing hypothesis.

## Partial function-field evaluation

Use a subtype/option style:

```lean
structure RegularAt
    {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F)
    (P : W.Point)
    (f : W.FunctionField) : Prop where
  exists_rep : ∃ a b : W.CoordinateRing,
    f = algebraMap W.CoordinateRing W.FunctionField a /
        algebraMap W.CoordinateRing W.FunctionField b ∧
    evalCoordAtPoint W P b ≠ 0
```

The exact representation API for `FractionRing` will differ, but the point is invariant: the denominator must not vanish.

## Wrapper simp lemmas

If the file defines:

```lean
def verticalCoord (a : F) : W.CoordinateRing :=
  CoordinateRing.XClass W a

def verticalFunction (a : F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (verticalCoord W a)
```

then the simp lemmas are definitional:

```lean
@[simp] theorem verticalCoord_eq (a : F) :
    verticalCoord W a = CoordinateRing.XClass W a := rfl

@[simp] theorem verticalFunction_eq (a : F) :
    verticalFunction W a =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W a) := rfl
```

For line/Y-minus-polynomial wrappers:

```lean
def lineCoord (p : F[X]) : W.CoordinateRing :=
  CoordinateRing.YClass W p

def lineFunction (p : F[X]) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (lineCoord W p)
```

use:

```lean
@[simp] theorem lineCoord_eq (p : F[X]) :
    lineCoord W p = CoordinateRing.YClass W p := rfl

@[simp] theorem lineFunction_eq (p : F[X]) :
    lineFunction W p =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W p) := rfl
```

If the actual definitions unfold through `CoordinateRing.mk`, prove by `rfl` or:

```lean
  simp [verticalFunction, verticalCoord]
```

## Recommended source-file structure

1. Keep `verticalFunction` and `lineFunction` as small wrappers and close their simp lemmas by `rfl`/`simp`.
2. Define `evalCoordAtPoint : W.CoordinateRing →+* F` first.
3. Define function-field evaluation only with a nonvanishing denominator condition.
4. Leave the five Weil-pairing property theorems as explicit hard seams until Miller divisors or divisor theory are formalized.

Bottom line: the easy simp holes are closable; a correct coordinate-ring evaluator is closable from the point equation; total `FunctionField` evaluation and the Weil-pairing property stubs are not pure simp/API holes.
