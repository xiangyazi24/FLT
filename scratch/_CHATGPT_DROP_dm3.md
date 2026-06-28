# Q2113 dm3

I attempted to read `FLT/Assumptions/MazurProof/MillerFunction.lean` on branch `ai-scratch`, but the GitHub connector returned `404 Not Found`; repo search also found no hits for `MillerFunction`, `evalAtPoint`, `verticalFunction`, or `lineFunction`.

Because the source file is not visible through the connector, I could not verify an exact patch against the local definitions.  The main conclusion is: evaluation is total on `W.CoordinateRing`, but not total on `W.FunctionField` without a regularity/non-pole hypothesis.

Concrete snippets to try once the file is visible:

```lean
noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F]
variable (W : Affine F)

-- Evaluate the outer Y-polynomial with coefficients in F[X] at P=(x,y).
def evalBivariateAtPoint (P : W.Point) : F[X][X] →+* F :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom P.x) P.y

-- Coordinate-ring evaluation.  The lift proof is exactly the point equation.
def evalCoordAtPoint (P : W.Point) : W.CoordinateRing →+* F :=
  AdjoinRoot.liftHom W.polynomial (evalBivariateAtPoint W P) (by
    simpa [evalBivariateAtPoint, WeierstrassCurve.Affine.equation_iff] using P.2)

end Affine
end WeierstrassCurve
```

For the O-case simplification holes, if the definitions return `1` at `0`, the replacements are:

```lean
@[simp] theorem verticalFunction_zero :
    verticalFunction W 0 = 1 := by
  simp [verticalFunction]

@[simp] theorem lineFunction_zero_left (P : W.Point) :
    lineFunction W 0 P = 1 := by
  simp [lineFunction]

@[simp] theorem lineFunction_zero_right (P : W.Point) :
    lineFunction W P 0 = 1 := by
  simp [lineFunction]
```

The true Weil-pairing properties, including additivity, self-pairing, power order, and nondegeneracy, are hard theorem seams unless the file stores them as fields of an abstract structure.
