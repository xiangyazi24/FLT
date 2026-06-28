# Q2027 (dm2): Miller function core for a short Weierstrass curve

Date searched/written: 2026-06-28.

Goal: give Lean 4 definitions for the Miller-function core behind the Weil pairing, without proving the divisor identities yet.

This uses Mathlib's existing Weierstrass-curve affine API:

* `WeierstrassCurve.Affine.CoordinateRing := AdjoinRoot W.polynomial`;
* `WeierstrassCurve.Affine.FunctionField := FractionRing W.CoordinateRing`;
* `CoordinateRing.mk : K[X][Y] →+* W.CoordinateRing`;
* `CoordinateRing.XClass W x`, representing `X - x` in the coordinate ring;
* `linePolynomial x y ℓ : K[X]`, representing `ℓ * (X - x) + y`;
* `W.slope x₁ x₂ y₁ y₂`, Mathlib's secant/tangent slope;
* `W.Point`, the nonsingular affine point type with the point at infinity.

Important convention: the total function `ellCoord W P Q` below returns `1` if either input is `O`, returns the vertical line if `Q = -P`, and otherwise returns the usual affine line

```text
Y - (λ * (X - x_P) + y_P).
```

This is the convention needed for a total Miller core.  The divisor-correctness theorem is not included here; the intended future theorem is

```text
div(g(P,Q)) = [P] + [Q] - [P+Q] - [O]
```

where `g(P,Q) = ell(P,Q) / v(P+Q)`.

## Lean 4 file

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Bits

/-!
# Miller-function core for Weierstrass curves

This file defines the rational functions used in the Miller loop for a short
Weierstrass curve `y^2 = x^3 + A*x + B`.

The definitions are deliberately computational and do **not** prove the divisor
formulae yet.  They live in the function field

  `W.FunctionField = FractionRing W.CoordinateRing`.

The main definitions are:

* `shortCurve A B` for `y^2 = x^3 + A*x + B`;
* `lineFunctionFF W x y λ` for `Y - (λ*(X-x)+y)`;
* `verticalFunctionFF W x` for `X - x`;
* `ellFF W P Q`, the total line/tangent/vertical function through `P,Q`;
* `millerFunction W P m`, the binary Miller-loop accumulator for `f_{m,P}`.
-/

namespace WeierstrassCurve
namespace Affine
namespace MillerCore

open Polynomial
open scoped Polynomial.Bivariate

universe u

variable {K : Type u} [Field K] [DecidableEq K]

noncomputable section

/-- The short Weierstrass curve `y^2 = x^3 + A*x + B`. -/
def shortCurve (A B : K) : Affine K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

/-- The point type for the short curve `y^2 = x^3 + A*x + B`. -/
abbrev ShortPoint (A B : K) : Type u :=
  (shortCurve (K := K) A B).Point

/-- The affine coordinate ring of the short curve `y^2 = x^3 + A*x + B`. -/
abbrev ShortCoordinateRing (A B : K) : Type u :=
  (shortCurve (K := K) A B).CoordinateRing

/-- The function field of the short curve `y^2 = x^3 + A*x + B`. -/
abbrev ShortFunctionField (A B : K) : Type u :=
  (shortCurve (K := K) A B).FunctionField

/-- Coerce a coordinate-ring element to the function field. -/
def coordToFF (W : Affine K) (z : W.CoordinateRing) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField z

/-- Send a bivariate polynomial to the function field of `W`. -/
def bivarToFF (W : Affine K) (F : K[X][Y]) : W.FunctionField :=
  coordToFF W (CoordinateRing.mk W F)

/-- The coordinate-ring class of `Y - (λ * (X - xP) + yP)`. -/
def lineFunctionCoord (W : Affine K) (xP yP λ : K) : W.CoordinateRing :=
  CoordinateRing.mk W (Y - C (linePolynomial xP yP λ))

/-- The function-field element `Y - (λ * (X - xP) + yP)`. -/
def lineFunctionFF (W : Affine K) (xP yP λ : K) : W.FunctionField :=
  coordToFF W (lineFunctionCoord W xP yP λ)

/-- The coordinate-ring class of the vertical function `X - xP`. -/
def verticalFunctionCoord (W : Affine K) (xP : K) : W.CoordinateRing :=
  CoordinateRing.XClass W xP

/-- The function-field element `X - xP`. -/
def verticalFunctionFF (W : Affine K) (xP : K) : W.FunctionField :=
  coordToFF W (verticalFunctionCoord W xP)

/-- Extract the `x`-coordinate of a finite affine point, returning `none` at infinity. -/
def pointX? {W : Affine K} : W.Point → Option K
  | .zero => none
  | .some x _ _ => some x

/-- Extract the `y`-coordinate of a finite affine point, returning `none` at infinity. -/
def pointY? {W : Affine K} : W.Point → Option K
  | .zero => none
  | .some _ y _ => some y

/--
The total line/tangent/vertical function in the coordinate ring.

* If either input is `O`, this returns `1` by convention.
* If `Q = -P`, this returns the vertical line `X - xP`.
* Otherwise this returns the affine secant/tangent line
  `Y - (λ * (X - xP) + yP)` with `λ = W.slope xP xQ yP yQ`.
-/
def ellCoord (W : Affine K) : W.Point → W.Point → W.CoordinateRing
  | .zero, _ => 1
  | _, .zero => 1
  | .some xP yP _hP, .some xQ yQ _hQ =>
      if _hvertical : xP = xQ ∧ yP = W.negY xQ yQ then
        verticalFunctionCoord W xP
      else
        lineFunctionCoord W xP yP (W.slope xP xQ yP yQ)

/-- The total line/tangent/vertical function in the function field. -/
def ellFF (W : Affine K) (P Q : W.Point) : W.FunctionField :=
  coordToFF W (ellCoord W P Q)

/--
The vertical function attached to a point.  At infinity we use the total
Miller-core convention `v(O) = 1`.
-/
def verticalAtPointFF (W : Affine K) : W.Point → W.FunctionField
  | .zero => 1
  | .some x _ _ => verticalFunctionFF W x

/--
The Miller quotient

  `g(P,Q) = ell(P,Q) / v(P+Q)`.

The future divisor theorem should say

  `div(g(P,Q)) = [P] + [Q] - [P+Q] - [O]`.
-/
def millerQuotientFF (W : Affine K) (P Q : W.Point) : W.FunctionField :=
  ellFF W P Q / verticalAtPointFF W (P + Q)

/-- State of the Miller loop: current multiple `R` and current function accumulator `f`. -/
structure MillerState (W : Affine K) where
  R : W.Point
  f : W.FunctionField

/-- Initial Miller state for the left-to-right binary loop: `R = P`, `f = 1`. -/
def initialState (W : Affine K) (P : W.Point) : MillerState W where
  R := P
  f := 1

/-- Doubling step: `(R,f) ↦ (2R, f^2 * g(R,R))`. -/
def millerDouble (W : Affine K) (s : MillerState W) : MillerState W where
  R := s.R + s.R
  f := s.f ^ 2 * millerQuotientFF W s.R s.R

/--
One left-to-right Miller step for a binary digit after the leading `1`.

After doubling, if the next bit is `1`, multiply by `g(2R,P)` and update
`R := 2R + P`; if it is `0`, keep the doubled state.
-/
def millerStepBit (W : Affine K) (P : W.Point) (b : Bool) (s : MillerState W) : MillerState W :=
  let s₂ := millerDouble W s
  if b then
    { R := s₂.R + P
      f := s₂.f * millerQuotientFF W s₂.R P }
  else
    s₂

/--
Binary digits used by the Miller loop: most-significant first, with the leading
`1` removed.

Mathlib's `Nat.bits m` is least-significant first, so we reverse it and drop the
leading most-significant bit.
-/
def millerBits (m : ℕ) : List Bool :=
  (Nat.bits m).reverse.drop 1

/-- Run the Miller loop over an explicit list of bits. -/
def millerLoopFromBits (W : Affine K) (P : W.Point) (bits : List Bool) : MillerState W :=
  bits.foldl (fun s b => millerStepBit W P b s) (initialState W P)

/--
The Miller function accumulator `f_{m,P}` computed from the binary expansion of
`m`.

For `m = 1`, this returns `1`, as expected from the normalization `f_{1,P}=1`.
The case `m = 0` is not used in the Weil-pairing construction; with the present
total convention it also returns the initial accumulator `1`.
-/
def millerFunction (W : Affine K) (P : W.Point) (m : ℕ) : W.FunctionField :=
  (millerLoopFromBits W P (millerBits m)).f

/-- Same function, with an explicit order hypothesis carried for downstream APIs. -/
def millerFunctionOfOrder (W : Affine K) (P : W.Point) (m : ℕ)
    (_hP : m • P = 0) : W.FunctionField :=
  millerFunction W P m

/-- Same function, with an exact-order hypothesis carried for downstream APIs. -/
def millerFunctionOfExactOrder (W : Affine K) (P : W.Point) (m : ℕ)
    (_hP : addOrderOf P = m) : W.FunctionField :=
  millerFunction W P m

/-!
## Short-curve convenience wrappers

These wrappers specialize the definitions above to `y^2 = x^3 + A*x + B`.
-/

/-- Line function on the short curve `y^2 = x^3 + A*x + B`. -/
def shortEllFF (A B : K) (P Q : ShortPoint (K := K) A B) : ShortFunctionField (K := K) A B :=
  ellFF (shortCurve (K := K) A B) P Q

/-- Vertical function at a point on the short curve `y^2 = x^3 + A*x + B`. -/
def shortVerticalAtPointFF (A B : K) (P : ShortPoint (K := K) A B) :
    ShortFunctionField (K := K) A B :=
  verticalAtPointFF (shortCurve (K := K) A B) P

/-- Miller quotient on the short curve `y^2 = x^3 + A*x + B`. -/
def shortMillerQuotientFF (A B : K) (P Q : ShortPoint (K := K) A B) :
    ShortFunctionField (K := K) A B :=
  millerQuotientFF (shortCurve (K := K) A B) P Q

/-- Miller function on the short curve `y^2 = x^3 + A*x + B`. -/
def shortMillerFunction (A B : K) (P : ShortPoint (K := K) A B) (m : ℕ) :
    ShortFunctionField (K := K) A B :=
  millerFunction (shortCurve (K := K) A B) P m

end

end MillerCore
end Affine
end WeierstrassCurve
```

## Notes for the next round

The core above is only the computational skeleton.  The next formal targets are:

1. define finite divisors supported on `W.Point`;
2. define evaluation of a function-field element at such divisors where no zero/pole conflict occurs;
3. prove the divisor identity for `millerQuotientFF`;
4. prove the loop invariant

```text
div(f_{n,P}) = n[P] - [nP] - (n-1)[O];
```

5. define the Weil pairing by a normalized Miller evaluation and then connect it to the abstract `WeilPairingData` interface from Q2012.

The definitions are intentionally total at `O` and in vertical cases so that the Miller loop can be written without partial functions.  Correctness theorems should state the exact mathematical hypotheses under which those total conventions agree with the divisor-theoretic formulas.
