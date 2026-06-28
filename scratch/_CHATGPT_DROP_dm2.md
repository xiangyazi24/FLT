# Q2052 (dm2): Miller loop structure in Lean 4

Date: 2026-06-28.

Goal: write the loop structure only.  The line/tangent/vertical functions are placeholders with `sorry`; the point is to get the binary double-and-add accumulator right.

Convention in this file:

* `W : WeierstrassCurve.Affine K`.
* `P : W.Point` is an `m`-torsion point, carried as a hypothesis `hP : m • P = 0`.
* The output lives in `W.FunctionField`, which is Mathlib's abbreviation for `FractionRing W.CoordinateRing`.
* Bits are processed **most-significant first**.
* The state starts at `T = O`, accumulator `f = 1`.
* For each bit:
  1. double: multiply by `tangentLine(T) / verticalLine(2T)`, set `T := 2T`;
  2. if the bit is `1`: multiply by `secantLine(T,P) / verticalLine(T+P)`, set `T := T+P`.

This is a total loop skeleton.  The placeholder line functions should later be replaced by the Q2027 `ell/v` functions, with conventions at `O` chosen so the first MSB step from `T = O` is harmless.

## Lean 4 code

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Bits

/-!
# Miller loop skeleton

This file only defines the double-and-add Miller-loop control flow.
The rational functions `secantLine`, `tangentLine`, and `verticalLine` are
placeholders.  Replace them later with explicit functions in
`W.FunctionField = FractionRing W.CoordinateRing`.
-/

namespace WeierstrassCurve
namespace Affine
namespace MillerLoopSkeleton

universe u

variable {K : Type u} [Field K] [DecidableEq K]

noncomputable section

/--
Placeholder for the secant line through two points, as a function in `K(W)`.

For the eventual implementation, this should be the line function through `P`
and `Q`, with total conventions at `O`.
-/
noncomputable def secantLine (W : Affine K) (_P _Q : W.Point) : W.FunctionField := by
  sorry

/--
Placeholder for the tangent line at a point, as a function in `K(W)`.

For the eventual implementation, this should be the tangent line at `P`, with a
total convention at `O`.
-/
noncomputable def tangentLine (W : Affine K) (_P : W.Point) : W.FunctionField := by
  sorry

/--
Placeholder for the vertical line through a point, as a function in `K(W)`.

For the eventual implementation, this should be `X - x(P)` for affine `P`, with
a total convention at `O`.
-/
noncomputable def verticalLine (W : Affine K) (_P : W.Point) : W.FunctionField := by
  sorry

/-- State of the Miller loop: current multiple `T` and accumulator `f`. -/
structure MillerState (W : Affine K) where
  current : W.Point
  acc : W.FunctionField

/-- Initial state: current point `O`, accumulator `1`. -/
def initialState (W : Affine K) : MillerState W where
  current := 0
  acc := 1

/-- The doubling update: multiply by `tangentLine(T) / verticalLine(2T)` and set `T := 2T`. -/
def doubleStep (W : Affine K) (s : MillerState W) : MillerState W where
  current := s.current + s.current
  acc := s.acc ^ 2 * (tangentLine W s.current / verticalLine W (s.current + s.current))

/--
The optional addition update for a `1` bit: multiply by
`secantLine(T,P) / verticalLine(T+P)` and set `T := T+P`.
-/
def addStep (W : Affine K) (P : W.Point) (s : MillerState W) : MillerState W where
  current := s.current + P
  acc := s.acc * (secantLine W s.current P / verticalLine W (s.current + P))

/--
Process one binary digit in the MSB-first Miller loop.

Every digit first performs a doubling step.  If the digit is `true`, it then
performs the addition step by `P`; if the digit is `false`, it keeps the doubled
state.
-/
def stepBit (W : Affine K) (P : W.Point) (bit : Bool) (s : MillerState W) : MillerState W :=
  let s₂ := doubleStep W s
  if bit then addStep W P s₂ else s₂

/--
Binary digits of `m`, most-significant first.

Mathlib's `Nat.bits m` is least-significant first, so we reverse it.
For `m = 0`, this returns `[]`.
-/
def bitsMSB (m : ℕ) : List Bool :=
  (Nat.bits m).reverse

/-- Run the Miller loop over an explicit list of MSB-first bits. -/
def loopFromBits (W : Affine K) (P : W.Point) (bits : List Bool) : MillerState W :=
  bits.foldl (fun s bit => stepBit W P bit s) (initialState W)

/-- Run the Miller loop over the binary expansion of `m`. -/
def loopState (W : Affine K) (P : W.Point) (m : ℕ) : MillerState W :=
  loopFromBits W P (bitsMSB m)

/--
The Miller-loop accumulator for a point `P` satisfying `m • P = O`.

The hypothesis is carried for the API and future correctness theorem; the loop
itself only needs `P` and `m`.
-/
def millerLoopFunction (W : Affine K) (P : W.Point) (m : ℕ)
    (_hP : m • P = 0) : W.FunctionField :=
  (loopState W P m).acc

/--
A variant returning both the final multiple and the accumulator.

Future invariant target:
if the processed prefix represents `n`, then `current = n • P` and
`acc = f_{n,P}` with divisor `n[P] - [nP] - (n-1)[O]`.
-/
def millerLoopStateOfOrder (W : Affine K) (P : W.Point) (m : ℕ)
    (_hP : m • P = 0) : MillerState W :=
  loopState W P m

/-!
## Recursive spelling

The fold-based implementation above is usually easiest to use.  This recursive
version is definitionally equivalent in spirit and may be more convenient for
induction on the bit list.
-/

def loopFromBitsRec (W : Affine K) (P : W.Point) : List Bool → MillerState W → MillerState W
  | [], s => s
  | bit :: bits, s => loopFromBitsRec W P bits (stepBit W P bit s)

/-- Recursive loop over the binary expansion of `m`. -/
def loopStateRec (W : Affine K) (P : W.Point) (m : ℕ) : MillerState W :=
  loopFromBitsRec W P (bitsMSB m) (initialState W)

/-- Recursive Miller-loop accumulator with the torsion hypothesis carried. -/
def millerLoopFunctionRec (W : Affine K) (P : W.Point) (m : ℕ)
    (_hP : m • P = 0) : W.FunctionField :=
  (loopStateRec W P m).acc

end

end MillerLoopSkeleton
end Affine
end WeierstrassCurve
```

## Notes

The loop above processes all bits including the leading `1`, because the state starts at `O`.  The first step therefore computes

```text
T = 2O + P = P
```

for the leading bit.  The placeholder functions must eventually satisfy the total conventions

```text
tangentLine(O) / verticalLine(O) = 1,
secantLine(O,P) / verticalLine(P) = 1,
```

or an equivalent normalization, so that the first step does not introduce a spurious factor.

If instead one starts with `T = P`, then the usual implementation drops the leading bit.  That is the Q2027 style.  This file follows the user-requested `T = O` convention.
