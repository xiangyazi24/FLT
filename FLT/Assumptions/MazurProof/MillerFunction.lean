import Mathlib

/-!
# Miller Function Definitions for the Weil Pairing

This file defines the Miller functions needed to compute the Weil pairing on an
affine Weierstrass curve `W` over a field `K`.

## Main definitions

* `verticalFunction` — the vertical line `X - x_P`, as an element of `W.FunctionField`
* `lineFunction` — the line through two points (tangent, secant, or vertical),
  as an element of `W.FunctionField`
* `gFunction` — the correction factor `lineFunction(P,Q) / verticalFunction(P+Q)`
* `millerLoop` — the double-and-add Miller accumulator computing `f_{m,P}`
* `weilPairing` — `e_m(P,Q) = f_{m,P}(Q+S)/f_{m,P}(S) · f_{m,Q}(S)/f_{m,Q}(P+S)`

## Implementation notes

All proofs are `sorry`.  The goal is to establish the correct type signatures and
definitions (the architectural skeleton).  The function-field evaluation map
`evalAtPoint` is axiomatized.

The coordinate ring `W.CoordinateRing` is `K[X,Y]/(W)` and the function field
`W.FunctionField` is its fraction field `Frac(K[X,Y]/(W))`.

## References

* Miller, "The Weil Pairing, and Its Efficient Calculation" (2004)
* Silverman, *The Arithmetic of Elliptic Curves*, Ch. III §8
-/

noncomputable section

namespace WeierstrassCurve.Affine.MillerFunction

universe u

/-! ## Binary expansion helper -/

/-- Binary digits of a natural number, most-significant bit first.
Returns `[]` for `m = 0`. -/
def bitsMSB (m : ℕ) : List Bool :=
  if _h : m = 0 then []
  else bitsMSB (m / 2) ++ [m % 2 == 1]
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

variable {K : Type u} [Field K] [DecidableEq K]

/-! ## Coordinate-ring embedding -/

section Helpers

variable (W : Affine K)

/-- Embed a coordinate-ring element into the function field `K(W)`.
This is the canonical `algebraMap : W.CoordinateRing →+* W.FunctionField`. -/
def toFunctionField (f : CoordinateRing W) : FunctionField W :=
  algebraMap (CoordinateRing W) (FunctionField W) f

end Helpers

/-! ## Line and vertical functions -/

section LineFunctions

variable (W : Affine K)

/-- The vertical line through a point, as an element of the function field.

For an affine point `P = (x_P, y_P)`, this is the image of `X - x_P`
in `K(W) = Frac(K[X,Y]/(W))`.  For the point at infinity `O`, it is `1`.

The divisor identity (to be proved separately) is:
  `div(verticalFunction P) = [P] + [-P] - 2[O]`. -/
def verticalFunction : Point W → FunctionField W
  | 0 => 1
  | .some x _ _ => toFunctionField W (CoordinateRing.XClass W x)

/-- The line through two points, as an element of the function field.

Branch convention (matching the Miller-loop identity requirements):
* If either point is `O`, return `1`.
* If the two affine points are additive inverses
  (`x₁ = x₂` and `y₁ = W.negY x₂ y₂`), return the vertical line `X - x₁`.
* Otherwise, return `Y - y₁ - λ(X - x₁)` where `λ = W.slope x₁ x₂ y₁ y₂`.
  Mathlib's `slope` handles both the tangent case (`P = Q`, non-2-torsion)
  and the secant case (`P ≠ Q`, `x₁ ≠ x₂`).

The divisor identity is:
  `div(lineFunction P Q) = [P] + [Q] + [-(P+Q)] - 3[O]`. -/
def lineFunction (P Q : Point W) : FunctionField W := by
  classical
  exact
    match P, Q with
    | 0, _ => 1
    | _, 0 => 1
    | .some x₁ y₁ _, .some x₂ y₂ _ =>
        if x₁ = x₂ ∧ y₁ = negY W x₂ y₂ then
          -- Vertical case: P + Q = O
          toFunctionField W (CoordinateRing.XClass W x₁)
        else
          -- Tangent or secant case
          toFunctionField W
            (CoordinateRing.YClass W (linePolynomial x₁ y₁ (slope W x₁ x₂ y₁ y₂)))

end LineFunctions

/-! ## Miller correction factor and loop -/

section MillerLoop

variable (W : Affine K) [IsDomain (CoordinateRing W)]

/-- The Miller correction factor `g(P, Q) = lineFunction(P, Q) / verticalFunction(P + Q)`.

The key divisor identity (to be proved separately) is:
  `div(g(P, Q)) = [P] + [Q] - [P+Q] - [O]`. -/
def gFunction (P Q : Point W) : FunctionField W :=
  lineFunction W P Q / verticalFunction W (P + Q)

/-- State of the Miller loop: the current elliptic-curve point `T = nP`
and the function-field accumulator `acc = f_{n,P}`.

Invariant (to be proved separately):
  `T = nP`  and  `div(acc) = n[P] - [nP] - (n-1)[O]`. -/
structure MillerState where
  /-- Current point on the curve, equal to `nP` after processing the
  binary prefix representing `n`. -/
  T : Point W
  /-- Function-field accumulator, equal to `f_{n,P}` after processing
  the binary prefix representing `n`. -/
  acc : FunctionField W

/-- Doubling step in the Miller loop:
  `T ↦ 2T`,  `acc ↦ acc² · g(T, T)`. -/
def doubleStep (s : MillerState W) : MillerState W where
  T := s.T + s.T
  acc := s.acc ^ 2 * gFunction W s.T s.T

/-- Addition step in the Miller loop:
  `T ↦ T + P`,  `acc ↦ acc · g(T, P)`. -/
def addStep (P : Point W) (s : MillerState W) : MillerState W where
  T := s.T + P
  acc := s.acc * gFunction W s.T P

/-- Process one bit in the MSB-first Miller loop.
Every bit first performs a doubling step; if the bit is `true`,
it then performs the addition step by `P`. -/
def stepBit (P : Point W) (bit : Bool) (s : MillerState W) : MillerState W :=
  let s₂ := doubleStep W s
  if bit then addStep W P s₂ else s₂

/-- The Miller loop: compute `f_{m,P} ∈ K(W)` via double-and-add
over the binary expansion of `m`.

The loop starts at `T = O`, `acc = 1` and processes all bits of `m`
(including the leading `1`).  The normalization conventions
  `verticalFunction(O) = 1`  and  `lineFunction(O, _) = 1`
ensure that the initial doubling step from `T = O` is harmless.

**Loop invariant** (to be proved separately):
after processing a prefix representing `n`,
  `T = nP`  and  `div(acc) = n[P] - [nP] - (n-1)[O]`.

If `P` has exact order `m`, then `T = mP = O` at the end, and
  `div(acc) = m[P] - m[O]`. -/
def millerLoop (P : Point W) (m : ℕ) : FunctionField W :=
  ((bitsMSB m).foldl (fun s bit => stepBit W P bit s)
    ({ T := 0, acc := 1 } : MillerState W)).acc

/-- Full Miller-loop state (returning both `T` and `acc`) for the
invariant proof target. -/
def millerLoopState (P : Point W) (m : ℕ) : MillerState W :=
  (bitsMSB m).foldl (fun s bit => stepBit W P bit s)
    ({ T := 0, acc := 1 } : MillerState W)

end MillerLoop

/-! ## Function-field evaluation and the Weil pairing -/

section WeilPairing

variable (W : Affine K) [IsDomain (CoordinateRing W)]

/-- Evaluate a function-field element at a point on the curve.

Mathematically, this is the ring homomorphism `ev_R : K(W) → K` defined by
  `x ↦ x_R`,  `y ↦ y_R`,
valid when the denominator of the rational function does not vanish at `R`.

The definition is axiomatized in this skeleton; it will later be constructed
from the evaluation map on the coordinate ring (sending `X ↦ x_R`, `Y ↦ y_R`)
extended to the fraction field via the universal property of localization. -/
def evalAtPoint (_f : FunctionField W) (_R : Point W) : K := by
  exact sorry

/-- The Weil pairing `e_m(P, Q)` via Miller functions with auxiliary point `S`.

  `e_m(P, Q) = (f_{m,P}(Q + S) / f_{m,P}(S)) · (f_{m,Q}(S) / f_{m,Q}(P + S))`

The auxiliary point `S` is chosen so that all four evaluations avoid the
support of the relevant divisors.  For independent generators `P, Q` of `E[m]`,
the simplified formula `(-1)^m · f_{m,P}(Q) / f_{m,Q}(P)` can be used (this
corresponds to a suitable choice of `S`). -/
def weilPairing (m : ℕ) (P Q S : Point W) : K :=
  (evalAtPoint W (millerLoop W P m) (Q + S) /
   evalAtPoint W (millerLoop W P m) S) *
  (evalAtPoint W (millerLoop W Q m) S /
   evalAtPoint W (millerLoop W Q m) (P + S))

/-! ## Properties (proof obligations, all sorry) -/

/-- The Weil pairing value is an `m`-th root of unity. -/
theorem weilPairing_pow_eq_one (m : ℕ) (hm : 0 < m) (P Q S : Point W)
    (hP : m • P = 0) (hQ : m • Q = 0) :
    weilPairing W m P Q S ^ m = 1 := by
  sorry

/-- Bilinearity in the first argument. -/
theorem weilPairing_add_left (m : ℕ) (P₁ P₂ Q S : Point W) :
    weilPairing W m (P₁ + P₂) Q S =
      weilPairing W m P₁ Q S * weilPairing W m P₂ Q S := by
  sorry

/-- Bilinearity in the second argument. -/
theorem weilPairing_add_right (m : ℕ) (P Q₁ Q₂ S : Point W) :
    weilPairing W m P (Q₁ + Q₂) S =
      weilPairing W m P Q₁ S * weilPairing W m P Q₂ S := by
  sorry

/-- The alternating property: `e_m(P, P) = 1`. -/
theorem weilPairing_self (m : ℕ) (P S : Point W) :
    weilPairing W m P P S = 1 := by
  sorry

/-- Nondegeneracy: if `P` has exact order `m`, there exists `Q` such that
`e_m(P, Q) ≠ 1`. -/
theorem weilPairing_nondegenerate (m : ℕ) (P : Point W)
    (hP : m • P = 0) (hPne : P ≠ 0) (hord : addOrderOf P = m) :
    ∃ Q S : Point W, weilPairing W m P Q S ≠ 1 := by
  sorry

end WeilPairing

/-! ## Simp lemmas for identity cases -/

section SimpLemmas

variable (W : Affine K)

omit [DecidableEq K] in
@[simp]
theorem verticalFunction_zero : verticalFunction W 0 = 1 :=
  rfl

@[simp]
theorem lineFunction_zero_left (Q : Point W) : lineFunction W 0 Q = 1 := by
  simp [lineFunction]

@[simp]
theorem lineFunction_zero_right (P : Point W) : lineFunction W P 0 = 1 := by
  cases P <;> simp [lineFunction]

end SimpLemmas

end MillerFunction
end Affine
end WeierstrassCurve
