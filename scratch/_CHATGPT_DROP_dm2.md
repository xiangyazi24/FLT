# Q2122 (dm2): `MillerFunction.lean` sorries and concrete replacements

Date: 2026-06-28.

Source inspected:

```text
repo:   xiangyazi24/FLT
branch: ai-scratch
file:   FLT/Assumptions/MazurProof/MillerFunction.lean
```

## Current sorry count

The pushed file currently has **6 literal `sorry`s**, not 8.

They are:

```text
line 198: evalAtPoint
line 221: weilPairing_pow_eq_one
line 227: weilPairing_add_left
line 233: weilPairing_add_right
line 238: weilPairing_self
line 245: weilPairing_nondegenerate
```

The three identity simp lemmas at the bottom are already closed:

```lean
@[simp]
theorem verticalFunction_zero : verticalFunction W 0 = 1 :=
  rfl

@[simp]
theorem lineFunction_zero_left (Q : Point W) : lineFunction W 0 Q = 1 := by
  simp [lineFunction]

@[simp]
theorem lineFunction_zero_right (P : Point W) : lineFunction W P 0 = 1 := by
  cases P <;> simp [lineFunction]
```

So there are no remaining simp-lemma sorries to replace in the current pushed file.

## Important obstruction

A mathematically correct total ring-hom-style evaluator

```lean
FunctionField W → K
```

cannot be constructed from point evaluation on `CoordinateRing W` without a non-pole hypothesis.  The reason is that `FunctionField W = FractionRing (CoordinateRing W)`, and extending a ring hom from a domain to its fraction field via `IsFractionRing.lift` requires the coordinate-ring map to be injective, equivalently that every nonzero denominator maps to a nonzero value.  Point evaluation is not injective: for example, `X - x_R` is a nonzero coordinate-ring element but evaluates to `0` at a point with `x`-coordinate `x_R`.

Therefore, the best honest replacement for the `evalAtPoint` sorry in the current skeleton is either:

1. a **totalized chosen-representative evaluator** that closes the definition but should not be used to prove the final Weil-pairing laws; or
2. a redesigned evaluator with an explicit numerator/denominator representative plus a proof that the denominator does not vanish at the point.

Since the requested file currently has the total signature

```lean
def evalAtPoint (_f : FunctionField W) (_R : Point W) : K
```

option (1) is the only way to replace that `sorry` without changing downstream type signatures.

## Replacement code for the `evalAtPoint` sorry

Replace the current block

```lean
/-- Evaluate a function-field element at a point on the curve.
...
-/
def evalAtPoint (_f : FunctionField W) (_R : Point W) : K := by
  exact sorry
```

with the following code.

```lean
/-- Evaluate a coordinate-ring element at an affine nonsingular point.

This is the honest quotient-level evaluation map.  The proof obligation for
`AdjoinRoot.lift` is exactly the curve equation contained in `hxy : W.Nonsingular x y`.

Mathlib's `CoordinateRing W` is `AdjoinRoot W.polynomial`, where the base ring is
`K[X]` and the adjoined/root variable is the outer `Y`.  So we evaluate the base
`K[X]` by `Polynomial.evalRingHom x`, and send the root/outer variable to `y`. -/
private def evalCoordinateAtAffine (x y : K) (hxy : W.Nonsingular x y) :
    CoordinateRing W →+* K :=
  AdjoinRoot.lift (f := W.polynomial) (Polynomial.evalRingHom x) y (by
    simpa [WeierstrassCurve.Affine.Equation, Polynomial.eval₂_evalRingHom] using hxy.1)

/-- Totalized evaluation of a function-field element at an affine nonsingular point.

This chooses some fraction representative `num / den` using the fraction-field
surjectivity theorem and returns `ev(num) / ev(den)`.

WARNING: this closes the skeleton definition, but it is not the final mathematical
API for Weil-pairing evaluation, because the result depends on the chosen representative
when the chosen denominator evaluates to zero.  The final API should carry a non-pole
hypothesis or an explicit regular representative. -/
private def evalFunctionFieldAtAffine (f : FunctionField W)
    (x y : K) (hxy : W.Nonsingular x y) : K := by
  classical
  let ev : CoordinateRing W →+* K := evalCoordinateAtAffine W x y hxy
  let hfrac : ∃ num den : CoordinateRing W,
      den ∈ nonZeroDivisors (CoordinateRing W) ∧
        algebraMap (CoordinateRing W) (FunctionField W) num /
          algebraMap (CoordinateRing W) (FunctionField W) den = f :=
    IsFractionRing.div_surjective (A := CoordinateRing W) (K := FunctionField W) f
  let num : CoordinateRing W := Classical.choose hfrac
  let hden := Classical.choose_spec hfrac
  let den : CoordinateRing W := Classical.choose hden
  exact ev num / ev den

/-- Evaluate a function-field element at a point on the curve.

For affine points this uses the totalized fraction-representative evaluator above.
For the point at infinity, this skeleton returns `0`.  A final divisor-aware API should
replace this with a partial/regular evaluation at `O`. -/
def evalAtPoint (f : FunctionField W) : Point W → K
  | 0 => 0
  | .some x y hxy => evalFunctionFieldAtAffine W f x y hxy
```

If the named-argument call to `IsFractionRing.div_surjective` does not elaborate on the pinned branch, use the following variant for the `hfrac` line:

```lean
  let hfrac : ∃ num den : CoordinateRing W,
      den ∈ nonZeroDivisors (CoordinateRing W) ∧
        algebraMap (CoordinateRing W) (FunctionField W) num /
          algebraMap (CoordinateRing W) (FunctionField W) den = f :=
    IsFractionRing.div_surjective (CoordinateRing W) f
```

That is the same theorem with explicit positional arguments.

## If `AdjoinRoot.lift` elaboration needs a more explicit proof

The only slightly fragile part is the `simpa` proof in `evalCoordinateAtAffine`.  If Lean does not rewrite the `eval₂` expression to `evalEval`, use this expanded version:

```lean
private def evalCoordinateAtAffine (x y : K) (hxy : W.Nonsingular x y) :
    CoordinateRing W →+* K :=
  AdjoinRoot.lift (f := W.polynomial) (Polynomial.evalRingHom x) y (by
    change Polynomial.eval₂ (Polynomial.evalRingHom x) y W.polynomial = 0
    rw [Polynomial.eval₂_evalRingHom]
    exact hxy.1)
```

The reason this works is:

```lean
hxy.1 : W.Equation x y
```

and `W.Equation x y` is definitionally:

```lean
W.polynomial.evalEval x y = 0
```

## Replacement code for simp lemmas, if needed

The current file already has these exact proofs, but if an older local branch still has sorries in the simp lemmas, use:

```lean
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
```

## Remaining 5 sorries

The remaining five theorem sorries should **not** be expected to close by unfolding definitions:

```lean
weilPairing_pow_eq_one
weilPairing_add_left
weilPairing_add_right
weilPairing_self
weilPairing_nondegenerate
```

They require the real Miller-function divisor theory:

```text
div(verticalFunction P) = [P] + [-P] - 2[O]
div(lineFunction P Q) = [P] + [Q] + [-(P+Q)] - 3[O]
div(gFunction P Q) = [P] + [Q] - [P+Q] - [O]
div(millerLoop P m) = m[P] - [mP] - (m-1)[O]
```

and a regularity/non-pole framework for all evaluations in the Weil-pairing formula.  With the current totalized evaluator, those theorem statements are not mathematically connected to the definitions strongly enough to prove.  In particular, `weilPairing_nondegenerate` is a deep theorem, not a simp/unfolding lemma.

## Recommended next API change

For the final version, replace the total evaluator with a regular-evaluation structure, for example:

```lean
structure RegularEvalData (W : Affine K) [IsDomain (CoordinateRing W)] (R : Point W) where
  num : CoordinateRing W
  den : CoordinateRing W
  den_nonzero : den ∈ nonZeroDivisors (CoordinateRing W)
  den_eval_ne_zero :
    match R with
    | 0 => True
    | .some x y hxy => evalCoordinateAtAffine W x y hxy den ≠ 0
  value : FunctionField W
  value_eq :
    algebraMap (CoordinateRing W) (FunctionField W) num /
      algebraMap (CoordinateRing W) (FunctionField W) den = value
```

Then define:

```lean
def RegularEvalData.eval (D : RegularEvalData W R) : K :=
  match R with
  | 0 => 0
  | .some x y hxy =>
      evalCoordinateAtAffine W x y hxy D.num /
        evalCoordinateAtAffine W x y hxy D.den
```

That is the right mathematical shape for later proving the Weil-pairing laws.

## Net effect

The code above replaces **1 of the 6 current sorries**: the `evalAtPoint` definition.

The simp lemmas are already closed.  The remaining 5 sorries are genuine theorem seams requiring divisor/evaluation theory, not local definitional unfolding.
