# Q2901 (dm-codex1): shrink `affinePointAddEquivOfVariableChange` to explicit map + `map_add`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Requested namespace: `MazurProof.KubertBridgeN12`

Goal: replace the residual

```lean
axiom affinePointAddEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃+
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W))
```

by explicit coordinate maps, checked nonsingularity preservation and inverse laws, leaving only:

```lean
axiom affineVariableChangeMap_add
```

for the explicit affine coordinate map.

## API checks

Run these first in the file or in a scratch Lean file:

```lean
#check WeierstrassCurve.VariableChange
#check WeierstrassCurve.VariableChange.inv_def
#check WeierstrassCurve.variableChange_a₁
#check WeierstrassCurve.variableChange_a₂
#check WeierstrassCurve.variableChange_a₃
#check WeierstrassCurve.variableChange_a₄
#check WeierstrassCurve.variableChange_a₆
#check WeierstrassCurve.Affine.Nonsingular
#check WeierstrassCurve.Affine.Equation
#check WeierstrassCurve.Affine.evalEval_polynomial
#check WeierstrassCurve.Affine.evalEval_polynomialX
#check WeierstrassCurve.Affine.evalEval_polynomialY
#check WeierstrassCurve.Affine.Point.some
#check WeierstrassCurve.Affine.Point.some.injEq
```

If `Units.val_inv_eq_inv_val` is not found by your local import set, search with:

```bash
grep -R "val_inv_eq_inv_val" .lake/packages/mathlib/Mathlib | head
```

or replace each use by `simp` after `have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero`.

## Pasteable staged code

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.KubertBridgeN12

noncomputable section

/-! ### 1. Coordinate maps -/

/--
Forward affine point map from `W` to `C • W`.
Mathlib's variable change convention is
`X_old = u^2 X_new + r`, `Y_old = u^3 Y_new + u^2 s X_new + t`,
so the forward map on points uses the inverse coordinate formulas.
-/
private def vcNewX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  ((C.u⁻¹ : ℚ) ^ 2) * (x - C.r)

private def vcNewY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  ((C.u⁻¹ : ℚ) ^ 3) * (y - C.s * (x - C.r) - C.t)

/-- Inverse affine coordinate map from `C • W` back to `W`. -/
private def vcOldX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  ((C.u : ℚ) ^ 2) * x + C.r

private def vcOldY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  ((C.u : ℚ) ^ 3) * y + ((C.u : ℚ) ^ 2) * C.s * x + C.t

private lemma vc_u_ne_zero (C : WeierstrassCurve.VariableChange ℚ) :
    (C.u : ℚ) ≠ 0 :=
  C.u.ne_zero

private lemma vc_u_inv_ne_zero (C : WeierstrassCurve.VariableChange ℚ) :
    (C.u⁻¹ : ℚ) ≠ 0 :=
  C.u⁻¹.ne_zero

private lemma vcOldX_vcNewX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    vcOldX C (vcNewX C x) = x := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  unfold vcOldX vcNewX
  simp only [Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vcOldY_vcNewXY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    vcOldY C (vcNewX C x) (vcNewY C x y) = y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  unfold vcOldY vcNewX vcNewY
  simp only [Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vcNewX_vcOldX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    vcNewX C (vcOldX C x) = x := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  unfold vcNewX vcOldX
  simp only [Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vcNewY_vcOldXY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    vcNewY C (vcOldX C x) (vcOldY C x y) = y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  unfold vcNewY vcOldX vcOldY
  simp only [Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

/-! ### 2. Polynomial identities for the forward map -/

private lemma vc_eval_polynomial_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomial.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 6) *
        (WeierstrassCurve.toAffine W).polynomial.evalEval x y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆,
    vcNewX, vcNewY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vc_eval_polynomialX_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomialX.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 4) *
        ((WeierstrassCurve.toAffine W).polynomialX.evalEval x y +
          C.s * (WeierstrassCurve.toAffine W).polynomialY.evalEval x y) := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    vcNewX, vcNewY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vc_eval_polynomialY_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomialY.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 3) *
        (WeierstrassCurve.toAffine W).polynomialY.evalEval x y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₃,
    vcNewX, vcNewY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

/-! ### 3. Polynomial identities for the backward map -/

private lemma vc_eval_polynomial_backward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine W).polynomial.evalEval
        (vcOldX C x) (vcOldY C x y) =
      ((C.u : ℚ) ^ 6) *
        (WeierstrassCurve.toAffine (C • W)).polynomial.evalEval x y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆,
    vcOldX, vcOldY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

private lemma vc_eval_polynomialY_backward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine W).polynomialY.evalEval
        (vcOldX C x) (vcOldY C x y) =
      ((C.u : ℚ) ^ 3) *
        (WeierstrassCurve.toAffine (C • W)).polynomialY.evalEval x y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₃,
    vcOldX, vcOldY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

/--
Backward `X` derivative identity in the triangular form needed for nonsingularity.
This avoids solving for `F_X` explicitly until after the `F_Y = 0` case split.
-/
private lemma vc_eval_polynomialX_add_sY_backward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine W).polynomialX.evalEval
        (vcOldX C x) (vcOldY C x y) +
      C.s * (WeierstrassCurve.toAffine W).polynomialY.evalEval
        (vcOldX C x) (vcOldY C x y) =
      ((C.u : ℚ) ^ 4) *
        (WeierstrassCurve.toAffine (C • W)).polynomialX.evalEval x y := by
  have hu : (C.u : ℚ) ≠ 0 := vc_u_ne_zero C
  simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    vcOldX, vcOldY, Units.val_inv_eq_inv_val]
  field_simp [hu]
  ring

/-! ### 4. Nonsingularity preservation -/

private theorem vc_nonsingular_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ}
    (h : (WeierstrassCurve.toAffine W).Nonsingular x y) :
    (WeierstrassCurve.toAffine (C • W)).Nonsingular
      (vcNewX C x) (vcNewY C x y) := by
  rcases h with ⟨hEq, hDeriv⟩
  constructor
  · rw [WeierstrassCurve.Affine.Equation] at hEq ⊢
    rw [vc_eval_polynomial_forward W C x y, hEq, mul_zero]
  · rw [vc_eval_polynomialX_forward W C x y,
        vc_eval_polynomialY_forward W C x y]
    have hu3 : ((C.u⁻¹ : ℚ) ^ 3) ≠ 0 := pow_ne_zero 3 (vc_u_inv_ne_zero C)
    have hu4 : ((C.u⁻¹ : ℚ) ^ 4) ≠ 0 := pow_ne_zero 4 (vc_u_inv_ne_zero C)
    rcases hDeriv with hX | hY
    · by_cases hY0 : (WeierstrassCurve.toAffine W).polynomialY.evalEval x y = 0
      · left
        intro hbad
        apply hX
        have hsum :
            (WeierstrassCurve.toAffine W).polynomialX.evalEval x y +
              C.s * (WeierstrassCurve.toAffine W).polynomialY.evalEval x y = 0 := by
          exact (mul_eq_zero.mp hbad).resolve_left hu4
        simpa [hY0] using hsum
      · right
        exact mul_ne_zero hu3 hY0
    · right
      exact mul_ne_zero hu3 hY

private theorem vc_nonsingular_backward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ}
    (h : (WeierstrassCurve.toAffine (C • W)).Nonsingular x y) :
    (WeierstrassCurve.toAffine W).Nonsingular
      (vcOldX C x) (vcOldY C x y) := by
  rcases h with ⟨hEq, hDeriv⟩
  constructor
  · rw [WeierstrassCurve.Affine.Equation] at hEq ⊢
    rw [vc_eval_polynomial_backward W C x y, hEq, mul_zero]
  · have hu3 : ((C.u : ℚ) ^ 3) ≠ 0 := pow_ne_zero 3 (vc_u_ne_zero C)
    have hu4 : ((C.u : ℚ) ^ 4) ≠ 0 := pow_ne_zero 4 (vc_u_ne_zero C)
    rcases hDeriv with hX | hY
    · by_cases hY0 :
          (WeierstrassCurve.toAffine (C • W)).polynomialY.evalEval x y = 0
      · left
        intro hOldX0
        have hOldY0 :
            (WeierstrassCurve.toAffine W).polynomialY.evalEval
              (vcOldX C x) (vcOldY C x y) = 0 := by
          rw [vc_eval_polynomialY_backward W C x y, hY0, mul_zero]
        have hsum : ((C.u : ℚ) ^ 4) *
            (WeierstrassCurve.toAffine (C • W)).polynomialX.evalEval x y = 0 := by
          rw [← vc_eval_polynomialX_add_sY_backward W C x y,
            hOldX0, hOldY0, mul_zero, add_zero]
        exact (mul_ne_zero hu4 hX) hsum
      · right
        rw [vc_eval_polynomialY_backward W C x y]
        exact mul_ne_zero hu3 hY0
    · right
      rw [vc_eval_polynomialY_backward W C x y]
      exact mul_ne_zero hu3 hY

/-! ### 5. Affine point maps and inverse laws -/

private def affineVariableChangeMap
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) →
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W))
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some (vcNewX C x) (vcNewY C x y)
        (vc_nonsingular_forward W C h)

private def affineVariableChangeInv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) →
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some (vcOldX C x) (vcOldY C x y)
        (vc_nonsingular_backward W C h)

private theorem affineVariableChange_left_inv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    Function.LeftInverse (affineVariableChangeInv W C) (affineVariableChangeMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [affineVariableChangeMap, affineVariableChangeInv,
        WeierstrassCurve.Affine.Point.some.injEq,
        vcOldX_vcNewX, vcOldY_vcNewXY]

private theorem affineVariableChange_right_inv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    Function.RightInverse (affineVariableChangeInv W C) (affineVariableChangeMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [affineVariableChangeMap, affineVariableChangeInv,
        WeierstrassCurve.Affine.Point.some.injEq,
        vcNewX_vcOldX, vcNewY_vcOldXY]

private noncomputable def affineVariableChangeEquiv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) where
  toFun := affineVariableChangeMap W C
  invFun := affineVariableChangeInv W C
  left_inv := affineVariableChange_left_inv W C
  right_inv := affineVariableChange_right_inv W C

/-! ### 6. New smaller residual: only addition preservation -/

/--
The only residual left after the explicit coordinate map, nonsingularity preservation,
and inverse laws are checked.
-/
axiom affineVariableChangeMap_add
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)) :
    affineVariableChangeMap W C (P + Q) =
      affineVariableChangeMap W C P + affineVariableChangeMap W C Q

/--
Replacement for the old `affinePointAddEquivOfVariableChange` axiom.
Call sites should not need to change if the old axiom had this exact name.
-/
noncomputable def affinePointAddEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃+
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) where
  toEquiv := affineVariableChangeEquiv W C
  map_add' := affineVariableChangeMap_add W C

end
end MazurProof.KubertBridgeN12
```

## If a proof line fails: local adaptation notes

### `Units.val_inv_eq_inv_val`

If this simp lemma is not in scope, replace the start of each algebra proof with:

```lean
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  have hui : ((C.u : ℚ)⁻¹) ≠ 0 := inv_ne_zero hu
  simp only [WeierstrassCurve.Affine.evalEval_polynomial, ...]
  change _ = _
  field_simp [hu, hui]
  ring
```

or add this local lemma:

```lean
private lemma coe_units_inv (u : ℚˣ) : ((u⁻¹ : ℚˣ) : ℚ) = (u : ℚ)⁻¹ := by
  exact Units.val_inv_eq_inv_val u
```

and include `coe_units_inv` in the `simp only` lists.

### Constructor/case syntax

If `cases P with | zero | some` does not work in the local namespace, use:

```lean
  rcases P with (_ | ⟨x, y, h⟩)
```

The affine point constructors in this Mathlib revision are:

```lean
WeierstrassCurve.Affine.Point.zero
WeierstrassCurve.Affine.Point.some (x y : ℚ) (h : W.Nonsingular x y)
```

### `simp` on proof arguments of `some`

If proof irrelevance does not close the inverse-law goals, use:

```lean
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨vcOldX_vcNewX C x, vcOldY_vcNewXY C x y⟩
```

and similarly for the right inverse.

## Verification order

1. Paste only Sections 1--3 and run:

```bash
lake env lean FLT/Assumptions/MazurProof/KubertBridgeN12.lean
```

The likely first failures are in `field_simp`; fix those by adding `hu`/`hui` or `coe_units_inv` as above.

2. Add Section 4 (`vc_nonsingular_forward/backward`).  These proofs should not require any group law facts.

3. Add Section 5.  If `Point.some.injEq` is awkward, prove inverse laws by `rw [Point.some.injEq]` explicitly.

4. Replace the old axiom with Section 6.  Downstream projective equivalence code using `Projective.Point.toAffineAddEquiv` should continue to work unchanged.

## Later attack on the remaining `map_add` residual

The next residual is local and concrete:

```lean
affineVariableChangeMap_add
```

Attack it with three algebra lemmas:

```lean
private lemma vc_negY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    vcNewY C x ((WeierstrassCurve.toAffine W).negY x y) =
      (WeierstrassCurve.toAffine (C • W)).negY
        (vcNewX C x) (vcNewY C x y) := by
  -- simp only [WeierstrassCurve.Affine.negY, variableChange_a₁, variableChange_a₃,
  --   vcNewX, vcNewY, Units.val_inv_eq_inv_val]
  -- field_simp [C.u.ne_zero]
  -- ring
  sorry

private lemma vc_vertical_iff
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ y₁ x₂ y₂ : ℚ) :
    (vcNewX C x₁ = vcNewX C x₂ ∧
      vcNewY C x₁ y₁ =
        (WeierstrassCurve.toAffine (C • W)).negY
          (vcNewX C x₂) (vcNewY C x₂ y₂)) ↔
    (x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂) := by
  -- Use `vcOldX_vcNewX`, `vcOldY_vcNewXY`, and `vc_negY`.
  sorry
```

Then split the nonvertical case into `x₁ = x₂` and `x₁ ≠ x₂`, expand Mathlib's affine `slope`, `addX`, `addY`, and finish each branch by `field_simp [C.u.ne_zero] <;> ring`.
