# Q2899 (dm-codex1): attacking `projectivePointAddEquivOfVariableChange`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Requested namespace: `MazurProof.KubertBridgeN12`

Current residual:

```lean
axiom projectivePointAddEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective W) ≃+
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (C • W))
```

## Bottom line

In the Mathlib revision pinned by this FLT repo (`96fd0fff...`), I do **not** see an existing point-level map induced by `WeierstrassCurve.VariableChange`.  The available APIs are:

* curve-level `VariableChange` action and coefficient formulas:
  `WeierstrassCurve.variableChange_a₁`, `variableChange_a₂`, `variableChange_a₃`, `variableChange_a₄`, `variableChange_a₆`, `variableChange_Δ`;
* affine/projective base-change maps for ring homomorphisms, not Weierstrass variable changes;
* `WeierstrassCurve.Projective.Point.toAffineAddEquiv`, which is the key way to avoid re-proving the projective group law;
* affine point constructors and group law in `WeierstrassCurve.Affine.Point`.

So the best attack is:

1. shrink the current projective residual to an **affine** variable-change `AddEquiv`;
2. prove the projective theorem from that affine theorem using `Projective.Point.toAffineAddEquiv`;
3. then shrink the affine residual further to one explicit `map_add` lemma for a coordinate map, after checking nonsingularity preservation and inverse laws.

The affine path still has a group-law preservation theorem to prove; `toAffineAddEquiv` avoids projective quotient/group-law work, but it does not magically prove that a new affine coordinate map preserves `+`.

## APIs to grep/check locally

```bash
grep -R "def toAffineAddEquiv\|toAffineLift_add" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean
grep -R "def add : W.Point\|lemma add_some\|lemma add_of_Y_eq" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
grep -R "variableChange_a₁\|variableChange_Δ\|structure VariableChange" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean
grep -R "nonsingular_iff_variableChange\|equation_iff_variableChange" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean
grep -R "protected lemma map_add\|baseChange_add" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean
```

Useful `#check`s:

```lean
#check WeierstrassCurve.VariableChange
#check WeierstrassCurve.VariableChange.inv_def
#check WeierstrassCurve.variableChange_a₁
#check WeierstrassCurve.variableChange_a₂
#check WeierstrassCurve.variableChange_a₃
#check WeierstrassCurve.variableChange_a₄
#check WeierstrassCurve.variableChange_a₆
#check WeierstrassCurve.variableChange_Δ
#check WeierstrassCurve.Affine.equation_iff_variableChange
#check WeierstrassCurve.Affine.nonsingular_iff_variableChange
#check WeierstrassCurve.Projective.Point.toAffineAddEquiv
#check WeierstrassCurve.Projective.Point.toAffineLift_add
#check WeierstrassCurve.Projective.map_add
#check WeierstrassCurve.Projective.baseChange_add
```

Interpretation:

* `Projective.map_add` and `Projective.baseChange_add` are for coefficient ring maps/base-change, not for `VariableChange`.
* `Affine.equation_iff_variableChange` and `Affine.nonsingular_iff_variableChange` handle the special translation putting an affine point at the origin; they are useful diagnostics but do not directly give arbitrary `C : VariableChange ℚ` point transport.
* I would not spend time searching for a hidden `VariableChange.Point.map` unless the greps above reveal something new.  The natural map appears not to exist yet.

## Stage 1: replace the projective residual by an affine residual

This is immediately better than the current axiom because all projective quotient/infinity work becomes checked by Mathlib's existing `toAffineAddEquiv`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.KubertBridgeN12

noncomputable section

/--
Smaller residual than the current projective axiom: an admissible Weierstrass variable
change induces an additive equivalence on affine nonsingular point groups.

This avoids projective quotient representatives and relies on the checked Mathlib
projective-to-affine additive equivalence to recover the projective theorem.
-/
axiom affinePointAddEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃+
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W))

/-- Checked wrapper: projective point equivalence follows from the affine one. -/
noncomputable def projectivePointAddEquivOfVariableChange_from_affine
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective W) ≃+
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (C • W)) := by
  classical
  exact
    ((WeierstrassCurve.Projective.Point.toAffineAddEquiv
        (WeierstrassCurve.toProjective W)).trans
      (affinePointAddEquivOfVariableChange W C)).trans
      (WeierstrassCurve.Projective.Point.toAffineAddEquiv
        (WeierstrassCurve.toProjective (C • W))).symm

end
end MazurProof.KubertBridgeN12
```

If Lean complains about definitional equality between

```lean
(WeierstrassCurve.toProjective W).toAffine.Point
```

and

```lean
WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)
```

insert `change` wrappers around the two `toAffineAddEquiv` terms.  `toProjective` and `toAffine` are abbreviations, so this should usually elaborate after `classical`.

## Stage 2: define the explicit affine coordinate maps

Mathlib's variable-change convention is old coordinates as functions of new coordinates:

```text
X_old = u^2 X_new + r,
Y_old = u^3 Y_new + u^2 s X_new + t.
```

Since the wanted direction is from points on `W` to points on `C • W`, use the inverse coordinate formulas:

```text
X_new = u^{-2}(X_old - r),
Y_new = u^{-3}(Y_old - s(X_old - r) - t).
```

Pasteable skeleton:

```lean
namespace MazurProof.KubertBridgeN12

noncomputable section

private def vcNewX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  ((C.u⁻¹ : ℚ) ^ 2) * (x - C.r)

private def vcNewY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  ((C.u⁻¹ : ℚ) ^ 3) * (y - C.s * (x - C.r) - C.t)

private def vcOldX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  ((C.u : ℚ) ^ 2) * x + C.r

private def vcOldY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  ((C.u : ℚ) ^ 3) * y + ((C.u : ℚ) ^ 2) * C.s * x + C.t

private lemma vc_unit_ne_zero (C : WeierstrassCurve.VariableChange ℚ) :
    (C.u : ℚ) ≠ 0 :=
  C.u.ne_zero

private lemma vc_unit_inv_ne_zero (C : WeierstrassCurve.VariableChange ℚ) :
    (C.u⁻¹ : ℚ) ≠ 0 :=
  C.u⁻¹.ne_zero

private lemma vcOldX_newX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    vcOldX C (vcNewX C x) = x := by
  unfold vcOldX vcNewX
  field_simp [vc_unit_ne_zero C]
  ring

private lemma vcOldY_newXY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    vcOldY C (vcNewX C x) (vcNewY C x y) = y := by
  unfold vcOldY vcNewX vcNewY
  field_simp [vc_unit_ne_zero C]
  ring

private lemma vcNewX_oldX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    vcNewX C (vcOldX C x) = x := by
  unfold vcNewX vcOldX
  field_simp [vc_unit_ne_zero C]
  ring

private lemma vcNewY_oldXY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    vcNewY C (vcOldX C x) (vcOldY C x y) = y := by
  unfold vcNewY vcOldX vcOldY
  field_simp [vc_unit_ne_zero C]
  ring

end
end MazurProof.KubertBridgeN12
```

If `field_simp [vc_unit_ne_zero C]` does not see the inverse coercions, add:

```lean
have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
have hui : ((C.u : ℚ)⁻¹) ≠ 0 := inv_ne_zero hu
field_simp [vcNewX, vcNewY, vcOldX, vcOldY, hu, hui]
ring
```

## Stage 3: preserve equation and nonsingularity

Do this with polynomial-value identities, not by trying to simplify the whole `Nonsingular` proposition at once.

The expected identities are:

```text
F_{C•W}(X_new,Y_new) = u^{-6} F_W(X_old,Y_old),
(F_{C•W})_X(X_new,Y_new) = u^{-4}(F_X(X_old,Y_old) + s F_Y(X_old,Y_old)),
(F_{C•W})_Y(X_new,Y_new) = u^{-3}F_Y(X_old,Y_old).
```

Lean declarations:

```lean
namespace MazurProof.KubertBridgeN12

noncomputable section

private lemma vc_eval_polynomial_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomial.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 6) *
        (WeierstrassCurve.toAffine W).polynomial.evalEval x y := by
  -- Expand only the affine polynomial and the five variable-change coefficients.
  -- Avoid unfolding unrelated point/group-law definitions.
  simp only [WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆,
    vcNewX, vcNewY]
  field_simp [vc_unit_ne_zero C]
  ring

private lemma vc_eval_polynomialX_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomialX.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 4) *
        ((WeierstrassCurve.toAffine W).polynomialX.evalEval x y +
          C.s * (WeierstrassCurve.toAffine W).polynomialY.evalEval x y) := by
  simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    vcNewX, vcNewY]
  field_simp [vc_unit_ne_zero C]
  ring

private lemma vc_eval_polynomialY_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).polynomialY.evalEval
        (vcNewX C x) (vcNewY C x y) =
      ((C.u⁻¹ : ℚ) ^ 3) *
        (WeierstrassCurve.toAffine W).polynomialY.evalEval x y := by
  simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₃,
    vcNewX, vcNewY]
  field_simp [vc_unit_ne_zero C]
  ring

private theorem vc_nonsingular_forward
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ}
    (h : (WeierstrassCurve.toAffine W).Nonsingular x y) :
    (WeierstrassCurve.toAffine (C • W)).Nonsingular
      (vcNewX C x) (vcNewY C x y) := by
  rcases h with ⟨hEq, hDeriv⟩
  constructor
  · -- equation preservation
    rw [WeierstrassCurve.Affine.Equation, vc_eval_polynomial_forward W C x y, hEq, mul_zero]
  · -- derivative nonvanishing.  Use the triangular derivative transformation.
    rw [vc_eval_polynomialX_forward W C x y, vc_eval_polynomialY_forward W C x y]
    have hu3 : ((C.u⁻¹ : ℚ) ^ 3) ≠ 0 := pow_ne_zero 3 (vc_unit_inv_ne_zero C)
    have hu4 : ((C.u⁻¹ : ℚ) ^ 4) ≠ 0 := pow_ne_zero 4 (vc_unit_inv_ne_zero C)
    rcases hDeriv with hX | hY
    · by_cases hY0 : (WeierstrassCurve.toAffine W).polynomialY.evalEval x y = 0
      · left
        intro hbad
        apply hX
        have : (WeierstrassCurve.toAffine W).polynomialX.evalEval x y +
            C.s * (WeierstrassCurve.toAffine W).polynomialY.evalEval x y = 0 := by
          exact (mul_eq_zero.mp hbad).resolve_left hu4
        simpa [hY0] using this
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
  -- Either prove direct backward polynomial identities, or use the forward theorem for `C⁻¹`
  -- plus the group-action identity `C⁻¹ • (C • W) = W`.
  -- Direct identities are less elegant but often easier to elaborate.
  -- Skeleton for the direct route:
  sorry

end
end MazurProof.KubertBridgeN12
```

For `vc_nonsingular_backward`, I recommend first writing the direct backward analogues:

```lean
private lemma vc_eval_polynomial_backward ...
private lemma vc_eval_polynomialX_backward ...
private lemma vc_eval_polynomialY_backward ...
```

with expected identities

```text
F_W(X_old,Y_old) = u^6 F_{C•W}(X_new,Y_new),
F_X(old) = u^4 (F'_X(new) - s*u^3? / u^4? ...)
F_Y(old) = u^3 F'_Y(new).
```

But you can avoid derivative algebra for the backward direction by applying the forward theorem to `C⁻¹` and then rewriting:

```lean
have h' := vc_nonsingular_forward (C • W) C⁻¹ h
-- h' has target `toAffine (C⁻¹ • (C • W))` at coordinates computed by `C⁻¹`.
-- Rewrite curve by `inv_smul_smul C W` and coordinates by coordinate-inverse lemmas.
```

This may need `simpa [vcNewX, vcNewY, vcOldX, vcOldY, WeierstrassCurve.VariableChange.inv_def]` plus `field_simp [C.u.ne_zero]` coordinate helper lemmas.  If that gets annoying, the direct backward lemmas are safer.

## Stage 4: define the affine point maps and prove bijection

Once nonsingularity preservation exists, this part is routine casework on `Affine.Point`.

```lean
namespace MazurProof.KubertBridgeN12

noncomputable section

private def affineVariableChangeMap
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) →
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W))
  | 0 => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some (vcNewX C x) (vcNewY C x y)
        (vc_nonsingular_forward W C h)

private def affineVariableChangeInv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) →
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)
  | 0 => 0
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
        vcOldX_newX, vcOldY_newXY]

private theorem affineVariableChange_right_inv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    Function.RightInverse (affineVariableChangeInv W C) (affineVariableChangeMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [affineVariableChangeMap, affineVariableChangeInv,
        WeierstrassCurve.Affine.Point.some.injEq,
        vcNewX_oldX, vcNewY_oldXY]

private noncomputable def affineVariableChangeEquiv
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) where
  toFun := affineVariableChangeMap W C
  invFun := affineVariableChangeInv W C
  left_inv := affineVariableChange_left_inv W C
  right_inv := affineVariableChange_right_inv W C

end
end MazurProof.KubertBridgeN12
```

If the `cases P with | zero | some` syntax differs locally, use:

```lean
  rcases P with (_ | ⟨x, y, h⟩)
```

matching the constructors in `Affine.Point.lean`.

## Stage 5: the only hard part — `map_add'`

After Stage 4, the remaining mathematical content is exactly:

```lean
namespace MazurProof.KubertBridgeN12

noncomputable section

/--
Smallest honest residual after the coordinate-map work: the explicit affine variable-change map
preserves the chord-and-tangent group law.
-/
axiom affineVariableChangeMap_add
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)) :
    affineVariableChangeMap W C (P + Q) =
      affineVariableChangeMap W C P + affineVariableChangeMap W C Q

noncomputable def affinePointAddEquivOfVariableChange_from_map_add
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) ≃+
      WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (C • W)) where
  toEquiv := affineVariableChangeEquiv W C
  map_add' := affineVariableChangeMap_add W C

end
end MazurProof.KubertBridgeN12
```

This is already a much smaller residual than the current projective axiom:

* no projective quotient representatives;
* no point at infinity cases except `0` in affine point type;
* no nonsingularity preservation;
* no inverse/bijection proof;
* only preservation of the already-defined affine group law remains.

### How to prove `affineVariableChangeMap_add` later

Do it by split lemmas, not a single `cases P; cases Q; simp; ring_nf`.

Needed coordinate identities:

```lean
private lemma vc_negY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    vcNewY C x ((WeierstrassCurve.toAffine W).negY x y) =
      (WeierstrassCurve.toAffine (C • W)).negY (vcNewX C x) (vcNewY C x y) := by
  -- unfold `Affine.negY`; use variableChange_a₁/a₃; field_simp; ring
  sorry

private lemma vc_add_vertical_condition_iff
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ y₁ x₂ y₂ : ℚ) :
    (vcNewX C x₁ = vcNewX C x₂ ∧
      vcNewY C x₁ y₁ =
        (WeierstrassCurve.toAffine (C • W)).negY (vcNewX C x₂) (vcNewY C x₂ y₂)) ↔
    (x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂) := by
  -- Use injectivity of `x ↦ vcNewX C x`, coordinate inverse lemmas, and `vc_negY`.
  sorry
```

For nonvertical addition, show transformed line slope and output coordinates agree.  Use Mathlib names from `Affine/Formula.lean`:

```lean
#check WeierstrassCurve.Affine.slope
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.negAddY
```

Expected lemmas:

```lean
private lemma vc_slope
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ}
    (hnot : ¬(x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂)) :
    -- statement depends on Mathlib's exact slope convention;
    -- derive by expanding `Affine.slope` after splitting `x₁ = x₂` vs `x₁ ≠ x₂`.
    True := by
  trivial

private lemma vc_addX
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ} :
    vcNewX C
      ((WeierstrassCurve.toAffine W).addX x₁ x₂
        ((WeierstrassCurve.toAffine W).slope x₁ x₂ y₁ y₂)) =
      (WeierstrassCurve.toAffine (C • W)).addX
        (vcNewX C x₁) (vcNewX C x₂)
        ((WeierstrassCurve.toAffine (C • W)).slope
          (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewY C x₂ y₂)) := by
  -- split `x₁ = x₂`; expand `slope`, `addX`, coefficient formulas; field_simp; ring
  sorry

private lemma vc_addY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ} :
    vcNewY C x₁
      ((WeierstrassCurve.toAffine W).addY x₁ x₂ y₁
        ((WeierstrassCurve.toAffine W).slope x₁ x₂ y₁ y₂)) =
      (WeierstrassCurve.toAffine (C • W)).addY
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁)
        ((WeierstrassCurve.toAffine (C • W)).slope
          (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewY C x₂ y₂)) := by
  -- similar but usually larger than `vc_addX`
  sorry
```

Then the proof of `affineVariableChangeMap_add` becomes casework:

```lean
theorem affineVariableChangeMap_add_checked
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)) :
    affineVariableChangeMap W C (P + Q) =
      affineVariableChangeMap W C P + affineVariableChangeMap W C Q := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · simp [affineVariableChangeMap]
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · simp [affineVariableChangeMap]
  by_cases hvert : x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂
  · -- both sides are zero by vertical-condition compatibility
    simp [WeierstrassCurve.Affine.Point.add_of_Y_eq hvert.1 hvert.2,
      affineVariableChangeMap, vc_add_vertical_condition_iff, hvert]
  · -- both sides are the same `some`, by `vc_addX` and `vc_addY`
    rw [WeierstrassCurve.Affine.Point.add_some hvert]
    rw [WeierstrassCurve.Affine.Point.add_some]
    · simp [affineVariableChangeMap, WeierstrassCurve.Affine.Point.some.injEq,
        vc_addX, vc_addY]
    · -- transformed pair is not vertical
      exact (vc_add_vertical_condition_iff W C x₁ y₁ x₂ y₂).not.mpr hvert
```

This is the direct formal route.  It is work, but each lemma is algebraic and local.

## Alternative route: coordinate-ring/class-group proof of `map_add'`

`Affine.Point.toClass` is a group hom into the class group and is injective.  A variable change should induce an isomorphism of coordinate rings, hence a class-group equivalence, and then `map_add'` can be proved by injectivity of `toClass` rather than by slope formulas.

This may be elegant but likely requires more infrastructure:

```lean
-- Not currently in Mathlib as far as I can see:
noncomputable def coordinateRingEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    (WeierstrassCurve.toAffine W).CoordinateRing ≃+*
      (WeierstrassCurve.toAffine (C • W)).CoordinateRing := by
  -- induced by X ↦ u² X + r, Y ↦ u³Y + u²sX + t, or inverse direction
  sorry
```

Then prove compatibility with `XYIdeal'`.  This may avoid the chord/tangent formulas, but it is probably a larger detour than the affine formula route.

## Direct projective coordinate map, if needed

If you decide not to go through affine charts, the forward projective representative map from `W` to `C • W` should be the homogeneous inverse coordinate change:

```lean
private def vcProjectiveNew
    (C : WeierstrassCurve.VariableChange ℚ) (P : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![((C.u⁻¹ : ℚ) ^ 2) * (P 0 - C.r * P 2),
    ((C.u⁻¹ : ℚ) ^ 3) * (P 1 - C.s * (P 0 - C.r * P 2) - C.t * P 2),
    P 2]
```

You would then need:

```lean
lemma vcProjectiveNew_equiv {P Q : Fin 3 → ℚ}
    (h : P ≈ Q) : vcProjectiveNew C P ≈ vcProjectiveNew C Q := by ...

lemma vcProjectiveNew_nonsingular
    {P : Fin 3 → ℚ}
    (h : (WeierstrassCurve.toProjective W).Nonsingular P) :
    (WeierstrassCurve.toProjective (C • W)).Nonsingular (vcProjectiveNew C P) := by ...
```

This can produce a projective `Equiv`, but proving `map_add'` at the projective level would mean matching Mathlib's projective addition formulas.  I would avoid this unless there is a later reason to need the projective coordinate map itself.

## Recommended replacement hierarchy

Best immediate improvement:

```lean
axiom affinePointAddEquivOfVariableChange
```

and make `projectivePointAddEquivOfVariableChange` a theorem via `toAffineAddEquiv`.

Next improvement:

```lean
axiom affineVariableChangeMap_add
```

with explicit checked coordinate map, nonsingularity preservation, and inverse laws.

Final target:

```lean
theorem affineVariableChangeMap_add_checked ...
```

proved from `vc_negY`, `vc_add_vertical_condition_iff`, `vc_addX`, and `vc_addY`.

This staged plan gives a real path from the current projective axiom to a single algebraic group-law compatibility lemma, then to no residual at all.
