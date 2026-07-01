# Q2905 (dm-codex1): attacking `affineVariableChangeMap_add`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Requested namespace: `MazurProof.KubertBridgeN12`

Assumed already checked in scratch:

```lean
vcNewX C x = ((C.u : ℚ)⁻¹)^2 * (x - C.r)
vcNewY C x y = ((C.u : ℚ)⁻¹)^3 * (y - C.s * (x - C.r) - C.t)
vcOldX C x = (C.u : ℚ)^2 * x + C.r
vcOldY C x y = (C.u : ℚ)^3 * y + (C.u : ℚ)^2 * C.s * x + C.t

vcOldX_vcNewX
vcOldY_vcNewXY
vcNewX_vcOldX
vcNewY_vcOldXY
vc_nonsingular_forward
vc_nonsingular_backward

affineVariableChangeMap
affineVariableChangeInv
affineVariableChangeEquiv
```

Important local correction retained here: in this Mathlib, `(C.u⁻¹ : ℚ)` already elaborates as `(C.u : ℚ)⁻¹`; do not use `Units.val_inv_eq_inv_val`. Use `field_simp [C.u.ne_zero]` and `inv_ne_zero C.u.ne_zero` directly.

The remaining residual is:

```lean
affineVariableChangeMap_add
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)) :
    affineVariableChangeMap W C (P + Q) =
      affineVariableChangeMap W C P + affineVariableChangeMap W C Q
```

Below is the staged route that should compile with only local algebra edits if a `simp only` list is missing a coefficient lemma.

## API checks

```lean
#check WeierstrassCurve.Affine.negY
#check WeierstrassCurve.Affine.slope
#check WeierstrassCurve.Affine.slope_of_X_ne
#check WeierstrassCurve.Affine.slope_of_Y_ne
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.negAddY
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.Point.add_some
#check WeierstrassCurve.Affine.Point.add_of_Y_eq
#check WeierstrassCurve.Affine.Point.add_of_X_ne
#check WeierstrassCurve.Affine.Y_eq_of_Y_ne
#check WeierstrassCurve.Affine.Point.toClass
#check WeierstrassCurve.Affine.Point.toClass_injective
```

The pinned API has:

```lean
Affine.negY x y = -y - a₁*x - a₃
Affine.slope x₁ x₂ y₁ y₂
Affine.addX x₁ x₂ ℓ = ℓ^2 + a₁*ℓ - a₂ - x₁ - x₂
Affine.negAddY x₁ x₂ y₁ ℓ = ℓ * (addX x₁ x₂ ℓ - x₁) + y₁
Affine.addY x₁ x₂ y₁ ℓ = negY (addX x₁ x₂ ℓ) (negAddY x₁ x₂ y₁ ℓ)
```

## Pasteable lemmas for the formula route

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.KubertBridgeN12

noncomputable section

/-! ### 1. Tiny injectivity helpers for the coordinate map -/

private lemma vcNewX_eq_iff
    (C : WeierstrassCurve.VariableChange ℚ) {x₁ x₂ : ℚ} :
    vcNewX C x₁ = vcNewX C x₂ ↔ x₁ = x₂ := by
  constructor
  · intro h
    have h' := congrArg (vcOldX C) h
    simpa [vcOldX_vcNewX] using h'
  · intro h
    simpa [h]

private lemma vcNewY_eq_iff_of_x_eq
    (C : WeierstrassCurve.VariableChange ℚ) {x₁ x₂ y₁ y₂ : ℚ}
    (hx : x₁ = x₂) :
    vcNewY C x₁ y₁ = vcNewY C x₂ y₂ ↔ y₁ = y₂ := by
  subst x₂
  constructor
  · intro h
    have h' := congrArg (fun Y => vcOldY C (vcNewX C x₁) Y) h
    simpa [vcOldY_vcNewXY] using h'
  · intro h
    simpa [h]

/-! ### 2. Negation and vertical-condition compatibility -/

private lemma vc_negY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x y : ℚ) :
    (WeierstrassCurve.toAffine (C • W)).negY (vcNewX C x) (vcNewY C x y) =
      vcNewY C x ((WeierstrassCurve.toAffine W).negY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  simp only [WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₃,
    vcNewX, vcNewY]
  field_simp [hu]
  ring

private lemma vc_vertical_iff
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ y₁ x₂ y₂ : ℚ) :
    (vcNewX C x₁ = vcNewX C x₂ ∧
      vcNewY C x₁ y₁ =
        (WeierstrassCurve.toAffine (C • W)).negY (vcNewX C x₂) (vcNewY C x₂ y₂)) ↔
    (x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂) := by
  constructor
  · rintro ⟨hxN, hyN⟩
    have hx : x₁ = x₂ := (vcNewX_eq_iff C).mp hxN
    refine ⟨hx, ?_⟩
    rw [vc_negY W C x₂ y₂] at hyN
    exact (vcNewY_eq_iff_of_x_eq C hx).mp hyN
  · rintro ⟨hx, hy⟩
    subst x₂
    subst y₁
    constructor
    · rfl
    · rw [vc_negY W C]

/-! ### 3. Slope transform -/

private def vcNewSlope (C : WeierstrassCurve.VariableChange ℚ) (ℓ : ℚ) : ℚ :=
  ((C.u : ℚ)⁻¹) * (ℓ - C.s)

private lemma vc_slope_of_X_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (WeierstrassCurve.toAffine (C • W)).slope
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewY C x₂ y₂) =
      vcNewSlope C ((WeierstrassCurve.toAffine W).slope x₁ x₂ y₁ y₂) := by
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  have hxN : vcNewX C x₁ ≠ vcNewX C x₂ := by
    intro hN
    exact hx ((vcNewX_eq_iff C).mp hN)
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
    WeierstrassCurve.Affine.slope_of_X_ne hxN]
  simp only [vcNewX, vcNewY, vcNewSlope]
  field_simp [hu, sub_ne_zero.mpr hx]
  ring

private lemma vc_slope_of_Y_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (WeierstrassCurve.toAffine W).Nonsingular x₁ y₁)
    (h₂ : (WeierstrassCurve.toAffine W).Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hy : y₁ ≠ (WeierstrassCurve.toAffine W).negY x₂ y₂) :
    (WeierstrassCurve.toAffine (C • W)).slope
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewY C x₂ y₂) =
      vcNewSlope C ((WeierstrassCurve.toAffine W).slope x₁ x₂ y₁ y₂) := by
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  have hyy : y₁ = y₂ :=
    WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.left h₂.left hx hy
  subst x₂
  subst y₂
  have hyN : vcNewY C x₁ y₁ ≠
      (WeierstrassCurve.toAffine (C • W)).negY (vcNewX C x₁) (vcNewY C x₁ y₁) := by
    intro hbad
    exact hy ((vc_vertical_iff W C x₁ y₁ x₁ y₁).mp ⟨rfl, hbad⟩).2
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
    WeierstrassCurve.Affine.slope_of_Y_ne rfl hyN]
  simp only [WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    vcNewX, vcNewY, vcNewSlope]
  -- `hy` proves the tangent denominator is nonzero after unfolding `negY`.
  have hden : y₁ - (-y₁ - (WeierstrassCurve.toAffine W).a₁ * x₁ -
        (WeierstrassCurve.toAffine W).a₃) ≠ 0 := by
    exact sub_ne_zero.mpr hy
  field_simp [hu, hden]
  ring

private lemma vc_slope_nonvertical
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (WeierstrassCurve.toAffine W).Nonsingular x₁ y₁)
    (h₂ : (WeierstrassCurve.toAffine W).Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂)) :
    (WeierstrassCurve.toAffine (C • W)).slope
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewY C x₂ y₂) =
      vcNewSlope C ((WeierstrassCurve.toAffine W).slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (WeierstrassCurve.toAffine W).negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
    exact vc_slope_of_Y_ne W C h₁ h₂ hx hy
  · exact vc_slope_of_X_ne W C hx

/-! ### 4. `addX`, `negAddY`, `addY` transform for an arbitrary line slope -/

private lemma vc_addX_line
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ ℓ : ℚ) :
    vcNewX C ((WeierstrassCurve.toAffine W).addX x₁ x₂ ℓ) =
      (WeierstrassCurve.toAffine (C • W)).addX
        (vcNewX C x₁) (vcNewX C x₂) (vcNewSlope C ℓ) := by
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    vcNewX, vcNewSlope]
  field_simp [hu]
  ring

private lemma vc_negAddY_line
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ y₁ ℓ : ℚ) :
    vcNewY C ((WeierstrassCurve.toAffine W).addX x₁ x₂ ℓ)
      ((WeierstrassCurve.toAffine W).negAddY x₁ x₂ y₁ ℓ) =
      (WeierstrassCurve.toAffine (C • W)).negAddY
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewSlope C ℓ) := by
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  simp only [WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    vcNewX, vcNewY, vcNewSlope]
  field_simp [hu]
  ring

private lemma vc_addY_line
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ y₁ ℓ : ℚ) :
    vcNewY C ((WeierstrassCurve.toAffine W).addX x₁ x₂ ℓ)
      ((WeierstrassCurve.toAffine W).addY x₁ x₂ y₁ ℓ) =
      (WeierstrassCurve.toAffine (C • W)).addY
        (vcNewX C x₁) (vcNewX C x₂) (vcNewY C x₁ y₁) (vcNewSlope C ℓ) := by
  rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addY]
  rw [vc_negY W C]
  rw [vc_addX_line W C]
  rw [vc_negAddY_line W C]

/-! ### 5. Final `map_add` proof -/

/--
This theorem should replace the residual axiom once the algebra lemmas above compile.
-/
theorem affineVariableChangeMap_add_checked
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W)) :
    affineVariableChangeMap W C (P + Q) =
      affineVariableChangeMap W C P + affineVariableChangeMap W C Q := by
  cases P with
  | zero => simp [affineVariableChangeMap]
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp [affineVariableChangeMap]
      | some x₂ y₂ h₂ =>
          by_cases hxy : x₁ = x₂ ∧ y₁ = (WeierstrassCurve.toAffine W).negY x₂ y₂
          · have hxyN :
                vcNewX C x₁ = vcNewX C x₂ ∧
                  vcNewY C x₁ y₁ =
                    (WeierstrassCurve.toAffine (C • W)).negY
                      (vcNewX C x₂) (vcNewY C x₂ y₂) :=
              (vc_vertical_iff W C x₁ y₁ x₂ y₂).mpr hxy
            rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
            simp [affineVariableChangeMap,
              WeierstrassCurve.Affine.Point.add_of_Y_eq hxyN.1 hxyN.2]
          · have hxyN : ¬(vcNewX C x₁ = vcNewX C x₂ ∧
                  vcNewY C x₁ y₁ =
                    (WeierstrassCurve.toAffine (C • W)).negY
                      (vcNewX C x₂) (vcNewY C x₂ y₂)) := by
              intro hbad
              exact hxy ((vc_vertical_iff W C x₁ y₁ x₂ y₂).mp hbad)
            rw [WeierstrassCurve.Affine.Point.add_some hxy]
            rw [WeierstrassCurve.Affine.Point.add_some hxyN]
            rw [WeierstrassCurve.Affine.Point.some.injEq]
            constructor
            · rw [vc_addX_line W C]
              rw [vc_slope_nonvertical W C h₁ h₂ hxy]
            · rw [vc_addY_line W C]
              rw [vc_slope_nonvertical W C h₁ h₂ hxy]

end
end MazurProof.KubertBridgeN12
```

### If the tangent slope lemma is the only slow/failing part

Replace the tangent proof by two smaller derivative-based lemmas using the already compiled nonsingularity identities from Q2901:

```lean
private lemma vc_tangent_den_ne_zero
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hy : y ≠ (WeierstrassCurve.toAffine W).negY x y) :
    (WeierstrassCurve.toAffine W).polynomialY.evalEval x y ≠ 0 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  rw [WeierstrassCurve.Affine.negY] at hy
  exact sub_ne_zero.mp (by
    -- `y - (-y - a₁*x - a₃) = polynomialY.evalEval x y`
    convert sub_ne_zero.mpr hy using 1 <;> ring)
```

Then prove tangent slope by:

```lean
rw [WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval ...]
```

if the local API elaborates this lemma.  It exists in `Affine/Formula.lean` as:

```lean
WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval
```

This avoids expanding the tangent numerator with all transformed coefficients in one shot.

## Class-group route assessment

Pinned Mathlib has the tempting APIs:

```lean
#check WeierstrassCurve.Affine.Point.toClass
#check WeierstrassCurve.Affine.Point.toClass_injective
```

`toClass` is a group hom from affine points to `Additive (ClassGroup W.CoordinateRing)`, and `toClass_injective` proves injectivity.  In principle, `map_add` could be proved by transporting ideals through a coordinate-ring isomorphism and then using injectivity of `toClass`.

However, in this Mathlib revision there is no ready-made

```lean
(W.toAffine).CoordinateRing ≃+* ((C • W).toAffine).CoordinateRing
```

for a `VariableChange`.  Building it requires proving that the polynomial quotient ideal is preserved by

```text
X ↦ u² X + r,
Y ↦ u³ Y + u² s X + t
```

and then proving compatibility with `CoordinateRing.XYIdeal'`.  That is likely more code than the affine formula route above.  The class-group route becomes shorter only after a reusable theorem like this exists:

```lean
noncomputable def coordinateRingEquivOfVariableChange
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    (WeierstrassCurve.toAffine W).CoordinateRing ≃+*
      (WeierstrassCurve.toAffine (C • W)).CoordinateRing := by
  -- not currently in Mathlib; substantial quotient-polynomial work
  sorry
```

So for this file, the formula route is the shorter path: the only remaining algebra after Q2901 is `vc_negY`, vertical compatibility, slope transform, and `addX/addY` transform.
