# Q2934 (dm-codex1): next checkable targets for residual A

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

Current residual A:

```lean
axiom tate_normal_form_at_point_of_addOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    TateNormalFormAtOrder12 E
```

The next bounded targets are:

1. extract the nonzero affine coordinates of `P`;
2. translate those coordinates to the origin and transport order 12;
3. normalize an origin-marked curve with `a₆=0` toward Tate form: first kill `a₄`, then scale to make `a₂=a₃=-b`.

Below, use the exact local notation in your file.  Since you said `(E⁄ℚ).Point` is the affine point group notation under `open scoped WeierstrassCurve.Affine`, the case split should be on `WeierstrassCurve.Affine.Point.zero` / `.some`.

## 1. Extract affine coordinates from `P`

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

structure AffineMarkedPointOfOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) where
  x0 : ℚ
  y0 : ℚ
  hxy : (E⁄ℚ).Nonsingular x0 y0
  hP_eq : P = WeierstrassCurve.Affine.Point.some x0 y0 hxy
  hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some x0 y0 hxy) = 12

theorem affineMarkedPointOfOrder12_of_addOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    AffineMarkedPointOfOrder12 E P := by
  have hP_ne_zero : P ≠ 0 := by
    intro hzero
    subst hzero
    -- `simp` should reduce `addOrderOf 0` to `1`.
    norm_num at hP
  cases P with
  | zero => exact (hP_ne_zero rfl).elim
  | some x0 y0 hxy =>
      exact
        { x0 := x0
          y0 := y0
          hxy := hxy
          hP_eq := rfl
          hOrder := hP }
```

If `norm_num at hP` does not simplify `addOrderOf 0`, use:

```lean
    have hzeroOrder : addOrderOf (0 : (E⁄ℚ).Point) = 1 := by simp
    rw [hzeroOrder] at hP
    norm_num at hP
```

## 2. Translate the marked affine point to the origin

Mathlib's `VariableChange` convention is

```text
X_old = u^2 X_new + r,
Y_old = u^3 Y_new + u^2 s X_new + t.
```

So to send old point `(x0,y0)` to new origin `(0,0)`, use `u=1, r=x0, s=0, t=y0`.

```lean
noncomputable def translatePointToOriginVC (x0 y0 : ℚ) :
    WeierstrassCurve.VariableChange ℚ :=
  { u := 1
    r := x0
    s := 0
    t := y0 }

/-- The translated curve has `a₆=0`, because the old point lies on `E`. -/
theorem translatePointToOrigin_a6
    (E : WeierstrassCurve ℚ) {x0 y0 : ℚ}
    (hxy : (E⁄ℚ).Nonsingular x0 y0) :
    ((translatePointToOriginVC x0 y0) • E).a₆ = 0 := by
  have hEq := hxy.left
  -- If this line fails because `E⁄ℚ` is not definally `E`, replace `hEq` by `simpa` first:
  -- have hEqE : (WeierstrassCurve.toAffine E).Equation x0 y0 := by simpa using hxy.left
  rw [WeierstrassCurve.Affine.equation_iff'] at hEq
  rw [WeierstrassCurve.variableChange_a₆]
  simp [translatePointToOriginVC]
  linear_combination (norm := ring) -hEq

/-- The marked point becomes the new origin and remains nonsingular. -/
theorem translatePointToOrigin_origin_nonsingular
    (E : WeierstrassCurve ℚ) {x0 y0 : ℚ}
    (hxy : (E⁄ℚ).Nonsingular x0 y0) :
    (((translatePointToOriginVC x0 y0) • E)⁄ℚ).Nonsingular 0 0 := by
  -- Mathlib has exactly the special translation lemma:
  -- `WeierstrassCurve.Affine.nonsingular_iff_variableChange`.
  simpa [translatePointToOriginVC] using
    (WeierstrassCurve.Affine.nonsingular_iff_variableChange
      (W := E⁄ℚ) x0 y0).mp hxy
```

If the target produced by `nonsingular_iff_variableChange` is `(translatePointToOriginVC x0 y0 • (E⁄ℚ)).Nonsingular 0 0` instead of `(((translatePointToOriginVC x0 y0) • E)⁄ℚ).Nonsingular 0 0`, add a small base-change/defeq adapter:

```lean
theorem translatePointToOrigin_origin_nonsingular_toAffine
    (E : WeierstrassCurve ℚ) {x0 y0 : ℚ}
    (hxy : (E⁄ℚ).Nonsingular x0 y0) :
    (WeierstrassCurve.toAffine ((translatePointToOriginVC x0 y0) • E)).Nonsingular 0 0 := by
  simpa using translatePointToOrigin_origin_nonsingular E hxy
```

### Order transport after translation

This uses your checked `affinePointAddEquivOfVariableChange` and explicit coordinate map.

```lean
/-- The explicit variable-change map sends `(x0,y0)` to `(0,0)`. -/
theorem affineVariableChangeMap_translate_origin
    (E : WeierstrassCurve ℚ) {x0 y0 : ℚ}
    (hxy : (E⁄ℚ).Nonsingular x0 y0) :
    affineVariableChangeMap E (translatePointToOriginVC x0 y0)
      (WeierstrassCurve.Affine.Point.some x0 y0 hxy) =
    WeierstrassCurve.Affine.Point.some 0 0
      (translatePointToOrigin_origin_nonsingular E hxy) := by
  -- This should be just the already checked coordinate map with `u=1,r=x0,s=0,t=y0`.
  simp [affineVariableChangeMap, translatePointToOriginVC, vcNewX, vcNewY]

/-- Exact order 12 is transported to the new origin. -/
theorem translatePointToOrigin_origin_order12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {x0 y0 : ℚ} (hxy : (E⁄ℚ).Nonsingular x0 y0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some x0 y0 hxy) = 12) :
    addOrderOf
      (WeierstrassCurve.Affine.Point.some 0 0
        (translatePointToOrigin_origin_nonsingular E hxy)) = 12 := by
  let C := translatePointToOriginVC x0 y0
  let e := affinePointAddEquivOfVariableChange E C
  have hmap : e (WeierstrassCurve.Affine.Point.some x0 y0 hxy) =
      WeierstrassCurve.Affine.Point.some 0 0
        (translatePointToOrigin_origin_nonsingular E hxy) := by
    simpa [e, C] using affineVariableChangeMap_translate_origin E hxy
  rw [← hmap]
  simpa [hOrder] using
    addOrderOf_apply_addEquiv e
      (WeierstrassCurve.Affine.Point.some x0 y0 hxy)
```

If `affinePointAddEquivOfVariableChange` has target `(C • E⁄ℚ).Point` but your explicit map theorem target is written with `toAffine`, use a `change` before `have hmap` and let `simpa` close the definitional equalities.

Bundle the checkable translation result:

```lean
structure TranslatedOriginOrder12 (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  x0 : ℚ
  y0 : ℚ
  hxy : (E⁄ℚ).Nonsingular x0 y0
  C0 : WeierstrassCurve.VariableChange ℚ
  hC0 : C0 = translatePointToOriginVC x0 y0
  hA6 : (C0 • E).a₆ = 0
  hO : ((C0 • E)⁄ℚ).Nonsingular 0 0
  hOriginOrder :
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12

theorem translate_order12_point_to_origin
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    TranslatedOriginOrder12 E := by
  rcases affineMarkedPointOfOrder12_of_addOrder12 E P hP with
    ⟨x0, y0, hxy, hP_eq, hOrder⟩
  refine
    { x0 := x0
      y0 := y0
      hxy := hxy
      C0 := translatePointToOriginVC x0 y0
      hC0 := rfl
      hA6 := translatePointToOrigin_a6 E hxy
      hO := translatePointToOrigin_origin_nonsingular E hxy
      hOriginOrder := translatePointToOrigin_origin_order12 E hxy hOrder }
```

This theorem is the next high-value checkable target: it removes affine extraction and translation from residual A.

## 3. Origin-preserving coordinate changes toward Tate form

Now work with an arbitrary curve `W` with origin `(0,0)` of exact order 12.

### 3.1 Kill `a₄` using `s = a₄/a₃`

Your new lemma `origin_a3_ne_zero_of_addOrderOf_eq_12` supplies `a₃ ≠ 0`.

```lean
noncomputable def killA4VC (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  { u := 1
    r := 0
    s := W.a₄ / W.a₃
    t := 0 }

theorem killA4_a4
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    ((killA4VC W h3) • W).a₄ = 0 := by
  rw [WeierstrassCurve.variableChange_a₄]
  simp [killA4VC]
  field_simp [h3]
  ring

theorem killA4_a6
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0)
    (h6 : W.a₆ = 0) :
    ((killA4VC W h3) • W).a₆ = 0 := by
  rw [WeierstrassCurve.variableChange_a₆]
  simp [killA4VC, h6]

theorem killA4_a3_ne_zero
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    ((killA4VC W h3) • W).a₃ ≠ 0 := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [killA4VC, h3]

/-- The origin remains the origin under `killA4VC`. -/
theorem killA4_origin_nonsingular
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0)
    (hO : (W⁄ℚ).Nonsingular 0 0) :
    (((killA4VC W h3) • W)⁄ℚ).Nonsingular 0 0 := by
  -- Use the explicit variable-change map or direct formula with `r=0,t=0`.
  -- Easiest is to apply `vc_nonsingular_forward` to `(0,0)` and simplify coordinates.
  simpa [killA4VC, vcNewX, vcNewY] using
    (vc_nonsingular_forward W (killA4VC W h3) hO)

theorem killA4_origin_order12
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h3 : W.a₃ ≠ 0)
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    addOrderOf
      (WeierstrassCurve.Affine.Point.some 0 0
        (killA4_origin_nonsingular W h3 hO)) = 12 := by
  let C := killA4VC W h3
  let e := affinePointAddEquivOfVariableChange W C
  have hmap : e (WeierstrassCurve.Affine.Point.some 0 0 hO) =
      WeierstrassCurve.Affine.Point.some 0 0
        (killA4_origin_nonsingular W h3 hO) := by
    simp [e, C, affineVariableChangeMap, killA4VC, vcNewX, vcNewY]
  rw [← hmap]
  simpa [hOrder] using
    addOrderOf_apply_addEquiv e (WeierstrassCurve.Affine.Point.some 0 0 hO)
```

This second block should also be checkable now.

### 3.2 Scale to Tate form once `a₂ ≠ 0`

After `a₆=0`, `a₄=0`, `a₃≠0`, the remaining normalization is pure scaling with `r=s=t=0`.  To make `a₂'=a₃'`, choose

```text
u = a₃/a₂.
```

This requires `a₂ ≠ 0`.  Proving `a₂ ≠ 0` from exact order 12 is the next genuine group-law exclusion.  Keep it as a small residual if needed.

```lean
/-- Small remaining mathematical exclusion: after origin and `a₄=0`, exact order 12 forces `a₂≠0`. -/
axiom origin_a2_ne_zero_of_a4_a6_origin_order12
    (W : WeierstrassCurve ℚ)
    (h6 : W.a₆ = 0)
    (h4 : W.a₄ = 0)
    (h3 : W.a₃ ≠ 0)
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    W.a₂ ≠ 0

noncomputable def scaleToTateVC
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  { u := Units.mk0 (W.a₃ / W.a₂) (by
      exact div_ne_zero (by
        -- This proof needs `W.a₃ ≠ 0`; either add it as an argument or infer it at call sites.
        -- Prefer the version below with both `h2` and `h3`.
        sorry) h2)
    r := 0
    s := 0
    t := 0 }
```

Use this less awkward version:

```lean
noncomputable def scaleToTateVC'
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  { u := Units.mk0 (W.a₃ / W.a₂) (div_ne_zero h3 h2)
    r := 0
    s := 0
    t := 0 }

def tateBOfOriginNormal (W : WeierstrassCurve ℚ) : ℚ :=
  - W.a₂ ^ 3 / W.a₃ ^ 2

def tateCOfOriginNormal (W : WeierstrassCurve ℚ) : ℚ :=
  1 - W.a₁ * W.a₂ / W.a₃

/-- Pure coefficient algebra: once `a₄=a₆=0` and `a₂,a₃≠0`, scaling gives Tate form. -/
theorem scaleToTate_eq_tateW
    (W : WeierstrassCurve ℚ)
    (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    (scaleToTateVC' W h2 h3) • W =
      tateW (tateBOfOriginNormal W) (tateCOfOriginNormal W) := by
  ext <;>
    simp [scaleToTateVC', tateW, tateBOfOriginNormal, tateCOfOriginNormal,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,
      h2, h3, h4, h6] <;>
    field_simp [h2, h3] <;>
    ring
```

This theorem is pure algebra and should be checkable.  It cleanly identifies the next true obstruction: proving `a₂≠0` in the origin-normalized, `a₄=0` situation from exact order 12.

## Minimal intermediate normal-form structure

If full `TateNormalFormAtOrder12` is too big to prove at once, introduce this checked intermediate target:

```lean
structure OriginA4KilledOrder12 (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  W : WeierstrassCurve ℚ
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = W
  hA6 : W.a₆ = 0
  hA4 : W.a₄ = 0
  hA3 : W.a₃ ≠ 0
  hO : (W⁄ℚ).Nonsingular 0 0
  hOriginOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12

theorem origin_a4_killed_order12_of_point_order12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    OriginA4KilledOrder12 E := by
  -- 1. `translate_order12_point_to_origin` gives W0 = C0•E, a6=0, origin order 12.
  -- 2. `origin_a3_ne_zero_of_addOrderOf_eq_12` gives W0.a3≠0.
  -- 3. Apply `killA4VC W0 h3`, compose variable changes, and use the killA4 lemmas.
  -- 4. Use `mul_smul` for variable-change composition.
  sorry
```

Then final Tate form is obtained from `OriginA4KilledOrder12` plus the single residual `origin_a2_ne_zero_of_a4_a6_origin_order12` and the checked algebra lemma `scaleToTate_eq_tateW`.

## Summary of genuinely mathematical steps

Checkable now:

* affine extraction from `P`;
* translation to origin and `a₆=0`;
* origin order transport through the checked variable-change `AddEquiv`;
* `a₃≠0` from your new order-two exclusion lemma;
* killing `a₄` by `s=a₄/a₃`;
* scaling to `tateW b c` assuming `a₂≠0`.

Leave as a small residual for now:

```lean
origin_a2_ne_zero_of_a4_a6_origin_order12
```

This is a bounded group-law exclusion lemma, much smaller than the original `tate_normal_form_at_point_of_addOrder12` axiom.
