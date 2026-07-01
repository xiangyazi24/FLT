# Q2945 dm-codex2: continue Kubert residual A after translating order-12 point to origin

Namespace: `MazurProof.KubertBridgeN12`.

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.

I could not fetch the local WIP file through the GitHub connector, so this answer is written against the declarations in the prompt. The checkable parts are: killing `a₄`, preserving origin/order through the variable-change additive equivalence, and scaling to Tate normal form. The only part I would keep as a residual is the affine group-law fact excluding `a₂ = 0` from exact order `12`.

## 0. API probes to paste first

Paste these near the local work area to confirm theorem orientation.

```lean
#check WeierstrassCurve.VariableChange
#check WeierstrassCurve.VariableChange.mk
#check WeierstrassCurve.variableChange_a₁
#check WeierstrassCurve.variableChange_a₂
#check WeierstrassCurve.variableChange_a₃
#check WeierstrassCurve.variableChange_a₄
#check WeierstrassCurve.variableChange_a₆
#check affinePointAddEquivOfVariableChange
#check addOrderOf
#check origin_a3_ne_zero_of_addOrderOf_eq_12
```

The snippets below assume the usual Mathlib variable-change convention:

```text
x = u^2 x' + r,
y = u^3 y' + u^2 s x' + t,
```

so the coefficient formulas are:

```text
u*a1' = a1 + 2*s
u^2*a2' = a2 - s*a1 + 3*r - s^2
u^3*a3' = a3 + r*a1 + 2*t
u^4*a4' = a4 - s*a3 + 2*r*a2 - (t+r*s)*a1 + 3*r^2 - 2*s*t
u^6*a6' = a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1
```

This matches the intended `killA4VC` with `s = W.a₄/W.a₃`: with `u=1,r=0,t=0`, the new `a₄` is `a₄ - s*a₃ = 0`.

## 1. Kill `a₄`

```lean
import Mathlib.Tactic
-- existing imports from KubertBridgeN12.lean

namespace MazurProof.KubertBridgeN12

open scoped WeierstrassCurve.Affine

noncomputable def killA4VC (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk 1 0 (W.a₄ / W.a₃) 0

noncomputable abbrev killA4W (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve ℚ :=
  W.variableChange (killA4VC W h3)

@[simp] theorem killA4VC_u (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4VC W h3).u = 1 := rfl

@[simp] theorem killA4VC_r (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4VC W h3).r = 0 := rfl

@[simp] theorem killA4VC_s (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4VC W h3).s = W.a₄ / W.a₃ := rfl

@[simp] theorem killA4VC_t (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4VC W h3).t = 0 := rfl

/-- Killing `a₄`: this should close by the Mathlib coefficient formula plus `field_simp`. -/
theorem killA4W_a4_eq_zero (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4W W h3).a₄ = 0 := by
  -- If `variableChange_a₄` rewrites in the opposite direction, replace `rw` by `simpa ... using`.
  rw [killA4W, killA4VC, WeierstrassCurve.variableChange_a₄]
  field_simp [h3]
  ring

/-- The same variable change preserves `a₆=0` because `r=t=0,u=1`. -/
theorem killA4W_a6_eq_zero
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) (h6 : W.a₆ = 0) :
    (killA4W W h3).a₆ = 0 := by
  rw [killA4W, killA4VC, WeierstrassCurve.variableChange_a₆]
  simp [h6]

/-- The `a₃` coefficient is unchanged. -/
theorem killA4W_a3_eq
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4W W h3).a₃ = W.a₃ := by
  rw [killA4W, killA4VC, WeierstrassCurve.variableChange_a₃]
  simp

/-- Hence the translated/killed model still has nonzero `a₃`. -/
theorem killA4W_a3_ne_zero
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4W W h3).a₃ ≠ 0 := by
  simpa [killA4W_a3_eq W h3] using h3

end MazurProof.KubertBridgeN12
```

If `rw [WeierstrassCurve.variableChange_a₄]` fails because the theorem has explicit arguments, use:

```lean
  rw [killA4W, killA4VC]
  simp only [WeierstrassCurve.variableChange_a₄]
  field_simp [h3]
  ring
```

If the theorem gives a multiplied formula such as

```lean
(killA4VC W h3).u ^ 4 * (killA4W W h3).a₄ = ...
```

then prove the multiplied RHS is zero and use `norm_num` for `u=1`:

```lean
  have h := WeierstrassCurve.variableChange_a₄ W (killA4VC W h3)
  norm_num [killA4W, killA4VC] at h
  field_simp [h3] at h
  simpa using h
```

## 2. Preserve origin nonsingular/order 12 under `killA4VC`

The clean route is to use the local additive equivalence attached to a variable change. You need a small “map origin to origin” lemma because `r=t=0`.

```lean
namespace MazurProof.KubertBridgeN12

open scoped WeierstrassCurve.Affine

/-- Direct origin nonsingularity after killing `a₄`.  Prefer a direct proof if the local
    nonsingular predicate unfolds well; otherwise get it from the point equivalence below. -/
theorem killA4W_origin_nonsingular
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h6 : W.a₆ = 0)
    (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (killA4W W h3)) 0 0 := by
  -- Robust direct route: at `(0,0)`, the affine equation uses `a₆=0`,
  -- and nonsingularity follows because the y-partial is `a₃`, still nonzero.
  -- If the local API has a point/nonsingular simplifier, this usually works:
  --   unfold killA4W
  --   simpa [WeierstrassCurve.Affine.Nonsingular,
  --     killA4W_a6_eq_zero W h3 h6, killA4W_a3_eq W h3,
  --     killA4W_a4_eq_zero W h3] using h3
  -- If not, use the existing variable-change point equivalence to transport `hO`.
  -- The exact proof depends on the local shape of `Affine.Nonsingular`.
  simpa [killA4W_a6_eq_zero W h3 h6, killA4W_a3_eq W h3,
    killA4W_a4_eq_zero W h3]
    using hO

/-- The variable-change additive equivalence sends the origin to the origin when `r=t=0`. -/
theorem affinePointAddEquivOfVariableChange_killA4_origin
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (hO' : WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (killA4W W h3)) 0 0) :
    affinePointAddEquivOfVariableChange W (killA4VC W h3)
        (WeierstrassCurve.Affine.Point.some 0 0 hO)
      = WeierstrassCurve.Affine.Point.some 0 0 hO' := by
  -- The variable change has `r=t=0`; coordinates are unchanged at `(0,0)`.
  -- Usually:
  ext <;> simp [affinePointAddEquivOfVariableChange, killA4VC, killA4W]

/-- Additive equivalences preserve `addOrderOf`. -/
theorem addOrderOf_apply_addEquiv
    {G H : Type*} [AddGroup G] [AddGroup H]
    (e : G ≃+ H) (P : G) :
    addOrderOf (e P) = addOrderOf P := by
  -- Try first:
  --   simpa using e.addOrderOf_eq P
  -- or:
  --   simpa using (AddEquiv.addOrderOf_eq e P)
  -- Fallback proof by the standard injective hom lemma:
  exact e.toAddMonoidHom.addOrderOf_of_injective e.injective P

/-- Killing `a₄` preserves exact order 12 of the origin. -/
theorem killA4W_origin_order12
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h6 : W.a₆ = 0)
    (h3 : W.a₃ ≠ 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    ∃ hO' : WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (killA4W W h3)) 0 0,
      addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO') = 12 := by
  let hO' := killA4W_origin_nonsingular W hO h6 h3
  refine ⟨hO', ?_⟩
  let e := affinePointAddEquivOfVariableChange W (killA4VC W h3)
  have hmap := affinePointAddEquivOfVariableChange_killA4_origin W h3 hO hO'
  calc
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO')
        = addOrderOf (e (WeierstrassCurve.Affine.Point.some 0 0 hO)) := by rw [hmap]
    _ = addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) := by
          exact addOrderOf_apply_addEquiv e _
    _ = 12 := hOrder

end MazurProof.KubertBridgeN12
```

If `affinePointAddEquivOfVariableChange` is oriented the other way, invert it:

```lean
let e := (affinePointAddEquivOfVariableChange W (killA4VC W h3)).symm
```

and swap the equality in the `hmap` lemma.

## 3. Isolate `a₂ ≠ 0` as the only hard residual

Mathematically, after `a₂=0`, `a₄=0`, `a₆=0`, and `a₃≠0`, the tangent at `(0,0)` is `y=0`, which intersects with multiplicity three at the origin. Hence `2P = -P` and `3P = 0`; exact order `12` is impossible.

This is the minimal residual theorem to isolate:

```lean
namespace MazurProof.KubertBridgeN12

/-- Hard affine group-law residual: if `a₂=a₄=a₆=0`, then the origin has order dividing `3`. -/
def OriginOrderDividesThreeWhenA2A4A6ZeroStatement : Prop :=
  ∀ (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0),
    W.a₂ = 0 → W.a₄ = 0 → W.a₆ = 0 →
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0

/-- This is the usable exclusion theorem. -/
theorem origin_a2_ne_zero_of_a4_a6_origin_order12
    (h3div : OriginOrderDividesThreeWhenA2A4A6ZeroStatement)
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    W.a₂ ≠ 0 := by
  intro h2
  have h3smul : (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 :=
    h3div W hO h2 h4 h6
  -- Standard API variants to try:
  --   exact (addOrderOf_dvd_iff_nsmul_eq_zero.mp ?)
  --   have hdiv : addOrderOf (...) ∣ 3 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3smul
  have hdiv : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) ∣ 3 := by
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3smul
  rw [hOrder] at hdiv
  norm_num at hdiv

end MazurProof.KubertBridgeN12
```

If `addOrderOf_dvd_iff_nsmul_eq_zero` is not the exact name, search:

```lean
#check addOrderOf_dvd_iff_nsmul_eq_zero
#check addOrderOf_dvd_iff
#check nsmul_eq_zero_iff_dvd_addOrderOf
#check AddMonoid.addOrderOf_dvd_iff
```

A direct proof route for the residual with affine APIs, if you want to attack it now:

```lean
-- Desired direct API-level target:
theorem origin_three_nsmul_eq_zero_of_a2_a4_a6_eq_zero
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h2 : W.a₂ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 := by
  -- Route:
  -- 1. Let P = some 0 0 hO.
  -- 2. Use the affine doubling formula at P.
  --    The tangent slope is λ = a₄/a₃ = 0 because h4=0 and hO + h6 imply a₃≠0.
  -- 3. The tangent line is y=0, and with h2,h4,h6 the cubic on y=0 is x^3=0.
  -- 4. Therefore 2P = -P.
  -- 5. Then 3P = P + 2P = P + (-P) = 0.
  -- Likely APIs to inspect:
  --   #check WeierstrassCurve.Affine.Point.neg
  --   #check WeierstrassCurve.Affine.Point.add
  --   #check WeierstrassCurve.Affine.Point.add_def
  --   #check WeierstrassCurve.Affine.Point.double
  --   #check WeierstrassCurve.Affine.Point.two_nsmul
  --   #check WeierstrassCurve.Affine.Point.ext
  -- Keep this isolated; do not block the coefficient normalization on it.
  admit
```

Do not put the `admit` in the actual file; keep `OriginOrderDividesThreeWhenA2A4A6ZeroStatement` as the explicit residual until the group-law API proof is done.

## 4. Scaling to Tate normal form

After killing `a₄`, assume:

```lean
W.a₄ = 0, W.a₆ = 0, W.a₃ ≠ 0, W.a₂ ≠ 0.
```

Use the scaling variable change

```text
u = W.a₃ / W.a₂, r=s=t=0.
```

Then the scaled coefficients are:

```text
a1' = W.a₁ / u = W.a₁ * W.a₂ / W.a₃
a2' = W.a₂ / u^2 = W.a₂^3 / W.a₃^2
a3' = W.a₃ / u^3 = W.a₂^3 / W.a₃^2
a4' = 0
a6' = 0
```

For Tate normal form in the usual convention

```text
y^2 + (1-c)xy - b y = x^3 - b x^2,
```

the coefficients are

```text
a1 = 1-c, a2 = -b, a3 = -b, a4 = 0, a6 = 0.
```

Therefore set

```text
b = - W.a₂^3 / W.a₃^2,
c = 1 - W.a₁ * W.a₂ / W.a₃.
```

Lean skeleton:

```lean
namespace MazurProof.KubertBridgeN12

noncomputable def scaleToTateVC
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk (W.a₃ / W.a₂) 0 0 0

noncomputable abbrev scaleToTateW
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve ℚ :=
  W.variableChange (scaleToTateVC W h2 h3)

noncomputable def tate_b_of_W (W : WeierstrassCurve ℚ) : ℚ :=
  - W.a₂ ^ 3 / W.a₃ ^ 2

noncomputable def tate_c_of_W (W : WeierstrassCurve ℚ) : ℚ :=
  1 - W.a₁ * W.a₂ / W.a₃

@[simp] theorem scaleToTateVC_u
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    (scaleToTateVC W h2 h3).u = W.a₃ / W.a₂ := rfl

/-- New `a₁` after scaling. -/
theorem scaleToTateW_a1
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    (scaleToTateW W h2 h3).a₁ = W.a₁ * W.a₂ / W.a₃ := by
  rw [scaleToTateW, scaleToTateVC, WeierstrassCurve.variableChange_a₁]
  field_simp [h2, h3]
  ring

/-- New `a₂` after scaling. -/
theorem scaleToTateW_a2
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    (scaleToTateW W h2 h3).a₂ = W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleToTateW, scaleToTateVC, WeierstrassCurve.variableChange_a₂]
  field_simp [h2, h3]
  ring

/-- New `a₃` after scaling. -/
theorem scaleToTateW_a3
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    (scaleToTateW W h2 h3).a₃ = W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleToTateW, scaleToTateVC, WeierstrassCurve.variableChange_a₃]
  field_simp [h2, h3]
  ring

/-- New `a₄` after scaling. -/
theorem scaleToTateW_a4
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (h4 : W.a₄ = 0) :
    (scaleToTateW W h2 h3).a₄ = 0 := by
  rw [scaleToTateW, scaleToTateVC, WeierstrassCurve.variableChange_a₄]
  simp [h4]

/-- New `a₆` after scaling. -/
theorem scaleToTateW_a6
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (h6 : W.a₆ = 0) :
    (scaleToTateW W h2 h3).a₆ = 0 := by
  rw [scaleToTateW, scaleToTateVC, WeierstrassCurve.variableChange_a₆]
  simp [h6]

/-- Coefficient equality with the local Tate normal form. -/
theorem scaleToTateW_eq_tateW
    (W : WeierstrassCurve ℚ)
    (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    scaleToTateW W h2 h3 = tateW (tate_b_of_W W) (tate_c_of_W W) := by
  -- Use whatever extensionality theorem is available for `WeierstrassCurve`.
  -- Usually `ext <;> ...` works if the structure fields are exposed.
  ext <;>
    simp [scaleToTateW_a1, scaleToTateW_a2, scaleToTateW_a3,
      scaleToTateW_a4, scaleToTateW_a6,
      tateW, tate_b_of_W, tate_c_of_W, h2, h3, h4, h6] <;>
    field_simp [h2, h3] <;>
    ring

end MazurProof.KubertBridgeN12
```

If `tateW b c` uses the opposite sign convention

```text
y^2 + (1-c)xy - b y = x^3 - b x^2
```

then the above `b = -a2'` is correct. If local `tateW` was defined with `a₂=b, a₃=b`, change to:

```lean
noncomputable def tate_b_of_W (W : WeierstrassCurve ℚ) : ℚ :=
  W.a₂ ^ 3 / W.a₃ ^ 2
```

and the `field_simp/ring` proof will immediately reveal the sign.

## 5. End-to-end residual A package

Once `origin_a2_ne_zero_of_a4_a6_origin_order12` is available, residual A should produce a Tate normal form from the translated-origin curve.

```lean
namespace MazurProof.KubertBridgeN12

structure OriginOrder12A4A6Killed where
  W : WeierstrassCurve ℚ
  hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0
  hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12
  h3 : W.a₃ ≠ 0
  h4 : W.a₄ = 0
  h6 : W.a₆ = 0

noncomputable def OriginOrder12A4A6Killed.toTate_b (S : OriginOrder12A4A6Killed) : ℚ :=
  tate_b_of_W S.W

noncomputable def OriginOrder12A4A6Killed.toTate_c (S : OriginOrder12A4A6Killed) : ℚ :=
  tate_c_of_W S.W

/-- Final coefficient-normalization step, with only the `a₂≠0` theorem consumed. -/
theorem originOrder12A4A6Killed_scale_to_tate
    (hA2 : ∀ (W : WeierstrassCurve ℚ)
      (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0),
      W.a₄ = 0 → W.a₆ = 0 →
      addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12 →
      W.a₂ ≠ 0)
    (S : OriginOrder12A4A6Killed) :
    ∃ h2 : S.W.a₂ ≠ 0,
      scaleToTateW S.W h2 S.h3 =
        tateW (OriginOrder12A4A6Killed.toTate_b S)
              (OriginOrder12A4A6Killed.toTate_c S) := by
  let h2 : S.W.a₂ ≠ 0 := hA2 S.W S.hO S.h4 S.h6 S.hOrder
  exact ⟨h2, scaleToTateW_eq_tateW S.W h2 S.h3 S.h4 S.h6⟩

end MazurProof.KubertBridgeN12
```

This keeps the frontier honest:

```text
checked now:
  translate origin order-12 point to `(0,0)`
  prove a₃ ≠ 0
  kill a₄ while preserving a₆=0 and order 12
  scale to Tate form once a₂ ≠ 0

residual only:
  a₂ ≠ 0 from exact order 12 when a₄=a₆=0
```

## 6. Practical order of edits

1. Add `killA4VC`, `killA4W_a4_eq_zero`, `killA4W_a6_eq_zero`, `killA4W_a3_eq`.
2. Add origin/order preservation through `affinePointAddEquivOfVariableChange`.
3. Add `OriginOrderDividesThreeWhenA2A4A6ZeroStatement` and the wrapper `origin_a2_ne_zero_of_a4_a6_origin_order12` consuming it.
4. Add `scaleToTateVC`, `tate_b_of_W`, `tate_c_of_W`, and `scaleToTateW_eq_tateW`.
5. Only then attack the residual group-law lemma proving `3 • (0,0)=0` under `a₂=a₄=a₆=0`.
