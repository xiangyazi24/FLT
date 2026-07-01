# Q2962: narrow Tate normal form addition proof brick

Target: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.
Namespace: `MazurProof.KubertBridgeN12`.

The code below is intentionally split into small branch/slope/add-coordinate lemmas. This avoids the previous failure mode where `simp` had to solve all `slope/addX/addY` branches at once.

Relevant Mathlib APIs:

```lean
#check WeierstrassCurve.Affine.Point.add_self_of_Y_ne
#check WeierstrassCurve.Affine.Point.add_of_X_ne
#check WeierstrassCurve.Affine.slope_of_Y_ne
#check WeierstrassCurve.Affine.slope_of_X_ne
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.negAddY
#check WeierstrassCurve.Affine.negY
#check WeierstrassCurve.Affine.nonsingular_iff
#check WeierstrassCurve.Affine.equation_iff
```

## Code-first brick

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN12

open WeierstrassCurve

private theorem point_some_ext {W : WeierstrassCurve.Affine ℚ}
    {x y x' y' : ℚ} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  congr

@[simp] theorem tateW_negY_origin (b c : ℚ) :
    (tateW b c).negY 0 0 = b := by
  dsimp [tateW, WeierstrassCurve.Affine.negY]
  ring

@[simp] theorem tateW_negY_P2 (b c : ℚ) :
    (tateW b c).negY b (b * c) = 0 := by
  dsimp [tateW, WeierstrassCurve.Affine.negY]
  ring

@[simp] theorem tateW_negY_P3 (b c : ℚ) :
    (tateW b c).negY c (b - c) = c ^ 2 := by
  dsimp [tateW, WeierstrassCurve.Affine.negY]
  ring

/-- `2P=(b,bc)` is nonsingular. No condition beyond `b≠0` is needed. -/
theorem tateP2_nonsingular (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).Nonsingular b (b * c) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [tateW]
    ring
  · by_cases hc : c = 0
    · left
      intro hX
      dsimp [tateW] at hX
      rw [hc] at hX
      have hb2pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      nlinarith
    · right
      rw [tateW_negY_P2]
      exact mul_ne_zero hb hc

/-- `3P=(c,b-c)` is nonsingular. No condition beyond `b≠0` is needed. -/
theorem tateP3_nonsingular (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).Nonsingular c (b - c) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [tateW]
    ring
  · by_cases hY : b - c = c ^ 2
    · left
      intro hX
      dsimp [tateW] at hX
      have hbexpr : b = c + c ^ 2 := by nlinarith
      rw [hbexpr] at hX
      ring_nf at hX
      have hccc : c * c * c = 0 := by
        nlinarith
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp hccc with hcc | hc
        · exact eq_zero_of_mul_self_eq_zero hcc
        · exact hc
      have hb0 : b = 0 := by
        rw [hbexpr, hc0]
        norm_num
      exact hb hb0
    · right
      rw [tateW_negY_P3]
      exact hY

noncomputable def tateP2 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some b (b * c) (tateP2_nonsingular b c hb)

noncomputable def tateP3 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some c (b - c) (tateP3_nonsingular b c hb)

/-- The tangent at `(0,0)` is horizontal. -/
theorem tate_slope_origin_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).slope 0 0 0 0 = 0 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne (W := tateW b c) rfl]
  · dsimp [tateW, WeierstrassCurve.Affine.negY]
    field_simp [hb]
  · rw [tateW_negY_origin]
    exact hb.symm

@[simp] theorem tate_addX_origin_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).addX 0 0 ((tateW b c).slope 0 0 0 0) = b := by
  rw [tate_slope_origin_origin b c hb]
  dsimp [tateW, WeierstrassCurve.Affine.addX]
  ring

@[simp] theorem tate_addY_origin_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).addY 0 0 0 ((tateW b c).slope 0 0 0 0) = b * c := by
  rw [tate_slope_origin_origin b c hb]
  dsimp [tateW, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
  ring

/-- The secant through `(b,bc)` and `(0,0)` has slope `c`. -/
theorem tate_slope_P2_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).slope b 0 (b * c) 0 = c := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (W := tateW b c) hb]
  field_simp [hb]
  ring

@[simp] theorem tate_addX_P2_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).addX b 0 ((tateW b c).slope b 0 (b * c) 0) = c := by
  rw [tate_slope_P2_origin b c hb]
  dsimp [tateW, WeierstrassCurve.Affine.addX]
  ring

@[simp] theorem tate_addY_P2_origin (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).addY b 0 (b * c) ((tateW b c).slope b 0 (b * c) 0) = b - c := by
  rw [tate_slope_P2_origin b c hb]
  dsimp [tateW, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
  ring

/-- Direct affine group-law proof of `P+P=(b,bc)`. -/
theorem tate_origin_twoP_eq (b c : ℚ) (hb : b ≠ 0) :
    tateOriginAffine b c hb + tateOriginAffine b c hb = tateP2 b c hb := by
  unfold tateOriginAffine tateP2
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (W := tateW b c) (by
      rw [tateW_negY_origin]
      exact hb.symm)]
  apply point_some_ext
  · exact tate_addX_origin_origin b c hb
  · exact tate_addY_origin_origin b c hb

/-- Direct affine group-law proof of `(P+P)+P=(c,b-c)`.

This avoids `three_nsmul`/associativity rewriting. -/
theorem tate_origin_threeP_eq (b c : ℚ) (hb : b ≠ 0) :
    (tateOriginAffine b c hb + tateOriginAffine b c hb) + tateOriginAffine b c hb =
      tateP3 b c hb := by
  rw [tate_origin_twoP_eq b c hb]
  unfold tateP2 tateOriginAffine tateP3
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := tateW b c) hb]
  apply point_some_ext
  · exact tate_addX_P2_origin b c hb
  · exact tate_addY_P2_origin b c hb

end MazurProof.KubertBridgeN12
```

## If the `rw [Point.add_*]` lines do not elaborate

Use the fully explicit theorem names from `Point.lean`:

```lean
rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
  (W := tateW b c) (x₁ := 0) (y₁ := 0)
  (hy := by rw [tateW_negY_origin]; exact hb.symm)]

rw [WeierstrassCurve.Affine.Point.add_of_X_ne
  (W := tateW b c) (x₁ := b) (x₂ := 0)
  (y₁ := b*c) (y₂ := 0) (hx := hb)]
```

The branch conditions are:

* doubling: `0 ≠ negY(0,0)=b`, solved by `hb`;
* adding `P2+P`: `b ≠ 0`, again exactly `hb`.

No `c ≠ 0` is needed for `2P` or `3P`; `c ≠ 0` first appears when computing `4P` from the secant through `P` and `3P`.
