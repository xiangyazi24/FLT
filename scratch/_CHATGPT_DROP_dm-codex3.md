# Q2946: Tate normal form `2P` and `3P` using Mathlib affine group law

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.
Namespace: `MazurProof.KubertBridgeN12`.

I could not fetch the local WIP file from GitHub, so this is written against the pasted definitions and current Mathlib affine API. The relevant Mathlib names are:

```lean
#check WeierstrassCurve.Affine.Point.add_self_of_Y_ne
#check WeierstrassCurve.Affine.Point.add_of_X_ne
#check WeierstrassCurve.Affine.Point.add_some
#check WeierstrassCurve.Affine.slope_of_Y_ne
#check WeierstrassCurve.Affine.slope_of_X_ne
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.negAddY
#check WeierstrassCurve.Affine.negY
#check two_nsmul
#check three_nsmul
```

## Code to add after `tateOriginAffine`

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN12

open WeierstrassCurve

/-- `2P=(b,bc)` is nonsingular on the Tate normal form, assuming only `b≠0`. -/
theorem tateW_P2_nonsingular (b c : ℚ) (hb : b ≠ 0) :
    (tateW b c).Nonsingular b (b * c) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [tateW]
    ring
  · by_cases hc : c = 0
    · left
      intro h
      dsimp [tateW] at h
      rw [hc] at h
      have hb2pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      nlinarith
    · right
      intro h
      dsimp [tateW, WeierstrassCurve.Affine.negY] at h
      ring_nf at h
      exact (mul_ne_zero hb hc) h

/-- `3P=(c,b-c)` is nonsingular on the Tate normal form, assuming only `b≠0`. -/
theorem tateW_P3_nonsingular (b c : ℚ) (hb : b ≠ 0) :
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
      have hc0 : c = 0 := by
        have hprod : c * (c * c) = 0 := by
          simpa [pow_succ, pow_two, mul_assoc] using hX
        rcases mul_eq_zero.mp hprod with hc | hcc
        · exact hc
        · rcases mul_eq_zero.mp hcc with hc | hc
          · exact hc
          · exact hc
      have hb0 : b = 0 := by nlinarith
      exact hb hb0
    · right
      intro hneg
      dsimp [tateW, WeierstrassCurve.Affine.negY] at hneg
      ring_nf at hneg
      exact hY hneg

noncomputable def tateP2 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some b (b * c) (tateW_P2_nonsingular b c hb)

noncomputable def tateP3 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some c (b - c) (tateW_P3_nonsingular b c hb)

private theorem tate_origin_not_vertical (b c : ℚ) (hb : b ≠ 0) :
    (0 : ℚ) ≠ (tateW b c).negY 0 0 := by
  dsimp [tateW, WeierstrassCurve.Affine.negY]
  exact hb.symm

private theorem tate_add_origin_P2_x_ne (b c : ℚ) (hb : b ≠ 0) :
    b ≠ (0 : ℚ) := hb

/-- The tangent computation `2P=(b,bc)`. -/
theorem tate_origin_twoP_eq (b c : ℚ) (hb : b ≠ 0) :
    2 • tateOriginAffine b c hb = tateP2 b c hb := by
  rw [two_nsmul]
  unfold tateOriginAffine tateP2
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (W := tateW b c) (tate_origin_not_vertical b c hb)]
  -- The addition formula now has coordinates
  -- `addX 0 0 slope = b`, `addY 0 0 0 slope = b*c`.
  congr <;>
    dsimp [tateW, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY] <;>
    field_simp [hb] <;>
    ring

/-- The secant computation `3P=(c,b-c)`. -/
theorem tate_origin_threeP_eq (b c : ℚ) (hb : b ≠ 0) :
    3 • tateOriginAffine b c hb = tateP3 b c hb := by
  -- Put `3P` as `(2P)+P`, then use the checked `2P` formula.
  rw [three_nsmul]
  change (2 • tateOriginAffine b c hb) + tateOriginAffine b c hb = tateP3 b c hb
  rw [tate_origin_twoP_eq b c hb]
  unfold tateP2 tateP3 tateOriginAffine
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := tateW b c) (tate_add_origin_P2_x_ne b c hb)]
  -- The addition formula now has slope `(b*c-0)/(b-0)=c` and coordinates `(c,b-c)`.
  congr <;>
    dsimp [tateW, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY] <;>
    field_simp [hb] <;>
    ring

end MazurProof.KubertBridgeN12
```

## If `three_nsmul` does not rewrite to `(2 • P)+P`

In some local elaboration contexts, `three_nsmul` rewrites to `P + P + P` and the `change` line may not fire. Use this replacement prefix for `tate_origin_threeP_eq`:

```lean
  rw [three_nsmul, ← two_nsmul]
  rw [tate_origin_twoP_eq b c hb]
```

or, more explicitly:

```lean
  show (tateOriginAffine b c hb + tateOriginAffine b c hb) +
        tateOriginAffine b c hb = tateP3 b c hb
  rw [← two_nsmul, tate_origin_twoP_eq b c hb]
```

## If `congr` fails on `Point.some` proof terms

The constructor proof argument is a `Prop`, so proof irrelevance should let `congr` close the proof field. If it does not, add this helper once:

```lean
private theorem point_some_ext {W : WeierstrassCurve.Affine ℚ}
    {x y x' y' : ℚ} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  congr
```

Then replace the `congr <;> ...` tail in each theorem by:

```lean
  apply point_some_ext
  · dsimp [tateW, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX]
    field_simp [hb]
    ring
  · dsimp [tateW, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    field_simp [hb]
    ring
```

## Side conditions

No additional side conditions beyond `hb : b ≠ 0` are needed for `2P` and `3P`.

* `2P`: if `c=0`, nonsingularity is certified by the `X`-partial (`b^2≠0`); if `c≠0`, by the `Y`-partial.
* `3P`: if `b-c≠c^2`, the `Y`-partial certifies nonsingularity; if `b-c=c^2`, the `X`-partial would be singular only when `c=0`, which would force `b=0`, contradicting `hb`.

The next theorem `4P` does need `c≠0`, because the secant through `P` and `3P` uses slope `(b-c)/c`.
