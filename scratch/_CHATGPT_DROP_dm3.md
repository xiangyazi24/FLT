# Q112 (dm3): SEAM2 project-local glue for x-only differential addition

This is the project-local glue layer around the already-build-ready Kummer algebra.  The polynomial identities are no longer the risky part.  The seam is now:

```lean
xRep : (W⁄ℚ).Point → P1Q
```

plus enough simp lemmas to rewrite Mathlib's `Point.add` into the affine formulae `W.slope`, `W.addX`, and `W.negY`.

The Mathlib declarations used here are the current affine elliptic-curve declarations:

```lean
WeierstrassCurve.Affine.Point.zero
WeierstrassCurve.Affine.Point.some
WeierstrassCurve.Affine.Point.neg_some
WeierstrassCurve.Affine.Point.add_of_X_ne
WeierstrassCurve.Affine.Point.add_of_Y_eq
WeierstrassCurve.Affine.Y_eq_of_X_eq
WeierstrassCurve.Affine.slope_of_X_ne
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.negY
WeierstrassCurve.Affine.nonsingular_neg
WeierstrassCurve.Affine.nonsingular_add
```

Status legend:

```text
CLOSEABLE-NOW          = should compile once names are imported and project aliases are aligned.
MISSING-PROJECT-API    = not Mathlib-missing; needs local `P1Q`/normalization/xRep namespace choices.
MISSING-MATHLIB-API    = genuinely absent from Mathlib.  I do not see any such blocker here.
```

## 1. Projective x-coordinate type and `xRep`

Use a tiny projective line type first.  If the repo already has `RatHat`, `QHat`, or a projective line type, replace this with that type.  For the Kummer seam, all that is needed is equality by cross multiplication.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

noncomputable section

open WeierstrassCurve
open WeierstrassCurve.Affine

/-- Minimal projective rational x-coordinate. -/
structure P1Q where
  X : ℚ
  Z : ℚ
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1Q

/-- Equality in `ℙ¹(ℚ)`. -/
def SameQ (A B : P1Q) : Prop :=
  A.X * B.Z = B.X * A.Z

@[simp] lemma sameQ_refl (A : P1Q) : SameQ A A := by
  dsimp [SameQ]

@[simp] lemma sameQ_mk_iff {A B : P1Q} :
    SameQ A B ↔ A.X * B.Z = B.X * A.Z := Iff.rfl

end P1Q

namespace KummerDiffAdd

variable (W : WeierstrassCurve ℚ)

/-- The point at infinity on the Kummer line. -/
def xInf : P1Q :=
  { X := 1, Z := 0, not_both_zero := Or.inl one_ne_zero }

/-- The affine x-coordinate `[x:1]`. -/
def xAff (x : ℚ) : P1Q :=
  { X := x, Z := 1, not_both_zero := Or.inr one_ne_zero }

/-- Projective x-coordinate.  The group identity maps to `[1:0]`. -/
def xRep : (W⁄ℚ).Point → P1Q
  | .zero => xInf
  | .some x _ _ => xAff x

@[simp] lemma xRep_zero :
    xRep W (0 : (W⁄ℚ).Point) = xInf := rfl

@[simp] lemma xRep_some {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    xRep W (.some x y h : (W⁄ℚ).Point) = xAff x := rfl

@[simp] lemma xRep_some_X {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    (xRep W (.some x y h : (W⁄ℚ).Point)).X = x := rfl

@[simp] lemma xRep_some_Z {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    (xRep W (.some x y h : (W⁄ℚ).Point)).Z = 1 := rfl

@[simp] lemma xInf_X : (xInf : P1Q).X = 1 := rfl
@[simp] lemma xInf_Z : (xInf : P1Q).Z = 0 := rfl
@[simp] lemma xAff_X (x : ℚ) : (xAff x).X = x := rfl
@[simp] lemma xAff_Z (x : ℚ) : (xAff x).Z = 1 := rfl
```

Status: `CLOSEABLE-NOW`.  The only local decision is whether to reuse an existing repo projective-line type.

## 2. Negation preserves x-coordinate

Mathlib's point negation is definitional on affine points:

```lean
WeierstrassCurve.Affine.Point.neg_some
```

It sends `(x,y)` to `(x, W.negY x y)`, so `xRep` is unchanged up to projective equality.  With the above definition it is literally the same affine representative.

```lean
@[simp] lemma xRep_neg_some_same {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    P1Q.SameQ
      (xRep W (-(.some x y h : (W⁄ℚ).Point)))
      (xRep W (.some x y h : (W⁄ℚ).Point)) := by
  simp [xRep, xAff, P1Q.SameQ]

lemma xRep_neg_same (P : (W⁄ℚ).Point) :
    P1Q.SameQ (xRep W (-P)) (xRep W P) := by
  cases P with
  | zero =>
      simp [xRep, xInf, P1Q.SameQ]
  | some x y h =>
      simpa using xRep_neg_some_same (W := W) h
```

Status: `CLOSEABLE-NOW`.

## 3. The Kummer forms

These are the same forms from the algebra layer.

```lean
/-- `δ = X₁Z₂ - X₂Z₁`. -/
def delta (A B : P1Q) : ℚ :=
  A.X * B.Z - B.X * A.Z

/-- Homogeneous numerator for `x₊ + x₋`. -/
def sumNum (A B : P1Q) : ℚ :=
    2 * A.X * B.X * (A.X * B.Z + B.X * A.Z)
  + W.b₂ * A.X * B.X * A.Z * B.Z
  + W.b₄ * A.Z * B.Z * (A.X * B.Z + B.X * A.Z)
  + W.b₆ * A.Z^2 * B.Z^2

/-- Homogeneous numerator for `x₊ * x₋`. -/
def prodNum (A B : P1Q) : ℚ :=
    A.X^2 * B.X^2
  - W.b₄ * A.X * B.X * A.Z * B.Z
  - W.b₆ * (A.X * B.Z + B.X * A.Z) * A.Z * B.Z
  - W.b₈ * A.Z^2 * B.Z^2

lemma delta_eq_zero_of_same {A B : P1Q} (h : P1Q.SameQ A B) :
    delta A B = 0 := by
  dsimp [delta, P1Q.SameQ] at h ⊢
  linear_combination h
```

Status: `CLOSEABLE-NOW`.

## 4. Point.add to addX/slope rewrites

Mathlib's affine point addition is defined by cases:

```lean
Point.add : W.Point → W.Point → W.Point
| 0, P => P
| P, 0 => P
| some x₁ y₁ h₁, some x₂ y₂ h₂ =>
    if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0
    else some _ _ <| nonsingular_add h₁ h₂ hxy
```

For the nonvertical secant case, Mathlib already has:

```lean
WeierstrassCurve.Affine.Point.add_of_X_ne
```

which rewrites the sum to an affine `some` whose x-coordinate is definitionally

```lean
(W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂)
```

The local wrappers should be:

```lean
@[simp] lemma xRep_add_some_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) + (.some x₂ y₂ h₂ : (W⁄ℚ).Point))
      = xAff ((W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂)) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := W⁄ℚ) hx]
  rfl

@[simp] lemma xRep_add_some_X_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) + (.some x₂ y₂ h₂ : (W⁄ℚ).Point))).X
      = (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂) := by
  simp [xRep_add_some_of_X_ne (W := W) hx]

@[simp] lemma xRep_add_some_Z_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) + (.some x₂ y₂ h₂ : (W⁄ℚ).Point))).Z
      = 1 := by
  simp [xRep_add_some_of_X_ne (W := W) hx]
```

Status: `CLOSEABLE-NOW`.  No missing Mathlib API: `Point.add_of_X_ne` exists.

## 5. Rewriting `P - Q`

Use `sub_eq_add_neg`, `Point.neg_some`, and then `Point.add_of_X_ne`.  Negation keeps the same x-coordinate and replaces `y₂` by `(W⁄ℚ).negY x₂ y₂`.

```lean
@[simp] lemma xRep_sub_some_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) - (.some x₂ y₂ h₂ : (W⁄ℚ).Point))
      = xAff ((W⁄ℚ).addX x₁ x₂
          ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂))) := by
  rw [sub_eq_add_neg]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := W⁄ℚ) hx]
  rfl

@[simp] lemma xRep_sub_some_X_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) - (.some x₂ y₂ h₂ : (W⁄ℚ).Point))).X
      = (W⁄ℚ).addX x₁ x₂
          ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂)) := by
  simp [xRep_sub_some_of_X_ne (W := W) hx]

@[simp] lemma xRep_sub_some_Z_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) - (.some x₂ y₂ h₂ : (W⁄ℚ).Point))).Z
      = 1 := by
  simp [xRep_sub_some_of_X_ne (W := W) hx]
```

Status: `CLOSEABLE-NOW`.  If `rw [Point.neg_some]` does not infer `h₂`, use:

```lean
rw [WeierstrassCurve.Affine.Point.neg_some (W' := W⁄ℚ) h₂]
```

or simply:

```lean
simp [sub_eq_add_neg, xRep, WeierstrassCurve.Affine.Point.add_of_X_ne (W := W⁄ℚ) hx]
```

## 6. Nondegeneracy: from `delta ≠ 0` to `(xRep(P-Q)).Z ≠ 0`

The proof is by point cases.  If either point is infinity, it is immediate unless both are infinity, in which case `delta = 0`.  If both are affine, `delta ≠ 0` reduces to `x₁ ≠ x₂`, and the previous `xRep_sub_some_Z_of_X_ne` gives `Z = 1`.

```lean
lemma xRep_sub_Z_ne_zero_of_delta_ne_zero
    (P Q : (W⁄ℚ).Point)
    (hδ : delta (xRep W P) (xRep W Q) ≠ 0) :
    (xRep W (P - Q)).Z ≠ 0 := by
  classical
  cases P with
  | zero =>
      cases Q with
      | zero =>
          simp [xRep, xInf, delta] at hδ
      | some x₂ y₂ h₂ =>
          -- `0 - Q = -Q`, affine, so Z = 1.
          simp [xRep, xInf, xAff, delta, sub_eq_add_neg] at hδ ⊢
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          -- `P - 0 = P`, affine, so Z = 1.
          simp [xRep, xInf, xAff, delta] at hδ ⊢
      | some x₂ y₂ h₂ =>
          have hx : x₁ ≠ x₂ := by
            intro hx
            apply hδ
            simp [xRep, xAff, delta, hx]
          simp [xRep_sub_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx]
```

Status: `CLOSEABLE-NOW`.

This lemma is enough to prove the denominator nonzero in the functional differential-addition theorem:

```lean
lemma addFromSub_not_both_zero
    (P Q : (W⁄ℚ).Point)
    (hδ : delta (xRep W P) (xRep W Q) ≠ 0) :
    (sumNum W (xRep W P) (xRep W Q) * (xRep W (P - Q)).Z
        - (delta (xRep W P) (xRep W Q))^2 * (xRep W (P - Q)).X ≠ 0)
    ∨
    ((delta (xRep W P) (xRep W Q))^2 * (xRep W (P - Q)).Z ≠ 0) := by
  right
  exact mul_ne_zero (sq_ne_zero_iff.mpr hδ)
    (xRep_sub_Z_ne_zero_of_delta_ne_zero (W := W) P Q hδ)
```

Status: `CLOSEABLE-NOW`.

## 7. Degenerate `x₁ = x₂` branch

Mathlib gives:

```lean
WeierstrassCurve.Affine.Y_eq_of_X_eq
```

For nonsingular affine points this yields:

```lean
y₁ = y₂ ∨ y₁ = (W⁄ℚ).negY x₂ y₂
```

If `y₁ = y₂`, then `P = Q`, hence `P-Q=0`, so `Z₋ = 0`.  If `y₁ = negY x₂ y₂`, then `P = -Q`, hence `P+Q=0`, so `Z₊ = 0`.  Since `delta = 0`, both projective Kummer identities become `0 = 0`.

Useful local equalities:

```lean
lemma some_ext_of_xy_eq
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (.some x₁ y₁ h₁ : (W⁄ℚ).Point) = .some x₂ y₂ h₂ := by
  subst hx
  subst hy
  congr

lemma xRep_add_zero_of_Y_eq
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = (W⁄ℚ).negY x₂ y₂) :
    xRep W ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) + .some x₂ y₂ h₂) = xInf := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := W⁄ℚ) hx hy]
  rfl

lemma xRep_sub_zero_of_same_xy
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    xRep W ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) - .some x₂ y₂ h₂) = xInf := by
  have hPQ : (.some x₁ y₁ h₁ : (W⁄ℚ).Point) = .some x₂ y₂ h₂ :=
    some_ext_of_xy_eq (W := W) hx hy
  subst hPQ
  simp [xRep]
```

Status: `CLOSEABLE-NOW`.  If `congr` in `some_ext_of_xy_eq` does not close the proof field, replace the body after `subst`s with:

```lean
have hh : h₁ = h₂ := Subsingleton.elim _ _
subst hh
rfl
```

## 8. Global biquadratic theorem: case split skeleton

Assume the algebra layer has already proved the affine nondegenerate theorem:

```lean
lemma xRep_add_sub_kummer_affine_ne_x
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (W⁄ℚ).Equation x₁ y₁)
    (h₂ : (W⁄ℚ).Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let Y₁ := YsqCoord W x₁ y₁
    let Y₂ := YsqCoord W x₂ y₂
    let xp := (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂)
    let xm := (W⁄ℚ).addX x₁ x₂
      ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂))
    (x₁ - x₂)^2 * (xp + xm) = sumAff W x₁ x₂
    ∧
    (x₁ - x₂)^2 * xp * xm = prodAff W x₁ x₂ := by
  -- already designed in Round 2
  sorry
```

Then the global proof skeleton is:

```lean
theorem xRep_add_sub_kummer_biquadratic
    (P Q : (W⁄ℚ).Point) :
    let A  := xRep W P
    let B  := xRep W Q
    let Xp := xRep W (P + Q)
    let Xm := xRep W (P - Q)
    let D  := (delta A B)^2
    D * (Xp.X * Xm.Z + Xm.X * Xp.Z)
      = sumNum W A B * Xp.Z * Xm.Z
    ∧
    D * Xp.X * Xm.X
      = prodNum W A B * Xp.Z * Xm.Z := by
  classical
  cases P with
  | zero =>
      -- `0 + Q = Q`, `0 - Q = -Q`, `x(-Q) = x(Q)`.
      cases Q with
      | zero =>
          simp [xRep, xInf, delta, sumNum, prodNum]
      | some x₂ y₂ h₂ =>
          simp [xRep, xInf, xAff, delta, sumNum, prodNum,
            P1Q.SameQ, sub_eq_add_neg]
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          -- `P + 0 = P`, `P - 0 = P`.
          simp [xRep, xInf, xAff, delta, sumNum, prodNum]
      | some x₂ y₂ h₂ =>
          by_cases hx : x₁ = x₂
          · have hY := WeierstrassCurve.Affine.Y_eq_of_X_eq
                (W := W⁄ℚ) h₁.left h₂.left hx
            rcases hY with hy_same | hy_neg
            · -- P = Q, so P-Q = 0 and delta = 0.
              have hsub0 :
                  xRep W
                    ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) - .some x₂ y₂ h₂) = xInf :=
                xRep_sub_zero_of_same_xy (W := W) hx hy_same
              simp [xRep, xAff, xInf, delta, sumNum, prodNum, hx, hsub0]
            · -- P = -Q, so P+Q = 0 and delta = 0.
              have hadd0 :
                  xRep W
                    ((.some x₁ y₁ h₁ : (W⁄ℚ).Point) + .some x₂ y₂ h₂) = xInf :=
                xRep_add_zero_of_Y_eq (W := W) hx hy_neg
              simp [xRep, xAff, xInf, delta, sumNum, prodNum, hx, hadd0]
          · -- affine nondegenerate branch
            have hcore := xRep_add_sub_kummer_affine_ne_x
              (W := W) h₁.left h₂.left hx
            rcases hcore with ⟨hsum, hprod⟩
            -- Rewrite `P+Q` and `P-Q` xReps using the local wrappers.
            simp [xRep_add_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx,
                  xRep_sub_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx,
                  xRep, xAff, delta, sumNum, prodNum] at hsum hprod ⊢
            constructor
            · exact hsum
            · exact hprod
```

Status:

```text
CLOSEABLE-NOW after the affine algebra lemma is in namespace and the exact simp normal forms are aligned.
No MISSING-MATHLIB-API.
```

## 9. Functional differential addition theorem

Once the global theorem exists, the exported functional seam is short.

```lean
theorem xRep_add_of_xRep_sub
    (P Q : (W⁄ℚ).Point)
    (hδ : delta (xRep W P) (xRep W Q) ≠ 0) :
    P1Q.SameQ
      (xRep W (P + Q))
      { X := sumNum W (xRep W P) (xRep W Q) * (xRep W (P - Q)).Z
              - (delta (xRep W P) (xRep W Q))^2 * (xRep W (P - Q)).X
        Z := (delta (xRep W P) (xRep W Q))^2 * (xRep W (P - Q)).Z
        not_both_zero := addFromSub_not_both_zero (W := W) P Q hδ } := by
  classical
  rcases xRep_add_sub_kummer_biquadratic (W := W) P Q with ⟨hsum, _hprod⟩
  dsimp [P1Q.SameQ]
  ring_nf at hsum ⊢
  linear_combination hsum
```

Status: `CLOSEABLE-NOW`.

## 10. Exact dependency list

```text
CLOSEABLE-NOW / Mathlib already has:
  Point.zero
  Point.some
  Point.neg_some
  Point.add_of_X_ne
  Point.add_of_Y_eq
  Affine.Y_eq_of_X_eq
  Affine.slope_of_X_ne
  Affine.addX
  Affine.negY
  Affine.nonsingular_neg
  Affine.nonsingular_add

MISSING-PROJECT-API:
  P1Q if not already present;
  xRep namespace and simp tags;
  affine algebra lemma name alignment;
  optional raw-pair normalization if projective coordinates are normalized.

MISSING-MATHLIB-API:
  none identified.
```

## 11. First prototype order

Prototype these in this order:

```lean
xRep
xRep_zero
xRep_some
xRep_neg_same
xRep_add_some_of_X_ne
xRep_sub_some_of_X_ne
xRep_sub_Z_ne_zero_of_delta_ne_zero
xRep_add_sub_kummer_biquadratic
xRep_add_of_xRep_sub
```

The only place I expect elaboration friction is the exact namespace arguments for:

```lean
WeierstrassCurve.Affine.Point.neg_some
WeierstrassCurve.Affine.Point.add_of_X_ne
WeierstrassCurve.Affine.Point.add_of_Y_eq
```

If named rewriting fails, `simp [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add, hx]` is the fallback, because the definitions are by cases and the nonvertical branch is definitionally the `some (addX ...) (addY ...) (nonsingular_add ...)` constructor.
