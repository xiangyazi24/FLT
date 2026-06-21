import Mathlib
import scratch.Seam2Proto
import FLT.EllipticCurve.Torsion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

namespace Seam2Wired

/-- Minimal projective rational x-coordinate. -/
structure P1Q where
  X : ℚ
  Z : ℚ
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1Q

/-- Equality in `P¹(ℚ)`, by cross multiplication. -/
def SameQ (A B : P1Q) : Prop :=
  A.X * B.Z = B.X * A.Z

@[simp] lemma sameQ_refl (A : P1Q) : SameQ A A := by
  dsimp [SameQ]

@[simp] lemma sameQ_mk_iff {A B : P1Q} :
    SameQ A B ↔ A.X * B.Z = B.X * A.Z := Iff.rfl

end P1Q

variable (W : WeierstrassCurve ℚ)

/-- The point at infinity on the Kummer line. -/
def xInf : P1Q :=
  { X := 1, Z := 0, not_both_zero := Or.inl one_ne_zero }

/-- The affine x-coordinate `[x : 1]`. -/
def xAff (x : ℚ) : P1Q :=
  { X := x, Z := 1, not_both_zero := Or.inr one_ne_zero }

/-- Projective x-coordinate. The group identity maps to `[1 : 0]`. -/
def xRep : (W⁄ℚ).Point → P1Q
  | 0 => xInf
  | Point.some x _ _ => xAff x

@[simp] lemma xRep_zero :
    xRep W (0 : (W⁄ℚ).Point) = xInf := rfl

@[simp] lemma xRep_some {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    xRep W (Point.some x y h : (W⁄ℚ).Point) = xAff x := rfl

@[simp] lemma xRep_some_X {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    (xRep W (Point.some x y h : (W⁄ℚ).Point)).X = x := rfl

@[simp] lemma xRep_some_Z {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    (xRep W (Point.some x y h : (W⁄ℚ).Point)).Z = 1 := rfl

@[simp] lemma xInf_X : (xInf : P1Q).X = 1 := rfl
@[simp] lemma xInf_Z : (xInf : P1Q).Z = 0 := rfl
@[simp] lemma xAff_X (x : ℚ) : (xAff x).X = x := rfl
@[simp] lemma xAff_Z (x : ℚ) : (xAff x).Z = 1 := rfl

@[simp] lemma xRep_neg_some_same {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    P1Q.SameQ
      (xRep W (-(Point.some x y h : (W⁄ℚ).Point)))
      (xRep W (Point.some x y h : (W⁄ℚ).Point)) := by
  simp [xRep, xAff, P1Q.SameQ]

lemma xRep_neg_same (P : (W⁄ℚ).Point) :
    P1Q.SameQ (xRep W (-P)) (xRep W P) := by
  cases P with
  | zero =>
      rw [show -(Point.zero : (W⁄ℚ).Point) = 0 by rfl]
      simp [xRep, xInf, P1Q.SameQ]
  | some x y h =>
      exact xRep_neg_some_same (W := W) h

/-- `δ = X₁Z₂ - X₂Z₁`. -/
def delta (A B : P1Q) : ℚ :=
  A.X * B.Z - B.X * A.Z

/-- Homogeneous numerator for `x₊ + x₋`. -/
def sumNum (A B : P1Q) : ℚ :=
    2 * A.X * B.X * (A.X * B.Z + B.X * A.Z)
  + W.b₂ * A.X * B.X * A.Z * B.Z
  + W.b₄ * A.Z * B.Z * (A.X * B.Z + B.X * A.Z)
  + W.b₆ * A.Z ^ 2 * B.Z ^ 2

/-- Homogeneous numerator for `x₊ * x₋`. -/
def prodNum (A B : P1Q) : ℚ :=
    A.X ^ 2 * B.X ^ 2
  - W.b₄ * A.X * B.X * A.Z * B.Z
  - W.b₆ * (A.X * B.Z + B.X * A.Z) * A.Z * B.Z
  - W.b₈ * A.Z ^ 2 * B.Z ^ 2

lemma delta_eq_zero_of_same {A B : P1Q} (h : P1Q.SameQ A B) :
    delta A B = 0 := by
  dsimp [delta, P1Q.SameQ] at h ⊢
  linear_combination h

private lemma baseChange_negY_eq (x y : ℚ) :
    (W⁄ℚ).negY x y = W.toAffine.negY x y := by
  simp [WeierstrassCurve.Affine.negY]

private lemma baseChange_addX_eq (x₁ x₂ l : ℚ) :
    (W⁄ℚ).addX x₁ x₂ l = W.toAffine.addX x₁ x₂ l := by
  simp [WeierstrassCurve.Affine.addX]

private lemma baseChange_slope_eq (x₁ x₂ y₁ y₂ : ℚ) :
    (W⁄ℚ).slope x₁ x₂ y₁ y₂ = W.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.toAffine.negY x₂ y₂
    · have hy' : y₁ = (W⁄ℚ).negY x₂ y₂ := by
        simpa [WeierstrassCurve.Affine.negY] using hy
      simp [WeierstrassCurve.Affine.slope, hx, hy, hy']
    · have hy' : y₁ ≠ (W⁄ℚ).negY x₂ y₂ := by
        simpa [WeierstrassCurve.Affine.negY] using hy
      simp [WeierstrassCurve.Affine.slope, hx, hy, hy']
  · simp [WeierstrassCurve.Affine.slope, hx]

private lemma addX_eq_completed_square_formula_base_of_ne_x
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂) =
      (((Seam2Proto.YsqCoord W x₁ y₁ - Seam2Proto.YsqCoord W x₂ y₂) / (x₁ - x₂)) ^ 2
          - W.b₂) / 4 - x₁ - x₂ := by
  rw [baseChange_slope_eq (W := W) x₁ x₂ y₁ y₂]
  simpa [WeierstrassCurve.Affine.addX] using
    Seam2Proto.addX_eq_completed_square_formula_of_ne_x
      (W := W) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂) hx

private lemma subX_eq_completed_square_formula_base_of_ne_x
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂)) =
      (((Seam2Proto.YsqCoord W x₁ y₁ + Seam2Proto.YsqCoord W x₂ y₂) / (x₁ - x₂)) ^ 2
          - W.b₂) / 4 - x₁ - x₂ := by
  rw [baseChange_slope_eq (W := W) x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂)]
  rw [baseChange_negY_eq (W := W) x₂ y₂]
  simpa [WeierstrassCurve.Affine.addX] using
    Seam2Proto.subX_eq_completed_square_formula_of_ne_x
      (W := W) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂) hx

@[simp] lemma xRep_add_some_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) + Point.some x₂ y₂ h₂)
      = xAff ((W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂)) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := W⁄ℚ) hx]
  rfl

@[simp] lemma xRep_add_some_X_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) + Point.some x₂ y₂ h₂)).X
      = (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂) := by
  simp [xRep_add_some_of_X_ne (W := W) hx]

@[simp] lemma xRep_add_some_Z_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) + Point.some x₂ y₂ h₂)).Z = 1 := by
  simp [xRep_add_some_of_X_ne (W := W) hx]

@[simp] lemma xRep_sub_some_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) - Point.some x₂ y₂ h₂)
      = xAff ((W⁄ℚ).addX x₁ x₂
          ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂))) := by
  rw [sub_eq_add_neg]
  rw [WeierstrassCurve.Affine.Point.neg_some (W' := W⁄ℚ) h₂]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := W⁄ℚ) hx]
  rfl

@[simp] lemma xRep_sub_some_X_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) - Point.some x₂ y₂ h₂)).X
      = (W⁄ℚ).addX x₁ x₂
          ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂)) := by
  simp [xRep_sub_some_of_X_ne (W := W) hx]

@[simp] lemma xRep_sub_some_Z_of_X_ne
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    (xRep W
      ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) - Point.some x₂ y₂ h₂)).Z = 1 := by
  simp [xRep_sub_some_of_X_ne (W := W) hx]

lemma xRep_add_sub_kummer_affine_ne_x
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (W⁄ℚ).Equation x₁ y₁)
    (h₂ : (W⁄ℚ).Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let xp := (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂)
    let xm := (W⁄ℚ).addX x₁ x₂
      ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂))
    (x₁ - x₂) ^ 2 * (xp + xm) =
      2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆
    ∧
    (x₁ - x₂) ^ 2 * xp * xm =
      x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈ := by
  have hY₁ : Seam2Proto.YsqCoord W x₁ y₁ ^ 2 = Seam2Proto.fY W x₁ :=
    Seam2Proto.YsqCoord_sq_of_equation (W := W) h₁
  have hY₂ : Seam2Proto.YsqCoord W x₂ y₂ ^ 2 = Seam2Proto.fY W x₂ :=
    Seam2Proto.YsqCoord_sq_of_equation (W := W) h₂
  constructor
  · change
      (x₁ - x₂) ^ 2 *
        ((W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂) +
          (W⁄ℚ).addX x₁ x₂
            ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂))) =
        2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆
    rw [addX_eq_completed_square_formula_base_of_ne_x (W := W) hx,
      subX_eq_completed_square_formula_base_of_ne_x (W := W) hx]
    simpa [Seam2Proto.xPlusFormula, Seam2Proto.xMinusFormula] using
      Seam2Proto.differential_addition_affine_sum_cert
        (W := W) (x₁ := x₁) (x₂ := x₂)
        (Y₁ := Seam2Proto.YsqCoord W x₁ y₁)
        (Y₂ := Seam2Proto.YsqCoord W x₂ y₂) hx hY₁ hY₂
  · change
      (x₁ - x₂) ^ 2 *
          (W⁄ℚ).addX x₁ x₂ ((W⁄ℚ).slope x₁ x₂ y₁ y₂) *
        (W⁄ℚ).addX x₁ x₂
          ((W⁄ℚ).slope x₁ x₂ y₁ ((W⁄ℚ).negY x₂ y₂)) =
        x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈
    rw [addX_eq_completed_square_formula_base_of_ne_x (W := W) hx,
      subX_eq_completed_square_formula_base_of_ne_x (W := W) hx]
    simpa [Seam2Proto.xPlusFormula, Seam2Proto.xMinusFormula] using
      Seam2Proto.differential_addition_affine_prod_cert
        (W := W) (x₁ := x₁) (x₂ := x₂)
        (Y₁ := Seam2Proto.YsqCoord W x₁ y₁)
        (Y₂ := Seam2Proto.YsqCoord W x₂ y₂) hx hY₁ hY₂

lemma some_ext_of_xy_eq
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  congr

lemma xRep_add_zero_of_Y_eq
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = (W⁄ℚ).negY x₂ y₂) :
    xRep W ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) + Point.some x₂ y₂ h₂) = xInf := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := W⁄ℚ) hx hy]
  rfl

lemma xRep_sub_zero_of_same_xy
    {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (W⁄ℚ).Nonsingular x₁ y₁}
    {h₂ : (W⁄ℚ).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    xRep W ((Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) - Point.some x₂ y₂ h₂) = xInf := by
  have hPQ : (Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) = Point.some x₂ y₂ h₂ :=
    some_ext_of_xy_eq (W := W) hx hy
  rw [hPQ]
  simp [xRep]

set_option maxHeartbeats 2000000 in
-- The affine/degenerate point case split finishes with expanded rational normal forms.
theorem xRep_add_sub_kummer_biquadratic
    (P Q : (W⁄ℚ).Point) :
    let A := xRep W P
    let B := xRep W Q
    let Xp := xRep W (P + Q)
    let Xm := xRep W (P - Q)
    let D := (delta A B) ^ 2
    D * (Xp.X * Xm.Z + Xm.X * Xp.Z)
      = sumNum W A B * Xp.Z * Xm.Z
    ∧
    D * Xp.X * Xm.X
      = prodNum W A B * Xp.Z * Xm.Z := by
  classical
  cases P with
  | zero =>
      cases Q with
      | zero =>
          simp [xRep, xInf, delta, sumNum, prodNum]
      | some x₂ y₂ h₂ =>
          rw [show Point.zero + Point.some x₂ y₂ h₂ =
                (Point.some x₂ y₂ h₂ : (W⁄ℚ).Point) by rfl]
          rw [show Point.zero - Point.some x₂ y₂ h₂ =
                -(Point.some x₂ y₂ h₂ : (W⁄ℚ).Point) by rfl]
          simp [xRep, xInf, xAff, delta, sumNum, prodNum]
          constructor <;> ring_nf
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          rw [show Point.some x₁ y₁ h₁ + Point.zero =
                (Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) by rfl]
          rw [show Point.some x₁ y₁ h₁ - Point.zero =
                (Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) by rfl]
          simp [xRep, xInf, xAff, delta, sumNum, prodNum]
          constructor <;> ring_nf
      | some x₂ y₂ h₂ =>
          by_cases hx_eq : x₁ = x₂
          · have hY := WeierstrassCurve.Affine.Y_eq_of_X_eq
                (W := W⁄ℚ) h₁.left h₂.left hx_eq
            rcases hY with hy_same | hy_neg
            · subst x₁
              subst y₁
              have hsub0 :
                  xRep W
                    ((Point.some x₂ y₂ h₁ : (W⁄ℚ).Point) - Point.some x₂ y₂ h₂) = xInf :=
                xRep_sub_zero_of_same_xy (W := W) rfl rfl
              rw [hsub0]
              simp [xRep, xAff, xInf, delta, sumNum, prodNum]
            · subst x₁
              have hadd0 :
                  xRep W
                    ((Point.some x₂ y₁ h₁ : (W⁄ℚ).Point) + Point.some x₂ y₂ h₂) = xInf :=
                xRep_add_zero_of_Y_eq (W := W) rfl hy_neg
              rw [hadd0]
              simp [xRep, xAff, xInf, delta, sumNum, prodNum]
          · have hx : x₁ ≠ x₂ := hx_eq
            have hcore := xRep_add_sub_kummer_affine_ne_x
              (W := W) h₁.left h₂.left hx
            rcases hcore with ⟨hsum, hprod⟩
            rw [xRep_add_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx,
              xRep_sub_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx]
            constructor
            · simp [xRep, xAff, delta, sumNum, prodNum] at hsum ⊢
              ring_nf at hsum ⊢
              exact hsum
            · simp [xRep, xAff, delta, sumNum, prodNum] at hprod ⊢
              ring_nf at hprod ⊢
              exact hprod

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
          rw [show Point.zero - Point.some x₂ y₂ h₂ =
                -(Point.some x₂ y₂ h₂ : (W⁄ℚ).Point) by rfl]
          simp [xRep, xInf, xAff, delta] at hδ ⊢
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          rw [show Point.some x₁ y₁ h₁ - Point.zero =
                (Point.some x₁ y₁ h₁ : (W⁄ℚ).Point) by rfl]
          simp [xRep, xInf, xAff, delta] at hδ ⊢
      | some x₂ y₂ h₂ =>
          have hx : x₁ ≠ x₂ := by
            intro hx
            apply hδ
            simp [xRep, xAff, delta, hx]
          simp [xRep_sub_some_of_X_ne (W := W) (h₁ := h₁) (h₂ := h₂) hx]

lemma addFromSub_not_both_zero
    (P Q : (W⁄ℚ).Point)
    (hδ : delta (xRep W P) (xRep W Q) ≠ 0) :
    (sumNum W (xRep W P) (xRep W Q) * (xRep W (P - Q)).Z
        - (delta (xRep W P) (xRep W Q)) ^ 2 * (xRep W (P - Q)).X ≠ 0)
    ∨
    ((delta (xRep W P) (xRep W Q)) ^ 2 * (xRep W (P - Q)).Z ≠ 0) := by
  right
  exact mul_ne_zero (pow_ne_zero 2 hδ)
    (xRep_sub_Z_ne_zero_of_delta_ne_zero (W := W) P Q hδ)

set_option maxHeartbeats 2000000 in
-- The exported formula is a cross-multiplied homogeneous identity normalized by `ring_nf`.
theorem xRep_add_of_xRep_sub
    (P Q : (W⁄ℚ).Point)
    (hδ : delta (xRep W P) (xRep W Q) ≠ 0) :
    P1Q.SameQ
      (xRep W (P + Q))
      { X := sumNum W (xRep W P) (xRep W Q) * (xRep W (P - Q)).Z
              - (delta (xRep W P) (xRep W Q)) ^ 2 * (xRep W (P - Q)).X
        Z := (delta (xRep W P) (xRep W Q)) ^ 2 * (xRep W (P - Q)).Z
        not_both_zero := addFromSub_not_both_zero (W := W) P Q hδ } := by
  classical
  rcases xRep_add_sub_kummer_biquadratic (W := W) P Q with ⟨hsum, _hprod⟩
  dsimp [P1Q.SameQ]
  ring_nf at hsum ⊢
  linear_combination hsum

end Seam2Wired
