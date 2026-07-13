import FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints

/-!
# The rational two-isogeny quotient

This file constructs the degree-two Vélu quotient of an elliptic curve with a
rational point of order two.  The algebraic core is first proved for

`y² = x³ + A*x² + B*x`.

The target model is `y² = x³ - 2*A*x² + (A² - 4*B)*x`.  The general
Weierstrass curve is reduced to this model by an admissible variable change.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.Velu2Isogeny

open WeierstrassCurve.Affine
open MazurProof.N18RouteC.VariableChangePoints

noncomputable section

local instance : DecidableEq ℚ := Classical.decEq ℚ

def disc (A B : ℚ) : ℚ := A ^ 2 - 4 * B

def sourceEquationModel (A B x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + A * x ^ 2 + B * x

def targetEquationModel (A B x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 - 2 * A * x ^ 2 + disc A B * x

variable {A B : ℚ}

/-! ## The two elliptic curves -/

def sourceCurveModel : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := B
  a₆ := 0

def targetCurveModel : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -2 * A
  a₃ := 0
  a₄ := disc A B
  a₆ := 0


theorem sourceCurve_delta : (sourceCurveModel (A := A) (B := B)).Δ = 16 * B ^ 2 * disc A B := by
  simp [sourceCurveModel, disc, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem targetCurve_delta : (targetCurveModel (A := A) (B := B)).Δ = 256 * B * (disc A B) ^ 2 := by
  simp [targetCurveModel, disc, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

variable [sourceCurve_isElliptic : (sourceCurveModel (A := A) (B := B)).IsElliptic]

include sourceCurve_isElliptic in
theorem source_B_ne_zero : B ≠ 0 := by
  intro hB
  have hΔ : (sourceCurveModel (A := A) (B := B)).Δ ≠ 0 := (sourceCurveModel (A := A) (B := B)).isUnit_Δ.ne_zero
  apply hΔ
  rw [sourceCurve_delta, hB]
  norm_num

include sourceCurve_isElliptic in
theorem source_disc_ne_zero : disc A B ≠ 0 := by
  intro hd
  have hΔ : (sourceCurveModel (A := A) (B := B)).Δ ≠ 0 := (sourceCurveModel (A := A) (B := B)).isUnit_Δ.ne_zero
  apply hΔ
  rw [sourceCurve_delta, hd]
  ring

instance targetCurve_isElliptic : (targetCurveModel (A := A) (B := B)).IsElliptic where
  isUnit := by
    rw [targetCurve_delta]
    exact isUnit_iff_ne_zero.mpr <|
      mul_ne_zero (mul_ne_zero (by norm_num)
        (source_B_ne_zero (A := A) (B := B)))
        (pow_ne_zero 2 (source_disc_ne_zero (A := A) (B := B)))

@[simp] theorem sourceCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation (sourceCurveModel (A := A) (B := B)) x y ↔
      (sourceEquationModel A B) x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold sourceEquationModel
  simp [sourceCurveModel]

@[simp] theorem targetCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation (targetCurveModel (A := A) (B := B)) x y ↔
      (targetEquationModel A B) x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold targetEquationModel
  simp [targetCurveModel]
  ring

abbrev SourcePointModel := WeierstrassCurve.Affine.Point (sourceCurveModel (A := A) (B := B))
abbrev TargetPointModel := WeierstrassCurve.Affine.Point (targetCurveModel (A := A) (B := B))


/-! ## Affine formulae -/

def forwardX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2
def forwardYModel (x y : ℚ) : ℚ := y * (B - x ^ 2) / x ^ 2

def dualX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4
def dualYModel (x y : ℚ) : ℚ := y * (disc A B - x ^ 2) / x ^ 2 / 8


theorem forward_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation (sourceCurveModel (A := A) (B := B)) x y) :
    WeierstrassCurve.Affine.Equation (targetCurveModel (A := A) (B := B))
      (forwardX x y) ((forwardYModel (B := B)) x y) := by
  rw [targetCurve_equation_iff]
  have hcurve := (sourceCurve_equation_iff (A := A) (B := B) x y).mp h
  unfold sourceEquationModel at hcurve
  unfold targetEquationModel forwardX forwardYModel disc
  field_simp [hx]
  rw [hcurve]
  ring

theorem dual_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation (targetCurveModel (A := A) (B := B)) x y) :
    WeierstrassCurve.Affine.Equation (sourceCurveModel (A := A) (B := B))
      (dualX x y) ((dualYModel (A := A) (B := B)) x y) := by
  rw [sourceCurve_equation_iff]
  have hcurve := (targetCurve_equation_iff (A := A) (B := B) x y).mp h
  unfold targetEquationModel disc at hcurve
  unfold sourceEquationModel dualX dualYModel disc
  field_simp [hx]
  rw [hcurve]
  ring

/-! ## Total point maps -/

noncomputable def forwardPointModel : (SourcePointModel (A := A) (B := B)) → (TargetPointModel (A := A) (B := B))
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (forward_equation hx (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

noncomputable def dualPointModel : (TargetPointModel (A := A) (B := B)) → (SourcePointModel (A := A) (B := B))
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (dual_equation hx (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))


@[simp] theorem forwardPoint_zero :
    (forwardPointModel (A := A) (B := B)) (0 : SourcePointModel (A := A) (B := B)) = 0 := rfl
@[simp] theorem dualPoint_zero :
    (dualPointModel (A := A) (B := B)) (0 : TargetPointModel (A := A) (B := B)) = 0 := rfl

@[simp] theorem forwardPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (sourceCurveModel (A := A) (B := B)) x y)
    (hx : x = 0) :
    (forwardPointModel (A := A) (B := B)) (.some x y h) = 0 := by
  rw [forwardPointModel]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] theorem dualPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (targetCurveModel (A := A) (B := B)) x y)
    (hx : x = 0) :
    (dualPointModel (A := A) (B := B)) (.some x y h) = 0 := by
  rw [dualPointModel]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

theorem forwardPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (sourceCurveModel (A := A) (B := B)) x y)
    (hx : x ≠ 0) :
    (forwardPointModel (A := A) (B := B)) (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [forwardPointModel, hx]

theorem dualPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (targetCurveModel (A := A) (B := B)) x y)
    (hx : x ≠ 0) :
    (dualPointModel (A := A) (B := B)) (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [dualPointModel, hx]

/-! ## Coordinate composition identities -/

@[simp] theorem sourceCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY (sourceCurveModel (A := A) (B := B)) x y = -y := by
  simp [WeierstrassCurve.Affine.negY, sourceCurveModel]

@[simp] theorem targetCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY (targetCurveModel (A := A) (B := B)) x y = -y := by
  simp [WeierstrassCurve.Affine.negY, targetCurveModel]

private def fullTangentModel (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 2 * A * x + B) / (2 * y)

private def isogenousTangentModel (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 4 * A * x + disc A B) / (2 * y)


private def tangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

private def tangentY (a₂ x y m : ℚ) : ℚ :=
  -(m * (tangentX a₂ x m - x) + y)

theorem dual_forward_x {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (sourceEquationModel A B) x y) :
    dualX (forwardX x y) ((forwardYModel (B := B)) x y) =
      tangentX A x ((fullTangentModel (A := A) (B := B)) x y) := by
  unfold dualX forwardX forwardYModel tangentX fullTangentModel
  unfold sourceEquationModel at h
  field_simp [hx, hy]
  rw [h]
  ring

theorem dual_forward_y {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (sourceEquationModel A B) x y) :
    (dualYModel (A := A) (B := B)) (forwardX x y) ((forwardYModel (B := B)) x y) =
      tangentY A x y ((fullTangentModel (A := A) (B := B)) x y) := by
  unfold dualYModel forwardX forwardYModel tangentY tangentX fullTangentModel disc
  unfold sourceEquationModel at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + A * x ^ 2 + B * x) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x ^ 3 + A * x ^ 2 + B * x) ^ 2 := by rw [h]
  rw [hy4]
  rw [h]
  ring

theorem forward_dual_x {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (targetEquationModel A B) x y) :
    forwardX (dualX x y) ((dualYModel (A := A) (B := B)) x y) =
      tangentX (-2 * A) x ((isogenousTangentModel (A := A) (B := B)) x y) := by
  unfold forwardX dualX dualYModel tangentX isogenousTangentModel
  unfold targetEquationModel at h
  field_simp [hx, hy]
  rw [h]
  ring

theorem forward_dual_y {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (targetEquationModel A B) x y) :
    (forwardYModel (B := B)) (dualX x y) ((dualYModel (A := A) (B := B)) x y) =
      tangentY (-2 * A) x y ((isogenousTangentModel (A := A) (B := B)) x y) := by
  unfold forwardYModel dualX dualYModel tangentY tangentX isogenousTangentModel disc
  unfold targetEquationModel disc at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 - 2 * A * x ^ 2 + (A ^ 2 - 4 * B) * x) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x ^ 3 - 2 * A * x ^ 2 + (A ^ 2 - 4 * B) * x) ^ 2 := by rw [h]
  rw [hy4]
  rw [h]
  ring

/-! ## Identification with the affine group law -/

theorem sourceCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope (sourceCurveModel (A := A) (B := B)) x x y y =
      (fullTangentModel (A := A) (B := B)) x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY (sourceCurveModel (A := A) (B := B)) x y := by
    intro h
    apply hy
    rw [sourceCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [sourceCurveModel, fullTangentModel, WeierstrassCurve.Affine.negY]
  ring

theorem targetCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope (targetCurveModel (A := A) (B := B)) x x y y =
      (isogenousTangentModel (A := A) (B := B)) x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY (targetCurveModel (A := A) (B := B)) x y := by
    intro h
    apply hy
    rw [targetCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [targetCurveModel, isogenousTangentModel, WeierstrassCurve.Affine.negY]
  ring

theorem sourceCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX (sourceCurveModel (A := A) (B := B)) x x ((fullTangentModel (A := A) (B := B)) x y) =
      tangentX A x ((fullTangentModel (A := A) (B := B)) x y) := by
  simp [sourceCurveModel, tangentX]
  ring

theorem targetCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX (targetCurveModel (A := A) (B := B)) x x ((isogenousTangentModel (A := A) (B := B)) x y) =
      tangentX (-2 * A) x ((isogenousTangentModel (A := A) (B := B)) x y) := by
  simp [targetCurveModel, tangentX]
  ring

theorem sourceCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY (sourceCurveModel (A := A) (B := B)) x x y ((fullTangentModel (A := A) (B := B)) x y) =
      tangentY A x y ((fullTangentModel (A := A) (B := B)) x y) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    tangentY tangentX sourceCurveModel
  ring

theorem targetCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY (targetCurveModel (A := A) (B := B)) x x y ((isogenousTangentModel (A := A) (B := B)) x y) =
      tangentY (-2 * A) x y ((isogenousTangentModel (A := A) (B := B)) x y) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    tangentY tangentX targetCurveModel
  ring

private theorem fullTwo_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (sourceCurveModel (A := A) (B := B)) x y)
    (hx : x = 0) : y = 0 := by
  have heq : (sourceEquationModel A B) x y :=
    (sourceCurve_equation_iff x y).mp h.1
  unfold sourceEquationModel at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem isogenous_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (targetCurveModel (A := A) (B := B)) x y)
    (hx : x = 0) : y = 0 := by
  have heq : (targetEquationModel A B) x y :=
    (targetCurve_equation_iff x y).mp h.1
  unfold targetEquationModel at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem fullTwo_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (sourceCurveModel (A := A) (B := B)) x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : (SourcePointModel (A := A) (B := B))) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, sourceCurveModel])

private theorem isogenous_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular (targetCurveModel (A := A) (B := B)) x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : (TargetPointModel (A := A) (B := B))) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, targetCurveModel])

private theorem fullTwo_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY (sourceCurveModel (A := A) (B := B)) x y := by
  intro h
  apply hy
  rw [sourceCurve_negY] at h
  linarith

private theorem isogenous_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY (targetCurveModel (A := A) (B := B)) x y := by
  intro h
  apply hy
  rw [targetCurve_negY] at h
  linarith

/-- The dual map after the forward map is multiplication by two, including
the point at infinity and all affine kernel points. -/
theorem dual_comp_forwardPoint (P : (SourcePointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) ((forwardPointModel (A := A) (B := B)) P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := fullTwo_y_zero_of_x_zero h hx
        rw [forwardPoint_some_of_x_eq_zero h hx]
        simp only [dualPoint_zero]
        exact (fullTwo_double_eq_zero_of_y_zero h hy).symm
      · rw [forwardPoint_some_of_x_ne_zero h hx]
        by_cases hy : y = 0
        · have hfx : forwardX x y = 0 := by simp [forwardX, hy]
          change (dualPointModel (A := A) (B := B))
              (.some (forwardX x y) ((forwardYModel (B := B)) x y) _) = _
          rw [dualPoint_some_of_x_eq_zero _ hfx]
          exact (fullTwo_double_eq_zero_of_y_zero h hy).symm
        · have hfx : forwardX x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          change (dualPointModel (A := A) (B := B))
              (.some (forwardX x y) ((forwardYModel (B := B)) x y) _) = _
          rw [dualPoint_some_of_x_ne_zero _ hfx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (fullTwo_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (dualX (forwardX x y) ((forwardYModel (B := B)) x y))
              ((dualYModel (A := A) (B := B)) (forwardX x y) ((forwardYModel (B := B)) x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX (sourceCurveModel (A := A) (B := B)) x x
                (WeierstrassCurve.Affine.slope (sourceCurveModel (A := A) (B := B)) x x y y))
              (WeierstrassCurve.Affine.addY (sourceCurveModel (A := A) (B := B)) x x y
                (WeierstrassCurve.Affine.slope (sourceCurveModel (A := A) (B := B)) x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : (sourceEquationModel A B) x y :=
            (sourceCurve_equation_iff x y).mp h.1
          constructor
          · rw [dual_forward_x hx hy heq, sourceCurve_slope_self hy,
              sourceCurve_addX_tangent]
          · rw [dual_forward_y hx hy heq, sourceCurve_slope_self hy,
              sourceCurve_addY_tangent]

/-- The forward map after the dual map is multiplication by two, including
the point at infinity and all affine kernel points. -/
theorem forward_comp_dualPoint (P : (TargetPointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) ((dualPointModel (A := A) (B := B)) P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := isogenous_y_zero_of_x_zero h hx
        rw [dualPoint_some_of_x_eq_zero h hx]
        simp only [forwardPoint_zero]
        exact (isogenous_double_eq_zero_of_y_zero h hy).symm
      · rw [dualPoint_some_of_x_ne_zero h hx]
        by_cases hy : y = 0
        · have hdx : dualX x y = 0 := by simp [dualX, hy]
          change (forwardPointModel (A := A) (B := B)) (.some (dualX x y) ((dualYModel (A := A) (B := B)) x y) _) = _
          rw [forwardPoint_some_of_x_eq_zero _ hdx]
          exact (isogenous_double_eq_zero_of_y_zero h hy).symm
        · have hdx : dualX x y ≠ 0 := by
            exact div_ne_zero
              (div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx))
              (by norm_num)
          change (forwardPointModel (A := A) (B := B)) (.some (dualX x y) ((dualYModel (A := A) (B := B)) x y) _) = _
          rw [forwardPoint_some_of_x_ne_zero _ hdx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (isogenous_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (forwardX (dualX x y) ((dualYModel (A := A) (B := B)) x y))
              ((forwardYModel (B := B)) (dualX x y) ((dualYModel (A := A) (B := B)) x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX (targetCurveModel (A := A) (B := B)) x x
                (WeierstrassCurve.Affine.slope (targetCurveModel (A := A) (B := B)) x x y y))
              (WeierstrassCurve.Affine.addY (targetCurveModel (A := A) (B := B)) x x y
                (WeierstrassCurve.Affine.slope (targetCurveModel (A := A) (B := B)) x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : (targetEquationModel A B) x y :=
            (targetCurve_equation_iff x y).mp h.1
          constructor
          · rw [forward_dual_x hx hy heq, targetCurve_slope_self hy,
              targetCurve_addX_tangent]
          · rw [forward_dual_y hx hy heq, targetCurve_slope_self hy,
              targetCurve_addY_tangent]

/-! ## Kernel and negation behavior -/

theorem forwardPoint_neg (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (-P) = -(forwardPointModel (A := A) (B := B)) P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · rw [WeierstrassCurve.Affine.Point.neg_some,
          forwardPoint_some_of_x_eq_zero _ hx,
          forwardPoint_some_of_x_eq_zero h hx]
        rfl
      · rw [WeierstrassCurve.Affine.Point.neg_some,
          forwardPoint_some_of_x_ne_zero _ hx,
          forwardPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (forwardX x (WeierstrassCurve.Affine.negY (sourceCurveModel (A := A) (B := B)) x y))
            ((forwardYModel (B := B)) x (WeierstrassCurve.Affine.negY (sourceCurveModel (A := A) (B := B)) x y)) _ =
          -WeierstrassCurve.Affine.Point.some
            (forwardX x y) ((forwardYModel (B := B)) x y) _
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [forwardX, sourceCurveModel]
        · simp [forwardYModel, sourceCurveModel, targetCurveModel]
          ring

theorem dualPoint_neg (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (-P) = -(dualPointModel (A := A) (B := B)) P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · rw [WeierstrassCurve.Affine.Point.neg_some,
          dualPoint_some_of_x_eq_zero _ hx,
          dualPoint_some_of_x_eq_zero h hx]
        rfl
      · rw [WeierstrassCurve.Affine.Point.neg_some,
          dualPoint_some_of_x_ne_zero _ hx,
          dualPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (dualX x (WeierstrassCurve.Affine.negY (targetCurveModel (A := A) (B := B)) x y))
            ((dualYModel (A := A) (B := B)) x (WeierstrassCurve.Affine.negY (targetCurveModel (A := A) (B := B)) x y)) _ =
          -WeierstrassCurve.Affine.Point.some
            (dualX x y) ((dualYModel (A := A) (B := B)) x y) _
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [dualX, targetCurveModel]
        · simp [dualYModel, targetCurveModel, sourceCurveModel]
          ring

def sourceKernel : (SourcePointModel (A := A) (B := B)) :=
  WeierstrassCurve.Affine.Point.mk
    ((sourceCurve_equation_iff 0 0).mpr (by simp [sourceEquationModel]))

def targetKernel : (TargetPointModel (A := A) (B := B)) :=
  WeierstrassCurve.Affine.Point.mk
    ((targetCurve_equation_iff 0 0).mpr (by simp [targetEquationModel]))

@[simp] theorem forwardPoint_sourceKernel :
    (forwardPointModel (A := A) (B := B)) (sourceKernel (A := A) (B := B)) = 0 := by
  apply forwardPoint_some_of_x_eq_zero
  rfl

@[simp] theorem dualPoint_targetKernel :
    (dualPointModel (A := A) (B := B)) (targetKernel (A := A) (B := B)) = 0 := by
  apply dualPoint_some_of_x_eq_zero
  rfl

theorem sourceKernel_ne_zero : (sourceKernel (A := A) (B := B)) ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem targetKernel_ne_zero : (targetKernel (A := A) (B := B)) ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

@[simp] theorem two_nsmul_sourceKernel : 2 • (sourceKernel (A := A) (B := B)) = 0 := by
  exact fullTwo_double_eq_zero_of_y_zero _ rfl

@[simp] theorem two_nsmul_targetKernel : 2 • (targetKernel (A := A) (B := B)) = 0 := by
  exact isogenous_double_eq_zero_of_y_zero _ rfl

theorem forwardPoint_eq_zero_iff (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) P = 0 ↔
      P = 0 ∨ P = sourceKernel (A := A) (B := B) := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := fullTwo_y_zero_of_x_zero h hx
        subst x
        subst y
        constructor
        · intro _
          exact Or.inr rfl
        · intro _
          exact forwardPoint_sourceKernel
      · rw [forwardPoint_some_of_x_ne_zero h hx]
        constructor
        · intro hz
          exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hz).elim
        · rintro (hz | hk)
          · exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hz).elim
          · exfalso
            apply hx
            change WeierstrassCurve.Affine.Point.some x y h =
              WeierstrassCurve.Affine.Point.some 0 0 _ at hk
            exact (WeierstrassCurve.Affine.Point.some.inj hk).1

theorem dualPoint_eq_zero_iff (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) P = 0 ↔ P = 0 ∨ P = targetKernel := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := isogenous_y_zero_of_x_zero h hx
        subst x
        subst y
        constructor
        · intro _
          exact Or.inr rfl
        · intro _
          exact dualPoint_targetKernel
      · rw [dualPoint_some_of_x_ne_zero h hx]
        constructor
        · intro hz
          exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hz).elim
        · rintro (hz | hk)
          · exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hz).elim
          · exfalso
            apply hx
            change WeierstrassCurve.Affine.Point.some x y h =
              WeierstrassCurve.Affine.Point.some 0 0 _ at hk
            exact (WeierstrassCurve.Affine.Point.some.inj hk).1

theorem dual_comp_forwardPoint_fun :
    Function.comp (dualPointModel (A := A) (B := B)) (forwardPointModel (A := A) (B := B)) = fun P : (SourcePointModel (A := A) (B := B)) => 2 • P := by
  funext P
  exact dual_comp_forwardPoint P

theorem forward_comp_dualPoint_fun :
    Function.comp (forwardPointModel (A := A) (B := B)) (dualPointModel (A := A) (B := B)) = fun P : (TargetPointModel (A := A) (B := B)) => 2 • P := by
  funext P
  exact forward_comp_dualPoint P

/-! ## Formal group-law branches already forced by the composition identities -/

@[simp] theorem forwardPoint_add_zero (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + 0) = (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) 0 := by
  simp

@[simp] theorem forwardPoint_zero_add (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (0 + P) = (forwardPointModel (A := A) (B := B)) 0 + (forwardPointModel (A := A) (B := B)) P := by
  simp

@[simp] theorem dualPoint_add_zero (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + 0) = (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) 0 := by
  simp

@[simp] theorem dualPoint_zero_add (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (0 + P) = (dualPointModel (A := A) (B := B)) 0 + (dualPointModel (A := A) (B := B)) P := by
  simp

theorem forwardPoint_add_neg (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + -P) = (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) (-P) := by
  rw [add_neg_cancel, forwardPoint_zero, forwardPoint_neg, add_neg_cancel]

theorem dualPoint_add_neg (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + -P) = (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) (-P) := by
  rw [add_neg_cancel, dualPoint_zero, dualPoint_neg, add_neg_cancel]

theorem forwardPoint_add_self (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + P) = (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) P := by
  rw [← two_nsmul]
  calc
    (forwardPointModel (A := A) (B := B)) (2 • P) =
        (forwardPointModel (A := A) (B := B)) ((dualPointModel (A := A) (B := B)) ((forwardPointModel (A := A) (B := B)) P)) := by
      rw [dual_comp_forwardPoint]
    _ = 2 • (forwardPointModel (A := A) (B := B)) P := forward_comp_dualPoint _

theorem dualPoint_add_self (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + P) = (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) P := by
  rw [← two_nsmul]
  calc
    (dualPointModel (A := A) (B := B)) (2 • P) =
        (dualPointModel (A := A) (B := B)) ((forwardPointModel (A := A) (B := B)) ((dualPointModel (A := A) (B := B)) P)) := by
      rw [forward_comp_dualPoint]
    _ = 2 • (dualPointModel (A := A) (B := B)) P := dual_comp_forwardPoint _

/-! ## Translation by the kernel point -/

private theorem fullEquation_of_nonsingular {x y : ℚ}
    (h : Nonsingular (sourceCurveModel (A := A) (B := B)) x y) : (sourceEquationModel A B) x y :=
  (sourceCurve_equation_iff x y).mp h.1

private theorem isogenousEquation_of_nonsingular {x y : ℚ}
    (h : Nonsingular (targetCurveModel (A := A) (B := B)) x y) : (targetEquationModel A B) x y :=
  (targetCurve_equation_iff x y).mp h.1

private theorem full_y_zero_of_x_zero {x y : ℚ}
    (h : Nonsingular (sourceCurveModel (A := A) (B := B)) x y) (hx : x = 0) : y = 0 := by
  have heq := fullEquation_of_nonsingular h
  unfold sourceEquationModel at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem isogenous_y_zero_of_x_zero_hom {x y : ℚ}
    (h : Nonsingular (targetCurveModel (A := A) (B := B)) x y) (hx : x = 0) : y = 0 := by
  have heq := isogenousEquation_of_nonsingular h
  unfold targetEquationModel at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem full_slope_kernel {x y : ℚ} (hx : x ≠ 0) :
    slope (sourceCurveModel (A := A) (B := B)) x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

private theorem isogenous_slope_kernel {x y : ℚ} (hx : x ≠ 0) :
    slope (targetCurveModel (A := A) (B := B)) x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

private theorem full_add_kernel_x {x y : ℚ}
    (h : Nonsingular (sourceCurveModel (A := A) (B := B)) x y) (hx : x ≠ 0) :
    addX (sourceCurveModel (A := A) (B := B)) x 0 (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0) = B / x := by
  rw [full_slope_kernel hx]
  have heq := fullEquation_of_nonsingular h
  unfold sourceEquationModel at heq
  unfold addX sourceCurveModel
  field_simp [hx]
  linear_combination heq

private theorem full_add_kernel_y {x y : ℚ}
    (h : Nonsingular (sourceCurveModel (A := A) (B := B)) x y) (hx : x ≠ 0) :
    addY (sourceCurveModel (A := A) (B := B)) x 0 y (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0) =
      -(B * y / x ^ 2) := by
  rw [full_slope_kernel hx]
  unfold addY negAddY negY
  have hX : addX (sourceCurveModel (A := A) (B := B)) x 0 (y / x) = B / x := by
    rw [← full_slope_kernel (A := A) (B := B) hx]
    exact full_add_kernel_x (A := A) (B := B) h hx
  rw [hX]
  simp [sourceCurveModel]
  field_simp [hx]
  ring

private theorem isogenous_add_kernel_x {x y : ℚ}
    (h : Nonsingular (targetCurveModel (A := A) (B := B)) x y) (hx : x ≠ 0) :
    addX (targetCurveModel (A := A) (B := B)) x 0 (slope (targetCurveModel (A := A) (B := B)) x 0 y 0) = disc A B / x := by
  rw [isogenous_slope_kernel hx]
  have heq := isogenousEquation_of_nonsingular h
  unfold targetEquationModel at heq
  unfold addX targetCurveModel
  field_simp [hx]
  linear_combination heq

private theorem isogenous_add_kernel_y {x y : ℚ}
    (h : Nonsingular (targetCurveModel (A := A) (B := B)) x y) (hx : x ≠ 0) :
    addY (targetCurveModel (A := A) (B := B)) x 0 y (slope (targetCurveModel (A := A) (B := B)) x 0 y 0) =
      -(disc A B * y / x ^ 2) := by
  rw [isogenous_slope_kernel hx]
  unfold addY negAddY negY
  have hX : addX (targetCurveModel (A := A) (B := B)) x 0 (y / x) = disc A B / x := by
    rw [← isogenous_slope_kernel (A := A) (B := B) hx]
    exact isogenous_add_kernel_x (A := A) (B := B) h hx
  rw [hX]
  simp [targetCurveModel]
  field_simp [hx]
  ring

private theorem forward_translation_coordinates {x y : ℚ} (hB : B ≠ 0) (hx : x ≠ 0) :
    forwardX (B / x) (-(B * y / x ^ 2)) = forwardX x y ∧
      (forwardYModel (B := B)) (B / x) (-(B * y / x ^ 2)) = (forwardYModel (B := B)) x y := by
  constructor
  · unfold forwardX
    field_simp [hx, hB]
  · unfold forwardYModel
    field_simp [hx, hB]
    ring

private theorem dual_translation_coordinates {x y : ℚ}
    (hD : disc A B ≠ 0) (hx : x ≠ 0) :
    dualX (disc A B / x) (-(disc A B * y / x ^ 2)) = dualX x y ∧
      (dualYModel (A := A) (B := B)) (disc A B / x) (-(disc A B * y / x ^ 2)) = (dualYModel (A := A) (B := B)) x y := by
  constructor
  · unfold dualX
    field_simp [hx, hD]
  · unfold dualYModel
    field_simp [hx, hD]
    ring

/-- The forward quotient map is invariant under translation by its kernel. -/
theorem forwardPoint_add_sourceKernel (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + sourceKernel) = (forwardPointModel (A := A) (B := B)) P := by
  cases P with
  | zero =>
      change (forwardPointModel (A := A) (B := B)) sourceKernel = (forwardPointModel (A := A) (B := B)) 0
      rw [forwardPoint_sourceKernel, forwardPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := full_y_zero_of_x_zero h hx
        subst x
        subst y
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : (SourcePointModel (A := A) (B := B))) =
            sourceKernel by rfl]
        rw [← two_nsmul, two_nsmul_sourceKernel]
        rw [forwardPoint_zero, forwardPoint_sourceKernel]
      · change (forwardPointModel (A := A) (B := B))
            ((WeierstrassCurve.Affine.Point.some x y h : (SourcePointModel (A := A) (B := B))) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        have hax : addX (sourceCurveModel (A := A) (B := B)) x 0
            (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0) ≠ 0 := by
          rw [full_add_kernel_x h hx]
          exact div_ne_zero (source_B_ne_zero (A := A) (B := B)) hx
        rw [forwardPoint_some_of_x_ne_zero _ hax,
          forwardPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (forwardX
              (addX (sourceCurveModel (A := A) (B := B)) x 0 (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0))
              (addY (sourceCurveModel (A := A) (B := B)) x 0 y (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0)))
            ((forwardYModel (B := B))
              (addX (sourceCurveModel (A := A) (B := B)) x 0 (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0))
              (addY (sourceCurveModel (A := A) (B := B)) x 0 y (slope (sourceCurveModel (A := A) (B := B)) x 0 y 0))) _ =
          WeierstrassCurve.Affine.Point.some
            (forwardX x y) ((forwardYModel (B := B)) x y) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := forward_translation_coordinates
          (source_B_ne_zero (A := A) (B := B)) (x := x) (y := y) hx
        constructor
        · rw [full_add_kernel_x h hx, full_add_kernel_y h hx]
          exact hc.1
        · rw [full_add_kernel_x h hx, full_add_kernel_y h hx]
          exact hc.2

/-- The dual quotient map is invariant under translation by its kernel. -/
theorem dualPoint_add_targetKernel (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + targetKernel) = (dualPointModel (A := A) (B := B)) P := by
  cases P with
  | zero =>
      change (dualPointModel (A := A) (B := B)) targetKernel = (dualPointModel (A := A) (B := B)) 0
      rw [dualPoint_targetKernel, dualPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := isogenous_y_zero_of_x_zero h hx
        subst x
        subst y
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : (TargetPointModel (A := A) (B := B))) =
            targetKernel by rfl]
        rw [← two_nsmul, two_nsmul_targetKernel]
        rw [dualPoint_zero, dualPoint_targetKernel]
      · change (dualPointModel (A := A) (B := B))
            ((WeierstrassCurve.Affine.Point.some x y h : (TargetPointModel (A := A) (B := B))) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        have hax : addX (targetCurveModel (A := A) (B := B)) x 0
            (slope (targetCurveModel (A := A) (B := B)) x 0 y 0) ≠ 0 := by
          rw [isogenous_add_kernel_x h hx]
          exact div_ne_zero (source_disc_ne_zero (A := A) (B := B)) hx
        rw [dualPoint_some_of_x_ne_zero _ hax,
          dualPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (dualX
              (addX (targetCurveModel (A := A) (B := B)) x 0 (slope (targetCurveModel (A := A) (B := B)) x 0 y 0))
              (addY (targetCurveModel (A := A) (B := B)) x 0 y (slope (targetCurveModel (A := A) (B := B)) x 0 y 0)))
            ((dualYModel (A := A) (B := B))
              (addX (targetCurveModel (A := A) (B := B)) x 0 (slope (targetCurveModel (A := A) (B := B)) x 0 y 0))
              (addY (targetCurveModel (A := A) (B := B)) x 0 y (slope (targetCurveModel (A := A) (B := B)) x 0 y 0))) _ =
          WeierstrassCurve.Affine.Point.some
            (dualX x y) ((dualYModel (A := A) (B := B)) x y) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := dual_translation_coordinates
          (source_disc_ne_zero (A := A) (B := B)) (x := x) (y := y) hx
        constructor
        · rw [isogenous_add_kernel_x h hx, isogenous_add_kernel_y h hx]
          exact hc.1
        · rw [isogenous_add_kernel_x h hx, isogenous_add_kernel_y h hx]
          exact hc.2

theorem forwardPoint_sourceKernel_add (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (sourceKernel + P) = (forwardPointModel (A := A) (B := B)) P := by
  rw [add_comm, forwardPoint_add_sourceKernel]

theorem dualPoint_targetKernel_add (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (targetKernel + P) = (dualPointModel (A := A) (B := B)) P := by
  rw [add_comm, dualPoint_add_targetKernel]

/-- Additivity for a pair differing by the forward kernel point. -/
theorem forwardPoint_add_kernelTranslate (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + (P + sourceKernel)) =
      (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) (P + sourceKernel) := by
  rw [← add_assoc, forwardPoint_add_sourceKernel,
    forwardPoint_add_sourceKernel, forwardPoint_add_self]

/-- Additivity for a pair whose sum is the forward kernel point. -/
theorem forwardPoint_add_neg_kernelTranslate (P : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + (-P + sourceKernel)) =
      (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) (-P + sourceKernel) := by
  rw [← add_assoc, add_neg_cancel, zero_add, forwardPoint_sourceKernel,
    forwardPoint_add_sourceKernel, forwardPoint_neg, add_neg_cancel]

/-- Additivity for a pair differing by the dual kernel point. -/
theorem dualPoint_add_kernelTranslate (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + (P + targetKernel)) =
      (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) (P + targetKernel) := by
  rw [← add_assoc, dualPoint_add_targetKernel,
    dualPoint_add_targetKernel, dualPoint_add_self]

/-- Additivity for a pair whose sum is the dual kernel point. -/
theorem dualPoint_add_neg_kernelTranslate (P : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) (P + (-P + targetKernel)) =
      (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) (-P + targetKernel) := by
  rw [← add_assoc, add_neg_cancel, zero_add, dualPoint_targetKernel,
    dualPoint_add_targetKernel, dualPoint_neg, add_neg_cancel]

/-- A single eliminator for all forward-map group-law branches that do not
require the generic secant calculation. -/
theorem forwardPoint_add_of_basic_or_kernel_relation
    (P Q : (SourcePointModel (A := A) (B := B)))
    (hQ : Q = 0 ∨ Q = sourceKernel ∨ Q = P ∨ Q = -P ∨
      Q = P + sourceKernel ∨ Q = -P + sourceKernel) :
    (forwardPointModel (A := A) (B := B)) (P + Q) = (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact forwardPoint_add_zero P
  · rw [hQ, forwardPoint_add_sourceKernel, forwardPoint_sourceKernel, add_zero]
  · rw [hQ]
    exact forwardPoint_add_self P
  · rw [hQ]
    exact forwardPoint_add_neg P
  · rw [hQ]
    exact forwardPoint_add_kernelTranslate P
  · rw [hQ]
    exact forwardPoint_add_neg_kernelTranslate P

/-- A single eliminator for all dual-map group-law branches that do not
require the generic secant calculation. -/
theorem dualPoint_add_of_basic_or_kernel_relation
    (P Q : (TargetPointModel (A := A) (B := B)))
    (hQ : Q = 0 ∨ Q = targetKernel ∨ Q = P ∨ Q = -P ∨
      Q = P + targetKernel ∨ Q = -P + targetKernel) :
    (dualPointModel (A := A) (B := B)) (P + Q) = (dualPointModel (A := A) (B := B)) P + (dualPointModel (A := A) (B := B)) Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact dualPoint_add_zero P
  · rw [hQ, dualPoint_add_targetKernel, dualPoint_targetKernel, add_zero]
  · rw [hQ]
    exact dualPoint_add_self P
  · rw [hQ]
    exact dualPoint_add_neg P
  · rw [hQ]
    exact dualPoint_add_kernelTranslate P
  · rw [hQ]
    exact dualPoint_add_neg_kernelTranslate P

/-! ## Affine fibre separation -/

private theorem forward_x_fibre_factor
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (sourceEquationModel A B) x₁ y₁) (h₂ : (sourceEquationModel A B) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : forwardX x₁ y₁ = forwardX x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = B := by
  unfold forwardX at hX
  unfold sourceEquationModel at h₁ h₂
  field_simp [hx₁, hx₂] at hX
  rw [h₁, h₂] at hX
  have hmul : x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - B)) = 0 := by
    linear_combination hX
  have hfac : (x₁ - x₂) * (x₁ * x₂ - B) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hx₁ hx₂)
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem dual_x_fibre_factor
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (targetEquationModel A B) x₁ y₁)
    (h₂ : (targetEquationModel A B) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : dualX x₁ y₁ = dualX x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = disc A B := by
  unfold dualX at hX
  unfold targetEquationModel at h₁ h₂
  field_simp [hx₁, hx₂] at hX
  rw [h₁, h₂] at hX
  have hmul : x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - disc A B)) = 0 := by
    linear_combination hX
  have hfac : (x₁ - x₂) * (x₁ * x₂ - disc A B) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hx₁ hx₂)
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem forward_affine_fibre
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Nonsingular (sourceCurveModel (A := A) (B := B)) x₁ y₁)
    (h₂ : Nonsingular (sourceCurveModel (A := A) (B := B)) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : (forwardPointModel (A := A) (B := B))
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
      (forwardPointModel (A := A) (B := B))
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (SourcePointModel (A := A) (B := B))) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (SourcePointModel (A := A) (B := B))) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + sourceKernel := by
  rw [forwardPoint_some_of_x_ne_zero h₁ hx₁,
    forwardPoint_some_of_x_ne_zero h₂ hx₂] at hmap
  change WeierstrassCurve.Affine.Point.some
      (forwardX x₁ y₁) ((forwardYModel (B := B)) x₁ y₁) _ =
    WeierstrassCurve.Affine.Point.some
      (forwardX x₂ y₂) ((forwardYModel (B := B)) x₂ y₂) _ at hmap
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hmap
  have heq₁ := fullEquation_of_nonsingular h₁
  have heq₂ := fullEquation_of_nonsingular h₂
  have hxf := forward_x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (SourcePointModel (A := A) (B := B))) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (SourcePointModel (A := A) (B := B))) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + sourceKernel := by
    by_cases hyeq : y₁ = y₂
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hyroots := Y_eq_of_X_eq h₁.1 h₂.1 hxeq
      have hyneg : y₂ = -y₁ := by
        rcases hyroots with hy | hy
        · exact (hyeq hy).elim
        · rw [sourceCurve_negY] at hy
          linarith
      have hy₁ : y₁ ≠ 0 := by
        intro hyzero
        apply hyeq
        rw [hyzero] at hyneg ⊢
        simpa using hyneg.symm
      have hY := hcoords.2
      unfold forwardYModel at hY
      rw [← hxeq] at hY
      field_simp [hx₁] at hY
      rw [hyneg] at hY
      have hprod : y₁ * (B - x₁ ^ 2) = 0 := by
        linear_combination (1 / 2 : ℚ) * hY
      have hsquare : x₁ ^ 2 = B := by
        have := (mul_eq_zero.mp hprod).resolve_left hy₁
        linarith
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (SourcePointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [full_add_kernel_x h₁ hx₁, ← hxeq]
        field_simp [hx₁]
        nlinarith
      · rw [full_add_kernel_y h₁ hx₁, hyneg]
        field_simp [hx₁]
        nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = B / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ B := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      unfold forwardYModel at hY
      rw [hx₂val] at hY
      field_simp [hx₁] at hY
      rw [eq_div_iff (source_B_ne_zero (A := A) (B := B))] at hY
      have hfac : (x₁ ^ 2 - B) * (x₁ ^ 2 * y₂ + B * y₁) = 0 := by
        calc
          (x₁ ^ 2 - B) * (x₁ ^ 2 * y₂ + B * y₁) =
              -(y₁ * B * (B - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - B)) := by ring
          _ = 0 := by linear_combination -hY
      have hyrel : x₁ ^ 2 * y₂ + B * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (SourcePointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [full_add_kernel_x h₁ hx₁, hx₂val]
      · rw [full_add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

/-- The fibres of the forward rational-point map are exactly the cosets of
its two-element kernel. -/
theorem forwardPoint_eq_iff (P Q : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) P = (forwardPointModel (A := A) (B := B)) Q ↔
      Q = P ∨ Q = P + sourceKernel := by
  constructor
  · intro hPQ
    by_cases hPzero : (forwardPointModel (A := A) (B := B)) P = 0
    · have hQzero : (forwardPointModel (A := A) (B := B)) Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (forwardPoint_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (forwardPoint_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left; rw [hP, hQ]
      · right; rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, ← two_nsmul, two_nsmul_sourceKernel]
      · left; rw [hP, hQ]
    · have hQzero : (forwardPointModel (A := A) (B := B)) Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero forwardPoint_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero forwardPoint_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                exact forwardPoint_some_of_x_eq_zero h₁ hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                exact forwardPoint_some_of_x_eq_zero h₂ hx
              exact forward_affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (forwardPoint_add_sourceKernel P).symm

private theorem dual_affine_fibre
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Nonsingular (targetCurveModel (A := A) (B := B)) x₁ y₁)
    (h₂ : Nonsingular (targetCurveModel (A := A) (B := B)) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : (dualPointModel (A := A) (B := B))
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
      (dualPointModel (A := A) (B := B))
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (TargetPointModel (A := A) (B := B))) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (TargetPointModel (A := A) (B := B))) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          targetKernel := by
  rw [dualPoint_some_of_x_ne_zero h₁ hx₁,
    dualPoint_some_of_x_ne_zero h₂ hx₂] at hmap
  change WeierstrassCurve.Affine.Point.some
      (dualX x₁ y₁) ((dualYModel (A := A) (B := B)) x₁ y₁) _ =
    WeierstrassCurve.Affine.Point.some
      (dualX x₂ y₂) ((dualYModel (A := A) (B := B)) x₂ y₂) _ at hmap
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hmap
  have heq₁ := isogenousEquation_of_nonsingular h₁
  have heq₂ := isogenousEquation_of_nonsingular h₂
  have hxf := dual_x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (TargetPointModel (A := A) (B := B))) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (TargetPointModel (A := A) (B := B))) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
            targetKernel := by
    by_cases hyeq : y₁ = y₂
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hyroots := Y_eq_of_X_eq h₁.1 h₂.1 hxeq
      have hyneg : y₂ = -y₁ := by
        rcases hyroots with hy | hy
        · exact (hyeq hy).elim
        · rw [targetCurve_negY] at hy
          linarith
      have hy₁ : y₁ ≠ 0 := by
        intro hyzero
        apply hyeq
        rw [hyzero] at hyneg ⊢
        simpa using hyneg.symm
      have hY := hcoords.2
      unfold dualYModel at hY
      rw [← hxeq] at hY
      field_simp [hx₁] at hY
      rw [hyneg] at hY
      have hprod : y₁ * (disc A B - x₁ ^ 2) = 0 := by
        linear_combination (1 / 2 : ℚ) * hY
      have hsquare : x₁ ^ 2 = disc A B := by
        have := (mul_eq_zero.mp hprod).resolve_left hy₁
        linarith
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
            (TargetPointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [isogenous_add_kernel_x h₁ hx₁, ← hxeq]
        field_simp [hx₁]
        nlinarith
      · rw [isogenous_add_kernel_y h₁ hx₁, hyneg]
        field_simp [hx₁]
        nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = disc A B / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ disc A B := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      unfold dualYModel at hY
      rw [hx₂val] at hY
      field_simp [hx₁] at hY
      rw [eq_div_iff (source_disc_ne_zero (A := A) (B := B))] at hY
      have hfac :
          (x₁ ^ 2 - disc A B) * (x₁ ^ 2 * y₂ + disc A B * y₁) = 0 := by
        calc
          (x₁ ^ 2 - disc A B) * (x₁ ^ 2 * y₂ + disc A B * y₁) =
              -(y₁ * disc A B * (disc A B - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - disc A B)) := by ring
          _ = 0 := by linear_combination -hY
      have hyrel : x₁ ^ 2 * y₂ + disc A B * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
            (TargetPointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [isogenous_add_kernel_x h₁ hx₁, hx₂val]
      · rw [isogenous_add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

/-- The fibres of the dual rational-point map are exactly the cosets of its
two-element kernel. -/
theorem dualPoint_eq_iff (P Q : (TargetPointModel (A := A) (B := B))) :
    (dualPointModel (A := A) (B := B)) P = (dualPointModel (A := A) (B := B)) Q ↔
      Q = P ∨ Q = P + targetKernel := by
  constructor
  · intro hPQ
    by_cases hPzero : (dualPointModel (A := A) (B := B)) P = 0
    · have hQzero : (dualPointModel (A := A) (B := B)) Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (dualPoint_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (dualPoint_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left; rw [hP, hQ]
      · right; rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, ← two_nsmul, two_nsmul_targetKernel]
      · left; rw [hP, hQ]
    · have hQzero : (dualPointModel (A := A) (B := B)) Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero dualPoint_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero dualPoint_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                exact dualPoint_some_of_x_eq_zero h₁ hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                exact dualPoint_some_of_x_eq_zero h₂ hx
              exact dual_affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (dualPoint_add_targetKernel P).symm

/-! ## The generic forward secant: x-coordinate -/

private theorem forwardX_secant_form {x y : ℚ}
    (h : (sourceEquationModel A B) x y) (hx : x ≠ 0) :
    forwardX x y = x + A + B / x := by
  unfold forwardX
  rw [h]
  field_simp [hx]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The cleared-denominator certificate requires unbounded polynomial normalization.
private theorem forward_secant_x_identity
    {x1 y1 x2 y2 : ℚ}
    (h1 : y1 ^ 2 = x1 ^ 3 + A * x1 ^ 2 + B * x1)
    (h2 : y2 ^ 2 = x2 ^ 3 + A * x2 ^ 2 + B * x2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : ((y1 - y2) / (x1 - x2)) ^ 2 - A - x1 - x2 ≠ 0)
    (hF : x1 + A + B / x1 ≠ x2 + A + B / x2) :
    let ell := (y1 - y2) / (x1 - x2)
    let rx := ell ^ 2 - A - x1 - x2
    let m :=
      (y1 * (B - x1 ^ 2) / x1 ^ 2 -
        y2 * (B - x2 ^ 2) / x2 ^ 2) /
      ((x1 + A + B / x1) - (x2 + A + B / x2))
    rx + A + B / rx =
      m ^ 2 + 2 * A - (x1 + A + B / x1) - (x2 + A + B / x2) := by
  dsimp
  have h16 : x1 * x2 - B ≠ 0 := by
    intro hzero
    apply hF
    apply sub_eq_zero.mp
    calc
      (x1 + A + B / x1) - (x2 + A + B / x2) =
          (x1 - x2) * (x1 * x2 - B) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hAeq :
      (y1 - y2) ^ 2 - (x1 - x2) ^ 2 * A - x1 * (x1 - x2) ^ 2 -
          x2 * (x1 - x2) ^ 2 =
        (x1 - x2) ^ 2 *
          (((y1 - y2) / (x1 - x2)) ^ 2 - A - x1 - x2) := by
    field_simp [sub_ne_zero.mpr hx12]
  have hA :
      (y1 - y2) ^ 2 - (x1 - x2) ^ 2 * A - x1 * (x1 - x2) ^ 2 -
          x2 * (x1 - x2) ^ 2 ≠ 0 := by
    rw [hAeq]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx12)) hr
  have hBeq :
      x2 * (x1 * (x1 + A) + B) - x1 * (x2 * (x2 + A) + B) =
        (x1 - x2) * (x1 * x2 - B) := by ring
  have hB :
      x2 * (x1 * (x1 + A) + B) - x1 * (x2 * (x2 + A) + B) ≠ 0 := by
    rw [hBeq]
    exact mul_ne_zero (sub_ne_zero.mpr hx12) h16
  field_simp [hx1, hx2, sub_ne_zero.mpr hx12, hr,
    sub_ne_zero.mpr hF, h16]
  field_simp [hA, hB]
  linear_combination
    (B * (x1 - x2) ^ 3 *
      (2 * A * B * x1 ^ 2 * x2 ^ 3 + A * B * x1 * x2 ^ 4 -
        A * B * x2 ^ 5 - 4 * A * x1 ^ 3 * x2 ^ 4 + 2 * A * x1 ^ 2 * x2 ^ 5 +
        B ^ 2 * x1 ^ 3 * x2 + B ^ 2 * x1 ^ 2 * x2 ^ 2 -
        2 * B * x1 ^ 4 * x2 ^ 2 - B * x1 ^ 3 * x2 ^ 3 - B * x1 ^ 3 * y2 ^ 2 +
        4 * B * x1 ^ 2 * x2 ^ 4 - B * x1 ^ 2 * x2 * y2 ^ 2 +
        B * x1 * x2 ^ 2 * y1 ^ 2 - 2 * B * x1 * x2 ^ 2 * y1 * y2 +
        B * x1 * x2 ^ 2 * y2 ^ 2 - B * x2 ^ 6 + B * x2 ^ 3 * y1 ^ 2 -
        2 * B * x2 ^ 3 * y1 * y2 + B * x2 ^ 3 * y2 ^ 2 + x1 ^ 5 * x2 ^ 3 -
        2 * x1 ^ 4 * x2 ^ 4 - 3 * x1 ^ 3 * x2 ^ 5 -
        2 * x1 ^ 3 * x2 ^ 2 * y1 * y2 + 6 * x1 ^ 3 * x2 ^ 2 * y2 ^ 2 +
        2 * x1 ^ 2 * x2 ^ 6 - 2 * x1 ^ 2 * x2 ^ 3 * y1 ^ 2 +
        6 * x1 ^ 2 * x2 ^ 3 * y1 * y2 - 6 * x1 ^ 2 * x2 ^ 3 * y2 ^ 2)) * h1 +
    (B * x1 ^ 2 * (x1 - x2) ^ 3 *
      (-2 * A * B * x1 ^ 2 * x2 - A * B * x1 * x2 ^ 2 + A * B * x2 ^ 3 +
        4 * A * x1 ^ 3 * x2 ^ 2 - 2 * A * x1 ^ 2 * x2 ^ 3 - B ^ 2 * x1 ^ 2 -
        B ^ 2 * x1 * x2 - B * x1 ^ 3 * x2 + 3 * B * x1 ^ 2 * x2 ^ 2 -
        4 * B * x1 * x2 ^ 3 + 2 * B * x1 * y1 * y2 - B * x1 * y2 ^ 2 +
        2 * B * x2 ^ 4 + 2 * B * x2 * y1 * y2 - B * x2 * y2 ^ 2 +
        4 * x1 ^ 4 * x2 ^ 2 - 3 * x1 ^ 3 * x2 ^ 3 + 2 * x1 ^ 2 * x2 ^ 4 -
        x1 * x2 ^ 5 - 6 * x1 * x2 ^ 2 * y1 * y2 +
        2 * x1 * x2 ^ 2 * y2 ^ 2 + 2 * x2 ^ 3 * y1 * y2)) * h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The secant coefficient identities require unbounded polynomial normalization.
private theorem forward_secant_y_identity
    {x1 y1 x2 y2 ell r : ℚ}
    (h1 : y1 ^ 2 = x1 ^ 3 + A * x1 ^ 2 + B * x1)
    (h2 : y2 ^ 2 = x2 ^ 3 + A * x2 ^ 2 + B * x2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hell : ell = (y1 - y2) / (x1 - x2))
    (hrdef : r = ell ^ 2 - A - x1 - x2)
    (hr : r ≠ 0) (h16 : x1 * x2 - B ≠ 0) :
    let s := ell * (x1 - r) - y1
    let m :=
      (y1 * (B - x1 ^ 2) / x1 ^ 2 -
        y2 * (B - x2 ^ 2) / x2 ^ 2) /
      ((x1 + A + B / x1) - (x2 + A + B / x2))
    s * (B - r ^ 2) / r ^ 2 =
      m * ((x1 + A + B / x1) - (r + A + B / r)) -
        y1 * (B - x1 ^ 2) / x1 ^ 2 := by
  have hline : y2 = y1 - ell * (x1 - x2) := by
    rw [hell]
    field_simp [sub_ne_zero.mpr hx12]
    ring
  have h2' := h2
  rw [hline] at h2'
  have hBmul :
      (x1 - x2) *
        (x1 * x2 + x1 * r + x2 * r -
          (B - 2 * ell * y1 + 2 * ell ^ 2 * x1)) = 0 := by
    rw [hrdef]
    linear_combination h1 - h2'
  have hB :
      x1 * x2 + x1 * r + x2 * r -
          (B - 2 * ell * y1 + 2 * ell ^ 2 * x1) = 0 :=
    (mul_eq_zero.mp hBmul).resolve_left (sub_ne_zero.mpr hx12)
  have hC : x1 * x2 * r - (y1 - ell * x1) ^ 2 = 0 := by
    linear_combination x1 * hB - h1 - x1 ^ 2 * hrdef
  have hH :
      ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
          B * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
          B * y1 = 0 := by
    linear_combination (ell * x1 - y1) * hB - 2 * ell * hC
  have hFD_eq :
      (x1 + A + B / x1) - (x2 + A + B / x2) =
        (x1 - x2) * (x1 * x2 - B) / (x1 * x2) := by
    field_simp [hx1, hx2]
    ring
  have hm :
      (y1 * (B - x1 ^ 2) / x1 ^ 2 -
          y2 * (B - x2 ^ 2) / x2 ^ 2) /
        ((x1 + A + B / x1) - (x2 + A + B / x2)) =
      (-B * y1 * (x1 + x2) + ell * x1 ^ 2 * (B - x2 ^ 2)) /
        (x1 * x2 * (x1 * x2 - B)) := by
    rw [hline, hFD_eq]
    field_simp [hx1, hx2, sub_ne_zero.mpr hx12, h16]
    ring
  dsimp
  rw [hm]
  apply sub_eq_zero.mp
  calc
    (ell * (x1 - r) - y1) * (B - r ^ 2) / r ^ 2 -
          ((-B * y1 * (x1 + x2) + ell * x1 ^ 2 * (B - x2 ^ 2)) /
              (x1 * x2 * (x1 * x2 - B)) *
            ((x1 + A + B / x1) - (r + A + B / r)) -
          y1 * (B - x1 ^ 2) / x1 ^ 2) =
        B * (x1 - r) * (x2 - r) *
            (ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
              B * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
              B * y1) /
          (r ^ 2 * x1 * x2 * (x1 * x2 - B)) := by
      field_simp [hx1, hx2, hr, h16]
      ring
    _ = 0 := by rw [hH]; ring

/-- In the generic affine secant branch, the forward two-isogeny preserves
the x-coordinate of addition. -/
theorem forward_add_x_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular (sourceCurveModel (A := A) (B := B)) x1 y1)
    (h2 : Nonsingular (sourceCurveModel (A := A) (B := B)) x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX (sourceCurveModel (A := A) (B := B)) x1 x2
        (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    forwardX
        (addX (sourceCurveModel (A := A) (B := B)) x1 x2 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2))
        (addY (sourceCurveModel (A := A) (B := B)) x1 x2 y1 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2)) =
      addX (targetCurveModel (A := A) (B := B)) (forwardX x1 y1) (forwardX x2 y2)
        (slope (targetCurveModel (A := A) (B := B)) (forwardX x1 y1) (forwardX x2 y2)
          ((forwardYModel (B := B)) x1 y1) ((forwardYModel (B := B)) x2 y2)) := by
  have heq1 := fullEquation_of_nonsingular h1
  have heq2 := fullEquation_of_nonsingular h2
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := fullEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 - A - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, sourceCurveModel] using hr
  have hF' : x1 + A + B / x1 ≠ x2 + A + B / x2 := by
    simpa [forwardX_secant_form heq1 hx1,
      forwardX_secant_form heq2 hx2] using hF
  have hid := forward_secant_x_identity heq1 heq2 hx1 hx2 hx12 hr' hF'
  rw [forwardX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, slope_of_X_ne hF]
  rw [forwardX_secant_form heq1 hx1, forwardX_secant_form heq2 hx2]
  simpa [addX, sourceCurveModel, targetCurveModel, forwardYModel] using hid

/-- In the generic affine secant branch, the forward two-isogeny preserves
the y-coordinate of addition. -/
theorem forward_add_y_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular (sourceCurveModel (A := A) (B := B)) x1 y1)
    (h2 : Nonsingular (sourceCurveModel (A := A) (B := B)) x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX (sourceCurveModel (A := A) (B := B)) x1 x2
        (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    (forwardYModel (B := B))
        (addX (sourceCurveModel (A := A) (B := B)) x1 x2 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2))
        (addY (sourceCurveModel (A := A) (B := B)) x1 x2 y1 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2)) =
      addY (targetCurveModel (A := A) (B := B)) (forwardX x1 y1) (forwardX x2 y2) ((forwardYModel (B := B)) x1 y1)
        (slope (targetCurveModel (A := A) (B := B)) (forwardX x1 y1) (forwardX x2 y2)
          ((forwardYModel (B := B)) x1 y1) ((forwardYModel (B := B)) x2 y2)) := by
  have heq1 := fullEquation_of_nonsingular h1
  have heq2 := fullEquation_of_nonsingular h2
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := fullEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 - A - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, sourceCurveModel] using hr
  have hF' : x1 + A + B / x1 ≠ x2 + A + B / x2 := by
    simpa [forwardX_secant_form heq1 hx1,
      forwardX_secant_form heq2 hx2] using hF
  have h16 : x1 * x2 - B ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x1 + A + B / x1) - (x2 + A + B / x2) =
          (x1 - x2) * (x1 * x2 - B) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := forward_secant_y_identity heq1 heq2 hx1 hx2 hx12
    (ell := (y1 - y2) / (x1 - x2))
    (r := ((y1 - y2) / (x1 - x2)) ^ 2 - A - x1 - x2)
    rfl rfl hr' h16
  have hX := forward_add_x_generic h1 h2 hx1 hx2 hx12 hr hF
  unfold addY negAddY
  rw [targetCurve_negY, sourceCurve_negY]
  rw [← hX]
  rw [forwardX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, slope_of_X_ne hF]
  rw [forwardX_secant_form heq1 hx1, forwardX_secant_form heq2 hx2]
  simp only [forwardYModel, addX, sourceCurveModel]
  convert hid using 1 <;> ring

/-- The forward point map is additive in the generic affine secant branch. -/
theorem forwardPoint_add_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular (sourceCurveModel (A := A) (B := B)) x1 y1)
    (h2 : Nonsingular (sourceCurveModel (A := A) (B := B)) x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX (sourceCurveModel (A := A) (B := B)) x1 x2
        (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    (forwardPointModel (A := A) (B := B))
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12]
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  rw [forwardPoint_some_of_x_ne_zero hsum hr,
    forwardPoint_some_of_x_ne_zero h1 hx1,
    forwardPoint_some_of_x_ne_zero h2 hx2]
  change WeierstrassCurve.Affine.Point.some
      (forwardX
        (addX (sourceCurveModel (A := A) (B := B)) x1 x2 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2))
        (addY (sourceCurveModel (A := A) (B := B)) x1 x2 y1 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2)))
      ((forwardYModel (B := B))
        (addX (sourceCurveModel (A := A) (B := B)) x1 x2 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2))
        (addY (sourceCurveModel (A := A) (B := B)) x1 x2 y1 (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2))) _ =
    (WeierstrassCurve.Affine.Point.some
        (forwardX x1 y1) ((forwardYModel (B := B)) x1 y1) _ : (TargetPointModel (A := A) (B := B))) +
      WeierstrassCurve.Affine.Point.some
        (forwardX x2 y2) ((forwardYModel (B := B)) x2 y2) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hF,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨forward_add_x_generic h1 h2 hx1 hx2 hx12 hr hF,
    forward_add_y_generic h1 h2 hx1 hx2 hx12 hr hF⟩

private theorem forwardPoint_add_of_forwardX_eq
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular (sourceCurveModel (A := A) (B := B)) x1 y1)
    (h2 : Nonsingular (sourceCurveModel (A := A) (B := B)) x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hF : forwardX x1 y1 = forwardX x2 y2) :
    (forwardPointModel (A := A) (B := B))
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  have hf1 : Nonsingular (targetCurveModel (A := A) (B := B)) (forwardX x1 y1) ((forwardYModel (B := B)) x1 y1) :=
    equation_iff_nonsingular.mp
      (forward_equation hx1 (equation_iff_nonsingular.mpr h1))
  have hf2 : Nonsingular (targetCurveModel (A := A) (B := B)) (forwardX x2 y2) ((forwardYModel (B := B)) x2 y2) :=
    equation_iff_nonsingular.mp
      (forward_equation hx2 (equation_iff_nonsingular.mpr h2))
  have hKneg : -(sourceKernel (A := A) (B := B)) = sourceKernel (A := A) (B := B) := by
    rw [neg_eq_iff_add_eq_zero, ← two_nsmul, two_nsmul_sourceKernel]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (h₁ := hf1) (h₂ := hf2)).mp hF with hsame | hneg
  · have hmap :
        (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [forwardPoint_some_of_x_ne_zero h1 hx1,
        forwardPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hsame
    rcases (forwardPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (WeierstrassCurve.Affine.Point.some x2 y2 h2)).mp hmap with hQ | hQ
    · exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inl hQ)))
    · exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  · have hmapneg :
        (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          -(forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [forwardPoint_some_of_x_ne_zero h1 hx1,
        forwardPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hneg
    have hmap :
        (forwardPointModel (A := A) (B := B)) (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          (forwardPointModel (A := A) (B := B)) (-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) := by
      rw [forwardPoint_neg]
      exact hmapneg
    rcases (forwardPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (-(WeierstrassCurve.Affine.Point.some x2 y2 h2))).mp hmap with hQ | hQ
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
            congrArg Neg.neg hQ
      exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inl hQ'))))
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) + sourceKernel := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -((WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
                sourceKernel) := by rw [hQ]
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) + sourceKernel := by
            simp [hKneg, add_comm]
      exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ')))))

/-- The explicit forward two-isogeny is additive on all rational points. -/
theorem forwardPoint_add (P Q : (SourcePointModel (A := A) (B := B))) :
    (forwardPointModel (A := A) (B := B)) (P + Q) = (forwardPointModel (A := A) (B := B)) P + (forwardPointModel (A := A) (B := B)) Q := by
  cases P with
  | zero => exact forwardPoint_zero_add Q
  | some x1 y1 h1 =>
      cases Q with
      | zero => exact forwardPoint_add_zero _
      | some x2 y2 h2 =>
          by_cases hx1 : x1 = 0
          · have hy1 := full_y_zero_of_x_zero h1 hx1
            subst x1
            subst y1
            rw [show (WeierstrassCurve.Affine.Point.some 0 0 h1 : (SourcePointModel (A := A) (B := B))) =
              sourceKernel by rfl]
            rw [forwardPoint_sourceKernel_add, forwardPoint_sourceKernel, zero_add]
          · by_cases hx2 : x2 = 0
            · have hy2 := full_y_zero_of_x_zero h2 hx2
              subst x2
              subst y2
              rw [show (WeierstrassCurve.Affine.Point.some 0 0 h2 : (SourcePointModel (A := A) (B := B))) =
                sourceKernel by rfl]
              rw [forwardPoint_add_sourceKernel, forwardPoint_sourceKernel, add_zero]
            · by_cases hx12 : x1 = x2
              · rcases (WeierstrassCurve.Affine.Point.X_eq_iff
                  (h₁ := h1) (h₂ := h2)).mp hx12 with hsame | hneg
                · rw [← hsame]
                  exact forwardPoint_add_self _
                · have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
                          -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
                        (neg_neg _).symm
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
                        (congrArg Neg.neg hneg).symm
                  rw [hQ]
                  exact forwardPoint_add_neg _
              · by_cases hr : addX (sourceCurveModel (A := A) (B := B)) x1 x2
                    (slope (sourceCurveModel (A := A) (B := B)) x1 x2 y1 y2) = 0
                · have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
                  have hsumY := full_y_zero_of_x_zero hsum hr
                  have hsumK :
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 = sourceKernel := by
                    change
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 =
                        WeierstrassCurve.Affine.Point.some 0 0 _
                    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12,
                      WeierstrassCurve.Affine.Point.some.injEq]
                    exact ⟨hr, hsumY⟩
                  have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          sourceKernel := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : (SourcePointModel (A := A) (B := B))) =
                          -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                            ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : (SourcePointModel (A := A) (B := B))) +
                              WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
                        symm
                        rw [← add_assoc, neg_add_cancel, zero_add]
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          sourceKernel := by rw [hsumK]
                  exact forwardPoint_add_of_basic_or_kernel_relation _ _
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))
                · by_cases hF : forwardX x1 y1 = forwardX x2 y2
                  · exact forwardPoint_add_of_forwardX_eq h1 h2 hx1 hx2 hF
                  · exact forwardPoint_add_generic h1 h2 hx1 hx2 hx12 hr hF

/-- The explicit forward two-isogeny as an additive homomorphism. -/
noncomputable def forwardPointHom : (SourcePointModel (A := A) (B := B)) →+ (TargetPointModel (A := A) (B := B)) where
  toFun := (forwardPointModel (A := A) (B := B))
  map_zero' := forwardPoint_zero
  map_add' := forwardPoint_add

@[simp] theorem forwardPointHom_apply (P : (SourcePointModel (A := A) (B := B))) :
    forwardPointHom P = (forwardPointModel (A := A) (B := B)) P := rfl

/-! ## The dual homomorphism from a second forward Vélu map -/

private noncomputable def curveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst W'
  exact AddEquiv.refl _

private theorem curveEqAddEquiv_some
    {W W' : WeierstrassCurve ℚ} (h : W = W') {x y : ℚ}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    curveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst W'
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

def twoUnit : ℚˣ := Units.mk0 2 (by norm_num)

def dualScaleChange : WeierstrassCurve.VariableChange ℚ where
  u := twoUnit
  r := 0
  s := 0
  t := 0

theorem dualSource_eq_target :
    sourceCurveModel (A := -2 * A) (B := disc A B) =
      targetCurveModel (A := A) (B := B) := by
  ext <;> simp [sourceCurveModel, targetCurveModel]

theorem dualScale_curve :
    dualScaleChange •
        targetCurveModel (A := -2 * A) (B := disc A B) =
      sourceCurveModel (A := A) (B := B) := by
  ext <;>
    simp [dualScaleChange, twoUnit, sourceCurveModel, targetCurveModel, disc,
      WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;>
    ring

/-- The explicit dual two-isogeny as an additive homomorphism. -/
noncomputable def dualPointHom :
    (TargetPointModel (A := A) (B := B)) →+
      (SourcePointModel (A := A) (B := B)) := by
  letI : (sourceCurveModel (A := -2 * A) (B := disc A B)).IsElliptic := by
    rw [dualSource_eq_target (A := A) (B := B)]
    infer_instance
  let e₁ : (TargetPointModel (A := A) (B := B)) ≃+
      SourcePointModel (A := -2 * A) (B := disc A B) :=
    curveEqAddEquiv (dualSource_eq_target (A := A) (B := B)).symm
  let e₂ : TargetPointModel (A := -2 * A) (B := disc A B) ≃+
      SourcePointModel (A := A) (B := B) :=
    (variableChangePointAddEquiv
      (targetCurveModel (A := -2 * A) (B := disc A B)) dualScaleChange).trans
      (curveEqAddEquiv (dualScale_curve (A := A) (B := B)))
  exact e₂.toAddMonoidHom.comp
    ((forwardPointHom (A := -2 * A) (B := disc A B)).comp e₁.toAddMonoidHom)

@[simp] theorem dualPointHom_apply
    (P : TargetPointModel (A := A) (B := B)) :
    (dualPointHom (A := A) (B := B)) P =
      (dualPointModel (A := A) (B := B)) P := by
  letI : (sourceCurveModel (A := -2 * A) (B := disc A B)).IsElliptic := by
    rw [dualSource_eq_target (A := A) (B := B)]
    infer_instance
  change
    ((variableChangePointAddEquiv
        (targetCurveModel (A := -2 * A) (B := disc A B)) dualScaleChange).trans
      (curveEqAddEquiv (dualScale_curve (A := A) (B := B))))
        ((forwardPointHom (A := -2 * A) (B := disc A B))
          ((curveEqAddEquiv (dualSource_eq_target (A := A) (B := B)).symm) P)) =
      (dualPointModel (A := A) (B := B)) P
  cases P with
  | zero =>
      change
        ((variableChangePointAddEquiv
            (targetCurveModel (A := -2 * A) (B := disc A B)) dualScaleChange).trans
          (curveEqAddEquiv (dualScale_curve (A := A) (B := B))))
            ((forwardPointHom (A := -2 * A) (B := disc A B))
              ((curveEqAddEquiv
                (dualSource_eq_target (A := A) (B := B)).symm)
                  (0 : TargetPointModel (A := A) (B := B)))) =
          (dualPointModel (A := A) (B := B))
            (0 : TargetPointModel (A := A) (B := B))
      simp
  | some x y h =>
      have h' : WeierstrassCurve.Affine.Nonsingular
          (sourceCurveModel (A := -2 * A) (B := disc A B)) x y := by
        rw [dualSource_eq_target (A := A) (B := B)]
        exact h
      rw [show (curveEqAddEquiv (dualSource_eq_target (A := A) (B := B)).symm)
          (WeierstrassCurve.Affine.Point.some x y h) =
            WeierstrassCurve.Affine.Point.some x y h' from
        curveEqAddEquiv_some _]
      by_cases hx : x = 0
      · rw [dualPoint_some_of_x_eq_zero h hx]
        rw [forwardPointHom_apply, forwardPoint_some_of_x_eq_zero _ hx]
        simp
      · rw [dualPoint_some_of_x_ne_zero h hx]
        have hf : WeierstrassCurve.Affine.Nonsingular
            (targetCurveModel (A := -2 * A) (B := disc A B))
            (forwardX x y) (forwardYModel (B := disc A B) x y) :=
          WeierstrassCurve.Affine.equation_iff_nonsingular.mp
            (forward_equation (A := -2 * A) (B := disc A B) hx
              (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h'))
        have hs : WeierstrassCurve.Affine.Nonsingular
            (dualScaleChange •
              targetCurveModel (A := -2 * A) (B := disc A B))
            (variableChangePointX dualScaleChange (forwardX x y))
            (variableChangePointY dualScaleChange (forwardX x y)
              (forwardYModel (B := disc A B) x y)) :=
          WeierstrassCurve.Affine.equation_iff_nonsingular.mp
            (variableChangePoint_equation
              (targetCurveModel (A := -2 * A) (B := disc A B))
              dualScaleChange
              (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr hf))
        have hs' : WeierstrassCurve.Affine.Nonsingular
            (sourceCurveModel (A := A) (B := B))
            (variableChangePointX dualScaleChange (forwardX x y))
            (variableChangePointY dualScaleChange (forwardX x y)
              (forwardYModel (B := disc A B) x y)) := by
          rw [← dualScale_curve (A := A) (B := B)]
          exact hs
        rw [forwardPointHom_apply, forwardPoint_some_of_x_ne_zero _ hx]
        change (curveEqAddEquiv (dualScale_curve (A := A) (B := B)))
            (variableChangePointMap
              (targetCurveModel (A := -2 * A) (B := disc A B)) dualScaleChange
              (WeierstrassCurve.Affine.Point.some
                (forwardX x y) (forwardYModel (B := disc A B) x y) hf)) = _
        simp only [variableChangePointMap]
        rw [show (curveEqAddEquiv (dualScale_curve (A := A) (B := B)))
            (WeierstrassCurve.Affine.Point.some
              (variableChangePointX dualScaleChange (forwardX x y))
              (variableChangePointY dualScaleChange (forwardX x y)
                (forwardYModel (B := disc A B) x y)) hs) =
              WeierstrassCurve.Affine.Point.some _ _ hs' from
          curveEqAddEquiv_some _]
        simp only [WeierstrassCurve.Affine.Point.mk]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [variableChangePointX, dualScaleChange, twoUnit, dualX,
            forwardX, div_eq_mul_inv]
          ring
        · simp [variableChangePointMap, variableChangePointY, dualScaleChange,
            twoUnit, dualYModel, forwardYModel]
          ring

/-! ## The quotient theorem on the standard model -/

theorem exists_standard_two_isogeny :
    ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic)
      (phi : (SourcePointModel (A := A) (B := B)) →+ (E'⁄ℚ).Point)
      (dual : (E'⁄ℚ).Point →+ (SourcePointModel (A := A) (B := B)))
      (eta : (E'⁄ℚ).Point),
      addOrderOf eta = 2 ∧
      (∀ R, phi R = 0 ↔ R = 0 ∨ R = sourceKernel (A := A) (B := B)) ∧
      (∀ R, dual (phi R) = 2 • R) ∧ dual eta = 0 := by
  let E' := targetCurveModel (A := A) (B := B)
  have hE' : E'.IsElliptic := by
    dsimp [E']
    infer_instance
  let phi := forwardPointHom (A := A) (B := B)
  let dual := dualPointHom (A := A) (B := B)
  let eta := targetKernel (A := A) (B := B)
  refine ⟨E', hE', phi, dual, eta, ?_, ?_, ?_, ?_⟩
  · exact addOrderOf_eq_prime
      (two_nsmul_targetKernel (A := A) (B := B))
      (targetKernel_ne_zero (A := A) (B := B))
  · intro R
    exact forwardPoint_eq_zero_iff R
  · intro R
    change (dualPointHom (A := A) (B := B))
      ((forwardPointHom (A := A) (B := B)) R) = 2 • R
    rw [dualPointHom_apply, forwardPointHom_apply]
    exact dual_comp_forwardPoint R
  · change (dualPointHom (A := A) (B := B))
      (targetKernel (A := A) (B := B)) = 0
    rw [dualPointHom_apply]
    exact dualPoint_targetKernel

/-! ## Reduction of an arbitrary rational two-torsion point -/

omit A B sourceCurve_isElliptic in
/-- Every rational point of order two gives the rational degree-two Vélu
quotient, its dual, and the dual kernel point. -/
theorem exists_rational_two_isogeny_quotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {Q : (E⁄ℚ).Point} (hQ : addOrderOf Q = 2) :
    ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic)
      (phi : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
      (dual : (E'⁄ℚ).Point →+ (E⁄ℚ).Point)
      (eta : (E'⁄ℚ).Point),
      addOrderOf eta = 2 ∧
      (∀ R, phi R = 0 ↔ R = 0 ∨ R = Q) ∧
      (∀ R, dual (phi R) = 2 • R) ∧ dual eta = 0 := by
  cases Q with
  | zero =>
      change addOrderOf (0 : (E⁄ℚ).Point) = 2 at hQ
      simp at hQ
  | some r y h =>
      letI : (E⁄ℚ).IsElliptic := by
        change (E.map (algebraMap ℚ ℚ)).IsElliptic
        infer_instance
      have htwo : (2 : ℕ) •
          (WeierstrassCurve.Affine.Point.some r y h : (E⁄ℚ).Point) = 0 := by
        have hz := addOrderOf_nsmul_eq_zero
          (WeierstrassCurve.Affine.Point.some r y h : (E⁄ℚ).Point)
        rw [hQ] at hz
        exact hz
      have hselfneg :
          (WeierstrassCurve.Affine.Point.some r y h : (E⁄ℚ).Point) =
            -(WeierstrassCurve.Affine.Point.some r y h) := by
        apply eq_neg_of_add_eq_zero_left
        simpa [two_nsmul] using htwo
      rw [WeierstrassCurve.Affine.Point.neg_some] at hselfneg
      have htorsCoord := (WeierstrassCurve.Affine.Point.some.inj hselfneg).2
      have htors : (E⁄ℚ).a₃ + r * (E⁄ℚ).a₁ + 2 * y = 0 := by
        unfold WeierstrassCurve.Affine.negY at htorsCoord
        linear_combination htorsCoord
      have htorsE : E.a₃ + r * E.a₁ + 2 * y = 0 := by
        simpa [WeierstrassCurve.baseChange] using htors
      have heq := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at heq
      have heqE : y ^ 2 + E.a₁ * r * y + E.a₃ * y =
          r ^ 3 + E.a₂ * r ^ 2 + E.a₄ * r + E.a₆ := by
        simpa [WeierstrassCurve.baseChange] using heq
      let C : WeierstrassCurve.VariableChange ℚ :=
        { u := 1
          r := r
          s := -(E⁄ℚ).a₁ / 2
          t := y }
      let W : WeierstrassCurve ℚ := C • (E⁄ℚ)
      let A₀ : ℚ := W.a₂
      let B₀ : ℚ := W.a₄
      haveI : W.IsElliptic := by
        dsimp [W]
        infer_instance
      have hcurve : W = sourceCurveModel (A := A₀) (B := B₀) := by
        ext
        · simp [W, C, sourceCurveModel,
            WeierstrassCurve.variableChange_a₁]
          ring
        · rfl
        · simp [W, C, sourceCurveModel,
            WeierstrassCurve.variableChange_a₃]
          linear_combination htorsE
        · rfl
        · simp [W, C, sourceCurveModel,
            WeierstrassCurve.variableChange_a₆]
          linear_combination -heqE
      letI : (sourceCurveModel (A := A₀) (B := B₀)).IsElliptic := by
        rw [← hcurve]
        infer_instance
      let e : (E⁄ℚ).Point ≃+ SourcePointModel (A := A₀) (B := B₀) :=
        (variableChangePointAddEquiv (E⁄ℚ) C).trans (curveEqAddEquiv hcurve)
      have htrans : WeierstrassCurve.Affine.Nonsingular W
          (variableChangePointX C r) (variableChangePointY C r y) := by
        dsimp [W]
        exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePoint_equation (E⁄ℚ) C
            (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))
      have htrans' : WeierstrassCurve.Affine.Nonsingular
          (sourceCurveModel (A := A₀) (B := B₀))
          (variableChangePointX C r) (variableChangePointY C r y) := by
        rw [← hcurve]
        exact htrans
      have heQ : e (WeierstrassCurve.Affine.Point.some r y h) =
          sourceKernel (A := A₀) (B := B₀) := by
        change (curveEqAddEquiv hcurve)
            (variableChangePointMap (E⁄ℚ) C
              (WeierstrassCurve.Affine.Point.some r y h)) = _
        simp only [variableChangePointMap]
        rw [show (curveEqAddEquiv hcurve)
            (WeierstrassCurve.Affine.Point.some
              (variableChangePointX C r) (variableChangePointY C r y) htrans) =
              WeierstrassCurve.Affine.Point.some _ _ htrans' from
          curveEqAddEquiv_some _]
        simp only [sourceKernel, WeierstrassCurve.Affine.Point.mk]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [variableChangePointX, C]
        · simp [variableChangePointY, variableChangePointX, C]
      obtain ⟨E', hE', phi₀, dual₀, eta, hetaOrder, hphiKernel,
          hcomp, hetaKernel⟩ :=
        exists_standard_two_isogeny (A := A₀) (B := B₀)
      let phi : (E⁄ℚ).Point →+ (E'⁄ℚ).Point :=
        phi₀.comp e.toAddMonoidHom
      let dual : (E'⁄ℚ).Point →+ (E⁄ℚ).Point :=
        e.symm.toAddMonoidHom.comp dual₀
      refine ⟨E', hE', phi, dual, eta, hetaOrder, ?_, ?_, ?_⟩
      · intro R
        change phi₀ (e R) = 0 ↔ R = 0 ∨
          R = WeierstrassCurve.Affine.Point.some r y h
        rw [hphiKernel]
        constructor
        · rintro (hzero | hkernel)
          · left
            apply e.injective
            simpa using hzero
          · right
            apply e.injective
            simpa [heQ] using hkernel
        · rintro (rfl | rfl)
          · exact Or.inl e.map_zero
          · exact Or.inr heQ
      · intro R
        change e.symm (dual₀ (phi₀ (e R))) = 2 • R
        rw [hcomp]
        simpa using e.symm.map_nsmul 2 (e R)
      · change e.symm (dual₀ eta) = 0
        rw [hetaKernel]
        exact e.symm.map_zero


end

end MazurProof.Velu2Isogeny
