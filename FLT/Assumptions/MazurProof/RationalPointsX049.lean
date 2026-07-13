import FLT.Assumptions.MazurProof.RationalPointsN15Descent

/-!
# Rational points on `X₀(49)`

This file proves the rank-zero calculation for the minimal model

`y² + x*y = x³ - x² - 2*x - 1`.

The proof uses the split model

`V² = U³ + 21*U² + 112*U`

and its rational `2`-isogenous companion

`Z² = X³ - 42*X² - 7*X`.
-/

namespace MazurProof.RationalPointsX049

noncomputable section

open RationalPointsN15Descent

def E49Curve : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := -1
  a₃ := 0
  a₄ := -2
  a₆ := -1

def ESplitCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 21
  a₃ := 0
  a₄ := 112
  a₆ := 0

def EHatCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -42
  a₃ := 0
  a₄ := -7
  a₆ := 0

def OnE49 (x y : ℚ) : Prop :=
  y ^ 2 + x * y = x ^ 3 - x ^ 2 - 2 * x - 1

def OnESplit (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 + 21 * U ^ 2 + 112 * U

def OnEHat (X Z : ℚ) : Prop :=
  Z ^ 2 = X ^ 3 - 42 * X ^ 2 - 7 * X

theorem E49Curve_delta : E49Curve.Δ = (-343 : ℚ) := by
  norm_num [E49Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem ESplitCurve_delta : ESplitCurve.Δ = (-1404928 : ℚ) := by
  norm_num [ESplitCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem EHatCurve_delta : EHatCurve.Δ = (1404928 : ℚ) := by
  norm_num [EHatCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E49Curve_isElliptic : E49Curve.IsElliptic where
  isUnit := by rw [E49Curve_delta]; norm_num

instance ESplitCurve_isElliptic : ESplitCurve.IsElliptic where
  isUnit := by rw [ESplitCurve_delta]; norm_num

instance EHatCurve_isElliptic : EHatCurve.IsElliptic where
  isUnit := by rw [EHatCurve_delta]; norm_num

@[simp] theorem E49Curve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E49Curve x y ↔ OnE49 x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E49Curve, OnE49]
  ring_nf

@[simp] theorem ESplitCurve_equation_iff (U V : ℚ) :
    WeierstrassCurve.Affine.Equation ESplitCurve U V ↔ OnESplit U V := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ESplitCurve, OnESplit]
  ring_nf

@[simp] theorem EHatCurve_equation_iff (X Z : ℚ) :
    WeierstrassCurve.Affine.Equation EHatCurve X Z ↔ OnEHat X Z := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [EHatCurve, OnEHat]
  ring_nf

abbrev E49Point := WeierstrassCurve.Affine.Point E49Curve
abbrev ESplitPoint := WeierstrassCurve.Affine.Point ESplitCurve
abbrev EHatPoint := WeierstrassCurve.Affine.Point EHatCurve

theorem to_split_equation {x y : ℚ} (h : OnE49 x y) :
    OnESplit (4 * (x - 2)) (4 * (2 * y + x)) := by
  unfold OnE49 at h
  unfold OnESplit
  linear_combination 64 * h

theorem from_split_equation {U V : ℚ} (h : OnESplit U V) :
    OnE49 (U / 4 + 2) (V / 8 - U / 8 - 1) := by
  unfold OnESplit at h
  unfold OnE49
  linear_combination (1 / 64 : ℚ) * h

/-! ## The explicit two-isogeny -/

def phiX (U V : ℚ) : ℚ := V ^ 2 / U ^ 2

def phiY (U V : ℚ) : ℚ := V * (112 - U ^ 2) / U ^ 2

def dualX (X Z : ℚ) : ℚ := Z ^ 2 / (4 * X ^ 2)

def dualY (X Z : ℚ) : ℚ := Z * (-7 - X ^ 2) / (8 * X ^ 2)

theorem phi_on_curve {U V : ℚ} (hU : U ≠ 0) (h : OnESplit U V) :
    OnEHat (phiX U V) (phiY U V) := by
  unfold OnESplit at h
  unfold OnEHat phiX phiY
  field_simp [hU]
  rw [h]
  ring

theorem dual_on_curve {X Z : ℚ} (hX : X ≠ 0) (h : OnEHat X Z) :
    OnESplit (dualX X Z) (dualY X Z) := by
  unfold OnEHat at h
  unfold OnESplit dualX dualY
  field_simp [hX]
  rw [h]
  ring

noncomputable def phiPoint : ESplitPoint → EHatPoint
  | .zero => .zero
  | .some U _V h =>
      if hU : U = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (EHatCurve_equation_iff _ _ |>.2 <|
          phi_on_curve hU (ESplitCurve_equation_iff _ _ |>.1 h.1))

noncomputable def dualPoint : EHatPoint → ESplitPoint
  | .zero => .zero
  | .some X _Z h =>
      if hX : X = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (ESplitCurve_equation_iff _ _ |>.2 <|
          dual_on_curve hX (EHatCurve_equation_iff _ _ |>.1 h.1))

@[simp] theorem phiPoint_zero : phiPoint 0 = 0 := rfl

@[simp] theorem dualPoint_zero : dualPoint 0 = 0 := rfl

@[simp] theorem phiPoint_some_of_x_eq_zero {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hU : U = 0) :
    phiPoint (.some U V h) = 0 := by
  rw [phiPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] theorem dualPoint_some_of_x_eq_zero {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z)
    (hX : X = 0) :
    dualPoint (.some X Z h) = 0 := by
  rw [dualPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

theorem phiPoint_some_of_x_ne_zero {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hU : U ≠ 0) :
    phiPoint (.some U V h) =
      WeierstrassCurve.Affine.Point.mk
        (EHatCurve_equation_iff _ _ |>.2 <|
          phi_on_curve hU (ESplitCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [phiPoint, hU]

theorem dualPoint_some_of_x_ne_zero {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z)
    (hX : X ≠ 0) :
    dualPoint (.some X Z h) =
      WeierstrassCurve.Affine.Point.mk
        (ESplitCurve_equation_iff _ _ |>.2 <|
          dual_on_curve hX (EHatCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualPoint, hX]

/-! ### The two compositions -/

private def ESplitTangent (U V : ℚ) : ℚ :=
  (3 * U ^ 2 + 42 * U + 112) / (2 * V)

private def EHatTangent (X Z : ℚ) : ℚ :=
  (3 * X ^ 2 - 84 * X - 7) / (2 * Z)

private def tangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

theorem dual_phi_x {U V : ℚ} (hU : U ≠ 0) (hV : V ≠ 0)
    (h : OnESplit U V) :
    dualX (phiX U V) (phiY U V) =
      tangentX 21 U (ESplitTangent U V) := by
  unfold dualX phiX phiY tangentX ESplitTangent
  unfold OnESplit at h
  field_simp [hU, hV]
  rw [h]
  ring

theorem dual_phi_y {U V : ℚ} (hU : U ≠ 0) (hV : V ≠ 0)
    (h : OnESplit U V) :
    dualY (phiX U V) (phiY U V) =
      -(ESplitTangent U V *
          (tangentX 21 U (ESplitTangent U V) - U) + V) := by
  unfold dualY phiX phiY tangentX ESplitTangent
  unfold OnESplit at h
  field_simp [hU, hV]
  have hV4 : V ^ 4 = (U ^ 3 + 21 * U ^ 2 + 112 * U) ^ 2 := by
    calc
      V ^ 4 = (V ^ 2) ^ 2 := by ring
      _ = (U ^ 3 + 21 * U ^ 2 + 112 * U) ^ 2 := by rw [h]
  rw [hV4, h]
  ring

theorem phi_dual_x {X Z : ℚ} (hX : X ≠ 0) (hZ : Z ≠ 0)
    (h : OnEHat X Z) :
    phiX (dualX X Z) (dualY X Z) =
      tangentX (-42) X (EHatTangent X Z) := by
  unfold phiX dualX dualY tangentX EHatTangent
  unfold OnEHat at h
  field_simp [hX, hZ]
  rw [h]
  ring

theorem phi_dual_y {X Z : ℚ} (hX : X ≠ 0) (hZ : Z ≠ 0)
    (h : OnEHat X Z) :
    phiY (dualX X Z) (dualY X Z) =
      -(EHatTangent X Z *
          (tangentX (-42) X (EHatTangent X Z) - X) + Z) := by
  unfold phiY dualX dualY tangentX EHatTangent
  unfold OnEHat at h
  field_simp [hX, hZ]
  have hZ4 : Z ^ 4 = (X ^ 3 - 42 * X ^ 2 - 7 * X) ^ 2 := by
    calc
      Z ^ 4 = (Z ^ 2) ^ 2 := by ring
      _ = (X ^ 3 - 42 * X ^ 2 - 7 * X) ^ 2 := by rw [h]
  rw [hZ4, h]
  ring

@[simp] theorem ESplitCurve_negY (U V : ℚ) :
    WeierstrassCurve.Affine.negY ESplitCurve U V = -V := by
  simp [WeierstrassCurve.Affine.negY, ESplitCurve]

@[simp] theorem EHatCurve_negY (X Z : ℚ) :
    WeierstrassCurve.Affine.negY EHatCurve X Z = -Z := by
  simp [WeierstrassCurve.Affine.negY, EHatCurve]

private theorem ESplitCurve_slope_self {U V : ℚ} (hV : V ≠ 0) :
    WeierstrassCurve.Affine.slope ESplitCurve U U V V =
      ESplitTangent U V := by
  have hneg : V ≠ WeierstrassCurve.Affine.negY ESplitCurve U V := by
    intro h
    apply hV
    rw [ESplitCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [ESplitCurve, ESplitTangent, WeierstrassCurve.Affine.negY]
  ring

private theorem EHatCurve_slope_self {X Z : ℚ} (hZ : Z ≠ 0) :
    WeierstrassCurve.Affine.slope EHatCurve X X Z Z =
      EHatTangent X Z := by
  have hneg : Z ≠ WeierstrassCurve.Affine.negY EHatCurve X Z := by
    intro h
    apply hZ
    rw [EHatCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [EHatCurve, EHatTangent, WeierstrassCurve.Affine.negY]
  ring

private theorem ESplitCurve_addX_tangent (U V : ℚ) :
    WeierstrassCurve.Affine.addX ESplitCurve U U (ESplitTangent U V) =
      tangentX 21 U (ESplitTangent U V) := by
  simp [ESplitCurve, tangentX]
  ring

private theorem EHatCurve_addX_tangent (X Z : ℚ) :
    WeierstrassCurve.Affine.addX EHatCurve X X (EHatTangent X Z) =
      tangentX (-42) X (EHatTangent X Z) := by
  simp [EHatCurve, tangentX]
  ring

private theorem ESplitCurve_addY_tangent (U V : ℚ) :
    WeierstrassCurve.Affine.addY ESplitCurve U U V (ESplitTangent U V) =
      -(ESplitTangent U V *
          (tangentX 21 U (ESplitTangent U V) - U) + V) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX tangentX
    ESplitCurve
  ring

private theorem EHatCurve_addY_tangent (X Z : ℚ) :
    WeierstrassCurve.Affine.addY EHatCurve X X Z (EHatTangent X Z) =
      -(EHatTangent X Z *
          (tangentX (-42) X (EHatTangent X Z) - X) + Z) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX tangentX
    EHatCurve
  ring

private theorem ESplit_y_zero_of_x_zero {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hU : U = 0) : V = 0 := by
  have heq := (ESplitCurve_equation_iff U V).mp h.1
  unfold OnESplit at heq
  rw [hU] at heq
  norm_num at heq
  nlinarith

private theorem EHat_y_zero_of_x_zero {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z)
    (hX : X = 0) : Z = 0 := by
  have heq := (EHatCurve_equation_iff X Z).mp h.1
  unfold OnEHat at heq
  rw [hX] at heq
  norm_num at heq
  nlinarith

private theorem ESplit_double_eq_zero_of_y_zero {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hV : V = 0) :
    2 • (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hV, ESplitCurve])

private theorem EHat_double_eq_zero_of_y_zero {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z)
    (hZ : Z = 0) :
    2 • (WeierstrassCurve.Affine.Point.some X Z h : EHatPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hZ, EHatCurve])

theorem dual_comp_phiPoint (P : ESplitPoint) :
    dualPoint (phiPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some U V h =>
      by_cases hU : U = 0
      · have hV : V = 0 := ESplit_y_zero_of_x_zero h hU
        rw [phiPoint_some_of_x_eq_zero h hU, dualPoint_zero]
        exact (ESplit_double_eq_zero_of_y_zero h hV).symm
      · rw [phiPoint_some_of_x_ne_zero h hU]
        by_cases hV : V = 0
        · have hpx : phiX U V = 0 := by simp [phiX, hV]
          change dualPoint (.some (phiX U V) (phiY U V) _) = _
          rw [dualPoint_some_of_x_eq_zero _ hpx]
          exact (ESplit_double_eq_zero_of_y_zero h hV).symm
        · have hpx : phiX U V ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hV) (pow_ne_zero 2 hU)
          change dualPoint (.some (phiX U V) (phiY U V) _) = _
          rw [dualPoint_some_of_x_ne_zero _ hpx]
          have hneg : V ≠ WeierstrassCurve.Affine.negY ESplitCurve U V := by
            intro heq
            simp [WeierstrassCurve.Affine.negY, ESplitCurve] at heq
            apply hV
            linarith
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
          change WeierstrassCurve.Affine.Point.some
              (dualX (phiX U V) (phiY U V))
              (dualY (phiX U V) (phiY U V)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX ESplitCurve U U
                (WeierstrassCurve.Affine.slope ESplitCurve U U V V))
              (WeierstrassCurve.Affine.addY ESplitCurve U U V
                (WeierstrassCurve.Affine.slope ESplitCurve U U V V)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq := (ESplitCurve_equation_iff U V).mp h.1
          constructor
          · rw [dual_phi_x hU hV heq, ESplitCurve_slope_self hV,
              ESplitCurve_addX_tangent]
          · rw [dual_phi_y hU hV heq, ESplitCurve_slope_self hV,
              ESplitCurve_addY_tangent]

theorem phi_comp_dualPoint (P : EHatPoint) :
    phiPoint (dualPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some X Z h =>
      by_cases hX : X = 0
      · have hZ : Z = 0 := EHat_y_zero_of_x_zero h hX
        rw [dualPoint_some_of_x_eq_zero h hX, phiPoint_zero]
        exact (EHat_double_eq_zero_of_y_zero h hZ).symm
      · rw [dualPoint_some_of_x_ne_zero h hX]
        by_cases hZ : Z = 0
        · have hdx : dualX X Z = 0 := by simp [dualX, hZ]
          change phiPoint (.some (dualX X Z) (dualY X Z) _) = _
          rw [phiPoint_some_of_x_eq_zero _ hdx]
          exact (EHat_double_eq_zero_of_y_zero h hZ).symm
        · have hdx : dualX X Z ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hZ)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))
          change phiPoint (.some (dualX X Z) (dualY X Z) _) = _
          rw [phiPoint_some_of_x_ne_zero _ hdx]
          have hneg : Z ≠ WeierstrassCurve.Affine.negY EHatCurve X Z := by
            intro heq
            simp [WeierstrassCurve.Affine.negY, EHatCurve] at heq
            apply hZ
            linarith
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
          change WeierstrassCurve.Affine.Point.some
              (phiX (dualX X Z) (dualY X Z))
              (phiY (dualX X Z) (dualY X Z)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX EHatCurve X X
                (WeierstrassCurve.Affine.slope EHatCurve X X Z Z))
              (WeierstrassCurve.Affine.addY EHatCurve X X Z
                (WeierstrassCurve.Affine.slope EHatCurve X X Z Z)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq := (EHatCurve_equation_iff X Z).mp h.1
          constructor
          · rw [phi_dual_x hX hZ heq, EHatCurve_slope_self hZ,
              EHatCurve_addX_tangent]
          · rw [phi_dual_y hX hZ heq, EHatCurve_slope_self hZ,
              EHatCurve_addY_tangent]

/-! ### Explicit reconstruction of isogeny preimages -/

def dualPreimageX (r V : ℚ) : ℚ :=
  21 + 2 * r ^ 2 - 2 * V / r

def dualPreimageY (r V : ℚ) : ℚ :=
  2 * r * dualPreimageX r V

def phiPreimageX (r Z : ℚ) : ℚ :=
  (r ^ 2 - 21 - Z / r) / 2

def phiPreimageY (r Z : ℚ) : ℚ :=
  r * phiPreimageX r Z

theorem exists_dualPoint_preimage_of_x_eq_sq {U V r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hU : U ≠ 0) (hr : U = r ^ 2) :
    ∃ Q : EHatPoint,
      dualPoint Q = WeierstrassCurve.Affine.Point.some U V h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hU
    rw [hr, hrz]
    norm_num
  have hcurve : V ^ 2 = U ^ 3 + 21 * U ^ 2 + 112 * U := by
    exact (ESplitCurve_equation_iff U V).mp h.1
  have hcurveR : V ^ 2 = r ^ 6 + 21 * r ^ 4 + 112 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := dualPreimageX r V
  let qy := dualPreimageY r V
  have hprod : qx * (21 + 2 * r ^ 2 + 2 * V / r) = -7 := by
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : -7 - qx ^ 2 = 4 * qx * V / r := by
    rw [← hprod]
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : OnEHat qx qy := by
    unfold OnEHat
    dsimp [qx, qy, dualPreimageX, dualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (2 * V - 2 * r ^ 3 - 21 * r) * hcurveR
  have hqns : WeierstrassCurve.Affine.Nonsingular EHatCurve qx qy :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((EHatCurve_equation_iff qx qy).mpr hqeq)
  let Q : EHatPoint := WeierstrassCurve.Affine.Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [dualPoint_some_of_x_ne_zero hqns hqx]
  change WeierstrassCurve.Affine.Point.some (dualX qx qy) (dualY qx qy) _ =
    WeierstrassCurve.Affine.Point.some U V h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / (4 * qx ^ 2) = U
    rw [hr]
    field_simp [hqx]
    ring
  · change (2 * r * qx) * (-7 - qx ^ 2) / (8 * qx ^ 2) = V
    rw [hnum]
    field_simp [hqx, hr0]
    ring

theorem exists_phiPoint_preimage_of_x_eq_sq {X Z r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z)
    (hX : X ≠ 0) (hr : X = r ^ 2) :
    ∃ P : ESplitPoint,
      phiPoint P = WeierstrassCurve.Affine.Point.some X Z h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hX
    rw [hr, hrz]
    norm_num
  have hcurve : Z ^ 2 = X ^ 3 - 42 * X ^ 2 - 7 * X := by
    exact (EHatCurve_equation_iff X Z).mp h.1
  have hcurveR : Z ^ 2 = r ^ 6 - 42 * r ^ 4 - 7 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := phiPreimageX r Z
  let py := phiPreimageY r Z
  have hprod : px * ((r ^ 2 - 21 + Z / r) / 2) = 112 := by
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 112 - px ^ 2 = px * Z / r := by
    rw [← hprod]
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    ring
  have hpeq : OnESplit px py := by
    unfold OnESplit
    dsimp [px, py, phiPreimageX, phiPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + 21 * r + Z) * hcurveR
  have hpns : WeierstrassCurve.Affine.Nonsingular ESplitCurve px py :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((ESplitCurve_equation_iff px py).mpr hpeq)
  let P : ESplitPoint := WeierstrassCurve.Affine.Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [phiPoint_some_of_x_ne_zero hpns hpx]
  change WeierstrassCurve.Affine.Point.some (phiX px py) (phiY px py) _ =
    WeierstrassCurve.Affine.Point.some X Z h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = X
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (112 - px ^ 2) / px ^ 2 = Z
    rw [hnum]
    field_simp [hpx, hr0]

/-! ## The two Kummer images -/

theorem ESplit_integral_model {U V : ℚ} (h : OnESplit U V) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      U = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + 21 * A * B ^ 2 + 112 * B ^ 4) := by
  have hcubic : V ^ 2 =
      U ^ 3 + ((21 : ℤ) : ℚ) * U ^ 2 + ((112 : ℤ) : ℚ) * U := by
    simpa [OnESplit] using h
  exact integral_model_monic 21 112 U V hcubic

theorem EHat_integral_model {X Z : ℚ} (h : OnEHat X Z) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      X = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 - 42 * A * B ^ 2 - 7 * B ^ 4) := by
  have hcubic : Z ^ 2 =
      X ^ 3 + ((-42 : ℤ) : ℚ) * X ^ 2 + ((-7 : ℤ) : ℚ) * X := by
    simpa [OnEHat, sub_eq_add_neg] using h
  simpa [sub_eq_add_neg] using integral_model_monic (-42) (-7) X Z hcubic

private theorem squarefree_dvd_112 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 112) :
    d = 1 ∨ d = 2 ∨ d = 7 ∨ d = 14 := by
  have hpow : d ∣ 14 ^ 4 := by
    have : 112 ∣ 14 ^ 4 := by norm_num
    exact hdiv.trans this
  have hd14 : d ∣ 14 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 4 ≠ 0)).mp hpow
  have hdle : d ≤ 14 := Nat.le_of_dvd (by norm_num) hd14
  interval_cases d <;> norm_num at hd14
  all_goals simp

private theorem squarefree_dvd_7 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 7) : d = 1 ∨ d = 7 := by
  exact (Nat.dvd_prime (by norm_num)).mp hdiv

private theorem rat_squareclass_of_integral
    {x : ℚ} {A B d r : ℤ} (hB : B ≠ 0)
    (hx : x = (A : ℚ) / (B : ℚ) ^ 2)
    (hA : A = d * r ^ 2) :
    x = (d : ℚ) * ((r : ℚ) / (B : ℚ)) ^ 2 := by
  rw [hx, hA]
  push_cast
  field_simp [Int.cast_ne_zero.mpr hB]

private def reduce16to2 : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

/-- The four square residues modulo `16`, obtained by the sixteen individual
residue classes rather than a search over triples. -/
private theorem zmod16_sq_cases (a : ZMod 16) :
    a ^ 2 = 0 ∨ a ^ 2 = 1 ∨ a ^ 2 = 4 ∨ a ^ 2 = 9 := by
  fin_cases a <;> decide

private theorem reduce16to2_eq_zero_of_sq_even {a : ZMod 16}
    (h : a ^ 2 = 0 ∨ a ^ 2 = 4) : reduce16to2 a = 0 := by
  fin_cases a <;> decide

private theorem primitive_sq_residues
    {r B : ℤ} (hcop : Int.gcd r B = 1) :
    ¬ (((r : ZMod 16) ^ 2 = 0 ∨ (r : ZMod 16) ^ 2 = 4) ∧
      ((B : ZMod 16) ^ 2 = 0 ∨ (B : ZMod 16) ^ 2 = 4)) := by
  rintro ⟨hr, hB⟩
  have hr2 : (r : ZMod 2) = 0 := by
    simpa [reduce16to2, ZMod.castHom_apply] using
      reduce16to2_eq_zero_of_sq_even hr
  have hB2 : (B : ZMod 2) = 0 := by
    simpa [reduce16to2, ZMod.castHom_apply] using
      reduce16to2_eq_zero_of_sq_even hB
  have hdr : (2 : ℤ) ∣ r := (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp hr2
  have hdB : (2 : ℤ) ∣ B := (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp hB2
  have hdg : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hdr hdB
  rw [hcop] at hdg
  norm_num at hdg

private theorem no_primitive_ESplit_two_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 + 21 * r ^ 2 * B ^ 2 + 56 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  have hr := zmod16_sq_cases (r : ZMod 16)
  have hB := zmod16_sq_cases (B : ZMod 16)
  have hz := zmod16_sq_cases (z : ZMod 16)
  have hp := primitive_sq_residues hcop
  have hr4 : (r : ZMod 16) ^ 4 = ((r : ZMod 16) ^ 2) ^ 2 := by ring
  have hB4 : (B : ZMod 16) ^ 4 = ((B : ZMod 16) ^ 2) ^ 2 := by ring
  rcases hr with hr | hr | hr | hr <;>
    rcases hB with hB | hB | hB | hB <;>
      rcases hz with hz | hz | hz | hz <;>
        first
        | exact hp ⟨by simp_all, by simp_all⟩
        | norm_num [hr4, hB4, hr, hB, hz] at hm

private theorem no_primitive_ESplit_fourteen_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 14 * r ^ 4 + 21 * r ^ 2 * B ^ 2 + 8 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  have hr := zmod16_sq_cases (r : ZMod 16)
  have hB := zmod16_sq_cases (B : ZMod 16)
  have hz := zmod16_sq_cases (z : ZMod 16)
  have hp := primitive_sq_residues hcop
  have hr4 : (r : ZMod 16) ^ 4 = ((r : ZMod 16) ^ 2) ^ 2 := by ring
  have hB4 : (B : ZMod 16) ^ 4 = ((B : ZMod 16) ^ 2) ^ 2 := by ring
  rcases hr with hr | hr | hr | hr <;>
    rcases hB with hB | hB | hB | hB <;>
      rcases hz with hz | hz | hz | hz <;>
        first
        | exact hp ⟨by simp_all, by simp_all⟩
        | norm_num [hr4, hB4, hr, hB, hz] at hm

private theorem no_primitive_EHat_neg_one_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -(r ^ 4) - 42 * r ^ 2 * B ^ 2 + 7 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  have hr := zmod16_sq_cases (r : ZMod 16)
  have hB := zmod16_sq_cases (B : ZMod 16)
  have hz := zmod16_sq_cases (z : ZMod 16)
  have hp := primitive_sq_residues hcop
  have hr4 : (r : ZMod 16) ^ 4 = ((r : ZMod 16) ^ 2) ^ 2 := by ring
  have hB4 : (B : ZMod 16) ^ 4 = ((B : ZMod 16) ^ 2) ^ 2 := by ring
  rcases hr with hr | hr | hr | hr <;>
    rcases hB with hB | hB | hB | hB <;>
      rcases hz with hz | hz | hz | hz <;>
        first
        | exact hp ⟨by simp_all, by simp_all⟩
        | norm_num [hr4, hB4, hr, hB, hz] at hm

private theorem no_primitive_EHat_seven_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 7 * r ^ 4 - 42 * r ^ 2 * B ^ 2 - B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  have hr := zmod16_sq_cases (r : ZMod 16)
  have hB := zmod16_sq_cases (B : ZMod 16)
  have hz := zmod16_sq_cases (z : ZMod 16)
  have hp := primitive_sq_residues hcop
  have hr4 : (r : ZMod 16) ^ 4 = ((r : ZMod 16) ^ 2) ^ 2 := by ring
  have hB4 : (B : ZMod 16) ^ 4 = ((B : ZMod 16) ^ 2) ^ 2 := by ring
  rcases hr with hr | hr | hr | hr <;>
    rcases hB with hB | hB | hB | hB <;>
      rcases hz with hz | hz | hz | hz <;>
        first
        | exact hp ⟨by simp_all, by simp_all⟩
        | norm_num [hr4, hB4, hr, hB, hz] at hm

private theorem ESplit_x_nonnegative {U V : ℚ} (h : OnESplit U V) : 0 ≤ U := by
  by_contra hU
  have hUneg : U < 0 := lt_of_not_ge hU
  have hquad : 0 < U ^ 2 + 21 * U + 112 := by
    nlinarith [sq_nonneg (2 * U + 21)]
  unfold OnESplit at h
  nlinarith [mul_neg_of_neg_of_pos hUneg hquad, sq_nonneg V]

/-- The first Kummer image consists of the classes `1` and `7`. -/
theorem ESplit_rational_x_squareclasses {U V : ℚ}
    (h : OnESplit U V) (hU0 : U ≠ 0) :
    ∃ q : ℚ, U = q ^ 2 ∨ U = 7 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hU, hmodel⟩ := ESplit_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hU0
    rw [hU, hA]
    norm_num
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel
  have hdiv112 : d ∣ 112 := by simpa using hdiv
  have hUpos : 0 < U := lt_of_le_of_ne (ESplit_x_nonnegative h) (Ne.symm hU0)
  have hApos : 0 < A := by
    have hBq0 : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB0
    have hAq : (A : ℚ) = U * (B : ℚ) ^ 2 := by
      rw [hU]
      field_simp [hBq0]
    have : (0 : ℚ) < (A : ℚ) := by rw [hAq]; positivity
    exact_mod_cast this
  have hA : A = (d : ℤ) * (r : ℤ) ^ 2 := by
    rcases hsign with hp | hn
    · exact hp
    · rw [hn] at hApos
      have : (0 : ℤ) ≤ (d : ℤ) * (r : ℤ) ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      omega
  rcases squarefree_dvd_112 hd hdiv112 with rfl | rfl | rfl | rfl
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    simpa using rat_squareclass_of_integral hB0 hU hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 21) (b := 112) (d := 2) (e := 56)
      (by norm_num) hr0 (by norm_num) hA hmodel
    exact (no_primitive_ESplit_two_cover _ _ _
      (root_coprime_denominator hcop hA) hz).elim
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    simpa using rat_squareclass_of_integral hB0 hU hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 21) (b := 112) (d := 14) (e := 8)
      (by norm_num) hr0 (by norm_num) hA hmodel
    exact (no_primitive_ESplit_fourteen_cover _ _ _
      (root_coprime_denominator hcop hA) hz).elim

/-- The dual Kummer image consists of the classes `1` and `-7`. -/
theorem EHat_rational_x_squareclasses {X Z : ℚ}
    (h : OnEHat X Z) (hX0 : X ≠ 0) :
    ∃ q : ℚ, X = q ^ 2 ∨ X = -7 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hX, hmodel⟩ := EHat_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hX0
    rw [hX, hA]
    norm_num
  have hmodel' :
      C ^ 2 = A * (A ^ 2 + (-42) * A * B ^ 2 + (-7) * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  have hdiv7 : d ∣ 7 := by simpa using hdiv
  rcases squarefree_dvd_7 hd hdiv7 with rfl | rfl
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
      simpa using rat_squareclass_of_integral hB0 hX hA
    · have hA' : A = (-1 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA', hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -42) (b := -7) (d := -1) (e := 7)
        (by norm_num) hr0 (by norm_num) hA' hmodel'
      have hz' : z ^ 2 = -(r : ℤ) ^ 4 -
          42 * (r : ℤ) ^ 2 * B ^ 2 + 7 * B ^ 4 := by
        calc
          z ^ 2 = (-1 : ℤ) * (r : ℤ) ^ 4 +
              (-42) * (r : ℤ) ^ 2 * B ^ 2 + 7 * B ^ 4 := hz
          _ = _ := by ring
      exact (no_primitive_EHat_neg_one_cover _ _ _
        (root_coprime_denominator hcop hA') hz').elim
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA, hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -42) (b := -7) (d := 7) (e := -1)
        (by norm_num) hr0 (by norm_num) hA hmodel'
      have hz' : z ^ 2 = 7 * (r : ℤ) ^ 4 -
          42 * (r : ℤ) ^ 2 * B ^ 2 - B ^ 4 := by
        calc
          z ^ 2 = (7 : ℤ) * (r : ℤ) ^ 4 +
              (-42) * (r : ℤ) ^ 2 * B ^ 2 + (-1) * B ^ 4 := hz
          _ = _ := by ring
      exact (no_primitive_EHat_seven_cover _ _ _
        (root_coprime_denominator hcop hA) hz').elim
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
      have hA' : A = (-7 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      simpa using rat_squareclass_of_integral hB0 hX hA'

end

end MazurProof.RationalPointsX049
