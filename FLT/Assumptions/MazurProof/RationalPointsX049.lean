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
    (_hd : Squarefree d) (hdiv : d ∣ 7) : d = 1 ∨ d = 7 := by
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
  have hs : (reduce16to2 a) ^ 2 = 0 := by
    rcases h with h | h
    · calc
        (reduce16to2 a) ^ 2 = reduce16to2 (a ^ 2) := by simp
        _ = reduce16to2 0 := congrArg reduce16to2 h
        _ = 0 := by simp
    · calc
        (reduce16to2 a) ^ 2 = reduce16to2 (a ^ 2) := by simp
        _ = reduce16to2 4 := congrArg reduce16to2 h
        _ = 0 := by decide
  exact sq_eq_zero_iff.mp hs

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

private theorem no_ESplit_two_residues
    (R S T : ZMod 16)
    (hR : R = 0 ∨ R = 1 ∨ R = 4 ∨ R = 9)
    (hS : S = 0 ∨ S = 1 ∨ S = 4 ∨ S = 9)
    (hT : T = 0 ∨ T = 1 ∨ T = 4 ∨ T = 9)
    (hp : ¬ ((R = 0 ∨ R = 4) ∧ (S = 0 ∨ S = 4)))
    (h : T = 2 * R ^ 2 + 21 * R * S + 56 * S ^ 2) : False := by
  rcases hR with rfl | rfl | rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl <;>
      rcases hT with rfl | rfl | rfl | rfl
  all_goals first | exact hp ⟨by decide, by decide⟩ | (revert h; decide)

private theorem no_ESplit_fourteen_residues
    (R S T : ZMod 16)
    (hR : R = 0 ∨ R = 1 ∨ R = 4 ∨ R = 9)
    (hS : S = 0 ∨ S = 1 ∨ S = 4 ∨ S = 9)
    (hT : T = 0 ∨ T = 1 ∨ T = 4 ∨ T = 9)
    (hp : ¬ ((R = 0 ∨ R = 4) ∧ (S = 0 ∨ S = 4)))
    (h : T = 14 * R ^ 2 + 21 * R * S + 8 * S ^ 2) : False := by
  rcases hR with rfl | rfl | rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl <;>
      rcases hT with rfl | rfl | rfl | rfl
  all_goals first | exact hp ⟨by decide, by decide⟩ | (revert h; decide)

private theorem no_EHat_neg_one_residues
    (R S T : ZMod 16)
    (hR : R = 0 ∨ R = 1 ∨ R = 4 ∨ R = 9)
    (hS : S = 0 ∨ S = 1 ∨ S = 4 ∨ S = 9)
    (hT : T = 0 ∨ T = 1 ∨ T = 4 ∨ T = 9)
    (hp : ¬ ((R = 0 ∨ R = 4) ∧ (S = 0 ∨ S = 4)))
    (h : T = -(R ^ 2) - 42 * R * S + 7 * S ^ 2) : False := by
  rcases hR with rfl | rfl | rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl <;>
      rcases hT with rfl | rfl | rfl | rfl
  all_goals first | exact hp ⟨by decide, by decide⟩ | (revert h; decide)

private theorem no_EHat_seven_residues
    (R S T : ZMod 16)
    (hR : R = 0 ∨ R = 1 ∨ R = 4 ∨ R = 9)
    (hS : S = 0 ∨ S = 1 ∨ S = 4 ∨ S = 9)
    (hT : T = 0 ∨ T = 1 ∨ T = 4 ∨ T = 9)
    (hp : ¬ ((R = 0 ∨ R = 4) ∧ (S = 0 ∨ S = 4)))
    (h : T = 7 * R ^ 2 - 42 * R * S - S ^ 2) : False := by
  rcases hR with rfl | rfl | rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl <;>
      rcases hT with rfl | rfl | rfl | rfl
  all_goals first | exact hp ⟨by decide, by decide⟩ | (revert h; decide)

private theorem no_primitive_ESplit_two_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 + 21 * r ^ 2 * B ^ 2 + 56 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  let R : ZMod 16 := (r : ZMod 16) ^ 2
  let S : ZMod 16 := (B : ZMod 16) ^ 2
  let T : ZMod 16 := (z : ZMod 16) ^ 2
  apply no_ESplit_two_residues R S T
  · simpa [R] using zmod16_sq_cases (r : ZMod 16)
  · simpa [S] using zmod16_sq_cases (B : ZMod 16)
  · simpa [T] using zmod16_sq_cases (z : ZMod 16)
  · simpa [R, S] using primitive_sq_residues hcop
  · dsimp [R, S, T]
    calc
      (z : ZMod 16) ^ 2 = 2 * (r : ZMod 16) ^ 4 +
          21 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          56 * (B : ZMod 16) ^ 4 := hm
      _ = 2 * ((r : ZMod 16) ^ 2) ^ 2 +
          21 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          56 * ((B : ZMod 16) ^ 2) ^ 2 := by ring

private theorem no_primitive_ESplit_fourteen_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 14 * r ^ 4 + 21 * r ^ 2 * B ^ 2 + 8 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  let R : ZMod 16 := (r : ZMod 16) ^ 2
  let S : ZMod 16 := (B : ZMod 16) ^ 2
  let T : ZMod 16 := (z : ZMod 16) ^ 2
  apply no_ESplit_fourteen_residues R S T
  · simpa [R] using zmod16_sq_cases (r : ZMod 16)
  · simpa [S] using zmod16_sq_cases (B : ZMod 16)
  · simpa [T] using zmod16_sq_cases (z : ZMod 16)
  · simpa [R, S] using primitive_sq_residues hcop
  · dsimp [R, S, T]
    calc
      (z : ZMod 16) ^ 2 = 14 * (r : ZMod 16) ^ 4 +
          21 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          8 * (B : ZMod 16) ^ 4 := hm
      _ = 14 * ((r : ZMod 16) ^ 2) ^ 2 +
          21 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          8 * ((B : ZMod 16) ^ 2) ^ 2 := by ring

private theorem no_primitive_EHat_neg_one_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -(r ^ 4) - 42 * r ^ 2 * B ^ 2 + 7 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  let R : ZMod 16 := (r : ZMod 16) ^ 2
  let S : ZMod 16 := (B : ZMod 16) ^ 2
  let T : ZMod 16 := (z : ZMod 16) ^ 2
  apply no_EHat_neg_one_residues R S T
  · simpa [R] using zmod16_sq_cases (r : ZMod 16)
  · simpa [S] using zmod16_sq_cases (B : ZMod 16)
  · simpa [T] using zmod16_sq_cases (z : ZMod 16)
  · simpa [R, S] using primitive_sq_residues hcop
  · dsimp [R, S, T]
    calc
      (z : ZMod 16) ^ 2 = -(r : ZMod 16) ^ 4 -
          42 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          7 * (B : ZMod 16) ^ 4 := hm
      _ = -(((r : ZMod 16) ^ 2) ^ 2) -
          42 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 +
          7 * ((B : ZMod 16) ^ 2) ^ 2 := by ring

private theorem no_primitive_EHat_seven_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 7 * r ^ 4 - 42 * r ^ 2 * B ^ 2 - B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  let R : ZMod 16 := (r : ZMod 16) ^ 2
  let S : ZMod 16 := (B : ZMod 16) ^ 2
  let T : ZMod 16 := (z : ZMod 16) ^ 2
  apply no_EHat_seven_residues R S T
  · simpa [R] using zmod16_sq_cases (r : ZMod 16)
  · simpa [S] using zmod16_sq_cases (B : ZMod 16)
  · simpa [T] using zmod16_sq_cases (z : ZMod 16)
  · simpa [R, S] using primitive_sq_residues hcop
  · dsimp [R, S, T]
    calc
      (z : ZMod 16) ^ 2 = 7 * (r : ZMod 16) ^ 4 -
          42 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 -
          (B : ZMod 16) ^ 4 := hm
      _ = 7 * ((r : ZMod 16) ^ 2) ^ 2 -
          42 * (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 -
          ((B : ZMod 16) ^ 2) ^ 2 := by ring

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

/-! ## The weak two-descent -/

private def ESplitPointOf (U V : ℚ) (h : OnESplit U V) : ESplitPoint :=
  WeierstrassCurve.Affine.Point.some U V
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((ESplitCurve_equation_iff U V).mpr h))

private def EHatPointOf (X Z : ℚ) (h : OnEHat X Z) : EHatPoint :=
  WeierstrassCurve.Affine.Point.some X Z
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((EHatCurve_equation_iff X Z).mpr h))

private def ESplitKernel : ESplitPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((ESplitCurve_equation_iff 0 0).mpr (by norm_num [OnESplit]))

private def EHatKernel : EHatPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((EHatCurve_equation_iff 0 0).mpr (by norm_num [OnEHat]))

private theorem ESplitKernel_nonsingular :
    WeierstrassCurve.Affine.Nonsingular ESplitCurve 0 0 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((ESplitCurve_equation_iff 0 0).mpr (by norm_num [OnESplit]))

private theorem EHatKernel_nonsingular :
    WeierstrassCurve.Affine.Nonsingular EHatCurve 0 0 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((EHatCurve_equation_iff 0 0).mpr (by norm_num [OnEHat]))

@[simp] private theorem phiPoint_ESplitKernel : phiPoint ESplitKernel = 0 := by
  rfl

@[simp] private theorem dualPoint_EHatKernel : dualPoint EHatKernel = 0 := by
  rfl

private theorem ESplitKernel_two : 2 • ESplitKernel = 0 :=
  ESplit_double_eq_zero_of_y_zero _ rfl

private theorem EHatKernel_two : 2 • EHatKernel = 0 :=
  EHat_double_eq_zero_of_y_zero _ rfl

private theorem ESplit_slope_kernel {U V : ℚ} (hU : U ≠ 0) :
    WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0 = V / U := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hU]
  ring

private theorem EHat_slope_kernel {X Z : ℚ} (hX : X ≠ 0) :
    WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0 = Z / X := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hX]
  ring

private theorem ESplit_add_kernel_x {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V) (hU : U ≠ 0) :
    WeierstrassCurve.Affine.addX ESplitCurve U 0
        (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0) = 112 / U := by
  rw [ESplit_slope_kernel hU]
  have heq := (ESplitCurve_equation_iff U V).mp h.1
  unfold OnESplit at heq
  unfold WeierstrassCurve.Affine.addX ESplitCurve
  field_simp [hU]
  linear_combination heq

private theorem ESplit_add_kernel_y {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V) (hU : U ≠ 0) :
    WeierstrassCurve.Affine.addY ESplitCurve U 0 V
        (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0) =
      -(112 * V / U ^ 2) := by
  rw [ESplit_slope_kernel hU]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY
  have hX : WeierstrassCurve.Affine.addX ESplitCurve U 0 (V / U) = 112 / U := by
    rw [← ESplit_slope_kernel hU]
    exact ESplit_add_kernel_x h hU
  rw [hX]
  simp [ESplitCurve]
  field_simp [hU]
  ring

private theorem EHat_add_kernel_x {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z) (hX : X ≠ 0) :
    WeierstrassCurve.Affine.addX EHatCurve X 0
        (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) = -7 / X := by
  rw [EHat_slope_kernel hX]
  have heq := (EHatCurve_equation_iff X Z).mp h.1
  unfold OnEHat at heq
  unfold WeierstrassCurve.Affine.addX EHatCurve
  field_simp [hX]
  linear_combination heq

private theorem EHat_add_kernel_y {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z) (hX : X ≠ 0) :
    WeierstrassCurve.Affine.addY EHatCurve X 0 Z
        (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) =
      7 * Z / X ^ 2 := by
  rw [EHat_slope_kernel hX]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY
  have hX' : WeierstrassCurve.Affine.addX EHatCurve X 0 (Z / X) = -7 / X := by
    rw [← EHat_slope_kernel hX]
    exact EHat_add_kernel_x h hX
  rw [hX']
  simp [EHatCurve]
  field_simp [hX]
  ring

private theorem phi_translation_coordinates {U V : ℚ} (hU : U ≠ 0) :
    phiX (112 / U) (-(112 * V / U ^ 2)) = phiX U V ∧
      phiY (112 / U) (-(112 * V / U ^ 2)) = phiY U V := by
  constructor
  · unfold phiX
    field_simp [hU]
  · unfold phiY
    field_simp [hU]
    ring

private theorem dual_translation_coordinates {X Z : ℚ} (hX : X ≠ 0) :
    dualX (-7 / X) (7 * Z / X ^ 2) = dualX X Z ∧
      dualY (-7 / X) (7 * Z / X ^ 2) = dualY X Z := by
  constructor
  · unfold dualX
    field_simp [hX]
  · unfold dualY
    field_simp [hX]
    ring

private theorem phiPoint_add_kernel (P : ESplitPoint) :
    phiPoint (P + ESplitKernel) = phiPoint P := by
  cases P with
  | zero =>
      change phiPoint ESplitKernel = phiPoint 0
      rw [phiPoint_ESplitKernel, phiPoint_zero]
  | some U V h =>
      by_cases hU : U = 0
      · have hV := ESplit_y_zero_of_x_zero h hU
        subst U
        subst V
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : ESplitPoint) =
            ESplitKernel by rfl]
        rw [← two_nsmul, ESplitKernel_two]
        rw [phiPoint_zero, phiPoint_ESplitKernel]
      · change phiPoint
            ((WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hU]
        have hax : WeierstrassCurve.Affine.addX ESplitCurve U 0
            (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0) ≠ 0 := by
          rw [ESplit_add_kernel_x h hU]
          exact div_ne_zero (by norm_num) hU
        rw [phiPoint_some_of_x_ne_zero _ hax,
          phiPoint_some_of_x_ne_zero h hU]
        change WeierstrassCurve.Affine.Point.some
            (phiX
              (WeierstrassCurve.Affine.addX ESplitCurve U 0
                (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0))
              (WeierstrassCurve.Affine.addY ESplitCurve U 0 V
                (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0)))
            (phiY
              (WeierstrassCurve.Affine.addX ESplitCurve U 0
                (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0))
              (WeierstrassCurve.Affine.addY ESplitCurve U 0 V
                (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0))) _ =
          WeierstrassCurve.Affine.Point.some (phiX U V) (phiY U V) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := phi_translation_coordinates (U := U) (V := V) hU
        constructor
        · rw [ESplit_add_kernel_x h hU, ESplit_add_kernel_y h hU]
          exact hc.1
        · rw [ESplit_add_kernel_x h hU, ESplit_add_kernel_y h hU]
          exact hc.2

private theorem dualPoint_add_kernel (P : EHatPoint) :
    dualPoint (P + EHatKernel) = dualPoint P := by
  cases P with
  | zero =>
      change dualPoint EHatKernel = dualPoint 0
      rw [dualPoint_EHatKernel, dualPoint_zero]
  | some X Z h =>
      by_cases hX : X = 0
      · have hZ := EHat_y_zero_of_x_zero h hX
        subst X
        subst Z
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : EHatPoint) =
            EHatKernel by rfl]
        rw [← two_nsmul, EHatKernel_two]
        rw [dualPoint_zero, dualPoint_EHatKernel]
      · change dualPoint
            ((WeierstrassCurve.Affine.Point.some X Z h : EHatPoint) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX]
        have hax : WeierstrassCurve.Affine.addX EHatCurve X 0
            (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) ≠ 0 := by
          rw [EHat_add_kernel_x h hX]
          exact div_ne_zero (by norm_num) hX
        rw [dualPoint_some_of_x_ne_zero _ hax,
          dualPoint_some_of_x_ne_zero h hX]
        change WeierstrassCurve.Affine.Point.some
            (dualX
              (WeierstrassCurve.Affine.addX EHatCurve X 0
                (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0))
              (WeierstrassCurve.Affine.addY EHatCurve X 0 Z
                (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0)))
            (dualY
              (WeierstrassCurve.Affine.addX EHatCurve X 0
                (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0))
              (WeierstrassCurve.Affine.addY EHatCurve X 0 Z
                (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0))) _ =
          WeierstrassCurve.Affine.Point.some (dualX X Z) (dualY X Z) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := dual_translation_coordinates (X := X) (Z := Z) hX
        constructor
        · rw [EHat_add_kernel_x h hX, EHat_add_kernel_y h hX]
          exact hc.1
        · rw [EHat_add_kernel_x h hX, EHat_add_kernel_y h hX]
          exact hc.2

private theorem ESplit_exists_half_of_square_x {U V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular ESplitCurve U V)
    (hU : U ≠ 0) (hsq : ∃ q : ℚ, U = q ^ 2) :
    ∃ Q : ESplitPoint,
      2 • Q = WeierstrassCurve.Affine.Point.some U V h := by
  obtain ⟨q, hq⟩ := hsq
  obtain ⟨S, hS⟩ := exists_dualPoint_preimage_of_x_eq_sq h hU hq
  cases S with
  | zero =>
      change dualPoint (0 : EHatPoint) = _ at hS
      rw [dualPoint_zero] at hS
      cases hS
  | some X Z hXZ =>
      by_cases hX : X = 0
      · rw [dualPoint_some_of_x_eq_zero hXZ hX] at hS
        cases hS
      · have heq : OnEHat X Z := (EHatCurve_equation_iff X Z).mp hXZ.1
        obtain ⟨r, hr | hr⟩ := EHat_rational_x_squareclasses heq hX
        · obtain ⟨Q, hQ⟩ := exists_phiPoint_preimage_of_x_eq_sq hXZ hX hr
          refine ⟨Q, ?_⟩
          rw [← dual_comp_phiPoint Q, hQ, hS]
        · have hr0 : r ≠ 0 := by
            intro hr0
            apply hX
            rw [hr, hr0]
            norm_num
          let X' := WeierstrassCurve.Affine.addX EHatCurve X 0
            (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0)
          let Z' := WeierstrassCurve.Affine.addY EHatCurve X 0 Z
            (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0)
          have hXZ' : WeierstrassCurve.Affine.Nonsingular EHatCurve X' Z' :=
            WeierstrassCurve.Affine.nonsingular_add hXZ EHatKernel_nonsingular
              (fun hbad => hX hbad.1)
          have hX'sq : X' = (1 / r) ^ 2 := by
            change WeierstrassCurve.Affine.addX EHatCurve X 0
              (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) = _
            rw [EHat_add_kernel_x hXZ hX, hr]
            field_simp [hr0]
          have hX'0 : X' ≠ 0 := by rw [hX'sq]; positivity
          have hSplus :
              (WeierstrassCurve.Affine.Point.some X Z hXZ : EHatPoint) +
                  EHatKernel =
                WeierstrassCurve.Affine.Point.some X' Z' hXZ' := by
            change (WeierstrassCurve.Affine.Point.some X Z hXZ : EHatPoint) +
                WeierstrassCurve.Affine.Point.some 0 0 _ = _
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hX
          obtain ⟨Q, hQ⟩ :=
            exists_phiPoint_preimage_of_x_eq_sq hXZ' hX'0 hX'sq
          refine ⟨Q, ?_⟩
          rw [← dual_comp_phiPoint Q, hQ, ← hSplus,
            dualPoint_add_kernel, hS]

/-- Every point on the split model is a two-torsion point plus twice
another rational point. -/
theorem ESplit_two_descent_step (P : ESplitPoint) :
    ∃ T Q : ESplitPoint, 2 • T = 0 ∧ P = T + 2 • Q := by
  cases P with
  | zero => exact ⟨0, 0, by simp, rfl⟩
  | some U V h =>
      by_cases hU : U = 0
      · have hV : V = 0 := ESplit_y_zero_of_x_zero h hU
        refine ⟨WeierstrassCurve.Affine.Point.some U V h, 0,
          ESplit_double_eq_zero_of_y_zero h hV, by simp⟩
      · have heq : OnESplit U V := (ESplitCurve_equation_iff U V).mp h.1
        obtain ⟨q, hq | hq⟩ := ESplit_rational_x_squareclasses heq hU
        · obtain ⟨Q, hQ⟩ := ESplit_exists_half_of_square_x h hU ⟨q, hq⟩
          exact ⟨0, Q, by simp, by simpa using hQ.symm⟩
        · have hq0 : q ≠ 0 := by
            intro hq0
            apply hU
            rw [hq, hq0]
            norm_num
          let U' := WeierstrassCurve.Affine.addX ESplitCurve U 0
            (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0)
          let V' := WeierstrassCurve.Affine.addY ESplitCurve U 0 V
            (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0)
          have hUV' : WeierstrassCurve.Affine.Nonsingular ESplitCurve U' V' :=
            WeierstrassCurve.Affine.nonsingular_add h ESplitKernel_nonsingular
              (fun hbad => hU hbad.1)
          have hU'sq : U' = (4 / q) ^ 2 := by
            change WeierstrassCurve.Affine.addX ESplitCurve U 0
              (WeierstrassCurve.Affine.slope ESplitCurve U 0 V 0) = _
            rw [ESplit_add_kernel_x h hU, hq]
            field_simp [hq0]
            norm_num
          have hU'0 : U' ≠ 0 := by rw [hU'sq]; positivity
          have hPplus :
              (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
                  ESplitKernel =
                WeierstrassCurve.Affine.Point.some U' V' hUV' := by
            change (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
                WeierstrassCurve.Affine.Point.some 0 0 _ = _
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hU
          obtain ⟨Q, hQ⟩ :=
            ESplit_exists_half_of_square_x hUV' hU'0 ⟨_, hU'sq⟩
          refine ⟨ESplitKernel, Q, ESplitKernel_two, ?_⟩
          have hQ' : 2 • Q =
              (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
                ESplitKernel := by rw [hQ, ← hPplus]
          rw [hQ']
          calc
            (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) =
                (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) + 0 := by simp
            _ = (WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
                (ESplitKernel + ESplitKernel) := by
                  rw [← two_nsmul, ESplitKernel_two]
            _ = ESplitKernel +
                ((WeierstrassCurve.Affine.Point.some U V h : ESplitPoint) +
                  ESplitKernel) := by abel

/-- Iterating weak descent makes twice every rational point divisible by
every power of two. -/
theorem ESplit_two_nsmul_two_power_divisible (P : ESplitPoint) (n : ℕ) :
    ∃ Q : ESplitPoint, 2 • P = (2 ^ n : ℕ) • (2 • Q) := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨T, R, hT, hdecomp⟩ := ESplit_two_descent_step Q
      refine ⟨R, ?_⟩
      rw [hQ, hdecomp, nsmul_add, hT, zero_add]
      simp only [← mul_nsmul]
      congr 1
      omega

/-! ### Integral good-reduction model at two -/

open Scratch.TateZ2xZ10Reduction

def E49toSplitChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 2
  s := -1 / 2
  t := -1

theorem E49toSplitChange_curve : E49toSplitChange • E49Curve = ESplitCurve := by
  ext <;>
    simp [E49toSplitChange, E49Curve, ESplitCurve,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;>
    norm_num

private noncomputable def curveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
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

noncomputable def E49SplitAddEquiv : E49Point ≃+ ESplitPoint :=
  (variableChangePointAddEquiv E49Curve E49toSplitChange).trans
    (curveEqAddEquiv E49toSplitChange_curve)

theorem E49SplitAddEquiv_some
    {x y : ℚ} {h0 : WeierstrassCurve.Affine.Nonsingular E49Curve x y}
    {h1 : WeierstrassCurve.Affine.Nonsingular ESplitCurve
      (4 * (x - 2)) (4 * (2 * y + x))} :
    E49SplitAddEquiv (WeierstrassCurve.Affine.Point.some x y h0) =
      WeierstrassCurve.Affine.Point.some
        (4 * (x - 2)) (4 * (2 * y + x)) h1 := by
  change (curveEqAddEquiv E49toSplitChange_curve)
      (variableChangePointMap E49Curve E49toSplitChange
        (WeierstrassCurve.Affine.Point.some x y h0)) = _
  change (curveEqAddEquiv E49toSplitChange_curve)
      (WeierstrassCurve.Affine.Point.some
        (variableChangePointX E49toSplitChange x)
        (variableChangePointY E49toSplitChange x y) _) = _
  have hx : variableChangePointX E49toSplitChange x = 4 * (x - 2) := by
    norm_num [variableChangePointX, E49toSplitChange]
  have hy : variableChangePointY E49toSplitChange x y =
      4 * (2 * y + x) := by
    norm_num [variableChangePointY, E49toSplitChange]
    ring
  have hvar0 : WeierstrassCurve.Affine.Nonsingular
      (E49toSplitChange • E49Curve)
      (variableChangePointX E49toSplitChange x)
      (variableChangePointY E49toSplitChange x y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (variableChangePoint_equation E49Curve E49toSplitChange h0.1)
  have hvar : WeierstrassCurve.Affine.Nonsingular ESplitCurve
      (variableChangePointX E49toSplitChange x)
      (variableChangePointY E49toSplitChange x y) := by
    rw [← E49toSplitChange_curve]
    exact hvar0
  calc
    (curveEqAddEquiv E49toSplitChange_curve)
        (WeierstrassCurve.Affine.Point.some
          (variableChangePointX E49toSplitChange x)
          (variableChangePointY E49toSplitChange x y) _) =
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX E49toSplitChange x)
        (variableChangePointY E49toSplitChange x y) hvar :=
      curveEqAddEquiv_some E49toSplitChange_curve
    _ = WeierstrassCurve.Affine.Point.some
        (4 * (x - 2)) (4 * (2 * y + x)) h1 := by
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩

/-! ## Two-adic separatedness on the good model -/

private theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 2 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.ofNat_zero_le _

private theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by linarith
    have : padicValRat 2 b = padicValRat 2 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

private theorem val_const_mul_ge {a : ℚ} (z : ℤ) (hz : z ≠ 0) (ha : a ≠ 0) :
    padicValRat 2 a ≤ padicValRat 2 ((z : ℚ) * a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hz) ha]
  have hzval := val_int_nonneg z
  omega

private theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    l.sum = 0 ∨ padicValRat 2 q < padicValRat 2 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 2 q < padicValRat 2 a := hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 2 q < padicValRat 2 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

private theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    padicValRat 2 (q + l.sum) = padicValRat 2 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 2 q) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

private theorem zmod2_nonzero_eq_one (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

def E49DoubleDen (x y : ℚ) : ℚ := 2 * y + x

def E49DoubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + 4 * x ^ 2 + 8 * x + 1

def E49DoubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 10 * x ^ 4 - 22 * x ^ 3 -
    4 * x ^ 2 * y - 9 * x ^ 2 - 8 * x * y - 7 * x - y - 6

private theorem E49_doubleX_formula {x y : ℚ}
    (hd : E49DoubleDen x y ≠ 0) (hE : OnE49 x y) :
    WeierstrassCurve.Affine.addX E49Curve x x
        (WeierstrassCurve.Affine.slope E49Curve x x y y) =
      E49DoubleXNum x / E49DoubleDen x y ^ 2 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E49Curve x y := by
    intro h
    apply hd
    simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E49Curve x x y y =
      (3 * x ^ 2 - 2 * x - y - 2) / E49DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E49Curve, E49DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addX E49DoubleXNum
  simp only [E49Curve]
  unfold OnE49 at hE
  field_simp [hd]
  unfold E49DoubleDen
  linear_combination (3 - 8 * x) * hE

private theorem E49_doubleY_formula {x y : ℚ}
    (hd : E49DoubleDen x y ≠ 0) (hE : OnE49 x y) :
    WeierstrassCurve.Affine.addY E49Curve x x y
        (WeierstrassCurve.Affine.slope E49Curve x x y y) =
      E49DoubleYNum x y / E49DoubleDen x y ^ 3 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E49Curve x y := by
    intro h
    apply hd
    simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E49Curve x x y y =
      (3 * x ^ 2 - 2 * x - y - 2) / E49DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E49Curve, E49DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E49DoubleYNum
  simp [E49Curve]
  unfold OnE49 at hE
  field_simp [hd]
  unfold E49DoubleDen
  linear_combination
    (28 * x ^ 3 - 19 * x ^ 2 - 5 * x - 8 * y ^ 2 - 3 * y + 14) * hE

private theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 2 x + (b : ℤ) * padicValRat 2 y ≤
      padicValRat 2 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow hx, padicValRat.pow hy]
  have hcval := val_int_nonneg c
  omega

private theorem E49DoubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (E49DoubleXNum x) = -8 * k := by
  have hshape : E49DoubleXNum x =
      x ^ 4 + [4 * x ^ 2, 8 * x, (1 : ℚ)].sum := by
    simp [E49DoubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hge := val_monomial_ge hx hy 4 (by norm_num) 2 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 8 (by norm_num) 1 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · rw [padicValRat.pow hx, hvx, padicValRat.one]
      omega

private theorem E49DoubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (E49DoubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [(-2 : ℚ) * x ^ 5, (-1 : ℚ) * x ^ 4 * y, -10 * x ^ 4,
      -22 * x ^ 3, -4 * x ^ 2 * y, -9 * x ^ 2,
      -8 * x * y, -7 * x, (-1 : ℚ) * y, (-6 : ℚ)]
  have hshape : E49DoubleYNum x y = x ^ 6 + l.sum := by
    simp [E49DoubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow hx, hvx]
    · have hge := val_monomial_ge hx hy (-2) (by norm_num) 5 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-10) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-22) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-4) (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-9) (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-8) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-7) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-6)
      norm_num at hge ⊢
      omega

/-- A point is in the formal kernel at `2` when its affine coordinates have
valuations `(-2k,-3k)` for some `k>0`. -/
def E49FormalAtTwo : E49Point → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

def E49FormalLevel : E49Point → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

theorem E49FormalAtTwo_iff (P : E49Point) :
    E49FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, E49FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [E49FormalAtTwo, E49FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

theorem E49FormalLevel_double {P : E49Point} {k : ℤ}
    (hP : E49FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ E49FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [E49FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      by_cases hd : E49DoubleDen x y = 0
      · left
        rw [two_nsmul]
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvdenLower : 1 - 3 * k ≤ padicValRat 2 (E49DoubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y) (r := x) (by simpa [E49DoubleDen] using hd)
          rw [hv2y, hvx, min_eq_left (by omega)] at hmin
          simpa [E49DoubleDen] using hmin
        let k' : ℤ := 4 * k + padicValRat 2 (E49DoubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := E49DoubleXNum_val hx hy hk hvx
        have hvY := E49DoubleYNum_val hx hy hk hvx hvy
        have hN : E49DoubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : E49DoubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE : OnE49 x y := (E49Curve_equation_iff x y).mp h.1
        have hxform := E49_doubleX_formula hd hE
        have hyform := E49_doubleY_formula hd hE
        have hvx2 : padicValRat 2
              (WeierstrassCurve.Affine.addX E49Curve x x
                (WeierstrassCurve.Affine.slope E49Curve x x y y)) =
            -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow hd]
          dsimp [k']
          ring
        have hvy2 : padicValRat 2
              (WeierstrassCurve.Affine.addY E49Curve x x y
                (WeierstrassCurve.Affine.slope E49Curve x x y y)) =
            -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ WeierstrassCurve.Affine.negY E49Curve x y := by
          intro heq
          apply hd
          simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at heq ⊢
          linarith
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- At the good prime `2`, a rational point is integral or lies in the
formal kernel. -/
theorem E49_formal_or_integral (P : E49Point) :
    E49FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE : OnE49 x y := (E49Curve_equation_iff x y).mp h.1
      let vx := padicValRat 2 x
      let vy := padicValRat 2 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [x * y, -(x ^ 3), x ^ 2, 2 * x, (1 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnE49 at hE
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · rw [hx0, zero_mul, padicValRat.zero, hlead]
              omega
            · rw [padicValRat.mul hx0 hy, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 3 ≠ 0), neg_zero,
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 2 ≠ 0),
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, mul_zero, padicValRat.zero, hlead]
              omega
            · have hge := val_const_mul_ge 2 (by norm_num) hx0
              rw [hlead]
              dsimp [vx] at hxint hge ⊢
              omega
          · rw [padicValRat.one, hlead]
            omega
        have hval := val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, x * y, x ^ 2, 2 * x, (1 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnE49 at hE
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · rw [hy0, zero_pow (by norm_num : 2 ≠ 0),
                  padicValRat.zero, hlead]
                omega
              · rw [padicValRat.pow hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · by_cases hy0 : y = 0
              · rw [hy0, mul_zero, padicValRat.zero, hlead]
                omega
              · rw [padicValRat.mul hx hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · rw [padicValRat.pow hx, hlead]
              dsimp [vx] at hvxneg ⊢
              omega
            · have hge := val_const_mul_ge 2 (by norm_num) hx
              rw [hlead]
              dsimp [vx] at hvxneg hge ⊢
              omega
            · rw [padicValRat.one, hlead]
              omega
          have hval := val_add_list_eq l (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        have hleftne : y ^ 2 + x * y ≠ 0 := by
          intro hz
          have hvals : padicValRat 2 (y ^ 2) < padicValRat 2 (x * y) := by
            rw [padicValRat.pow hy, padicValRat.mul hx hy]
            dsimp [vx, vy] at hvylt ⊢
            omega
          have hv := val_add_eq_left_of_lt (pow_ne_zero 2 hy) hvals
          rw [hz, padicValRat.zero, padicValRat.pow hy] at hv
          dsimp [vy] at hvylt hv
          omega
        have hvleft : padicValRat 2 (y ^ 2 + x * y) = 2 * vy := by
          have hvals : padicValRat 2 (y ^ 2) < padicValRat 2 (x * y) := by
            rw [padicValRat.pow hy, padicValRat.mul hx hy]
            dsimp [vx, vy] at hvylt ⊢
            omega
          rw [val_add_eq_left_of_lt (pow_ne_zero 2 hy) hvals,
            padicValRat.pow hy]
          rfl
        let l : List ℚ := [-(x ^ 2), -2 * x, (-1 : ℚ)]
        have hrightshape : x ^ 3 + l.sum = x ^ 3 - x ^ 2 - 2 * x - 1 := by
          simp [l]
          ring
        have hrightgt : ∀ a ∈ l,
            padicValRat 2 (x ^ 3) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · rw [padicValRat.pow hx, padicValRat.neg,
              padicValRat.pow hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · have hge := val_const_mul_ge (-2) (by norm_num) hx
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · rw [padicValRat.pow hx, padicValRat.neg, padicValRat.one]
            dsimp [vx] at hvxneg ⊢
            omega
        have hvright0 := val_add_list_eq l (pow_ne_zero 3 hx) hrightgt
        have hvright : padicValRat 2 (x ^ 3 - x ^ 2 - 2 * x - 1) =
            3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 - x ^ 2 - 2 * x - 1) := by rw [hE]
            _ = 3 * vx := hvright
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

private theorem ratPadicInt_red_eq_one_of_val_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    PadicInt.toZMod (ratPadicInt q (by omega)) = 1 := by
  apply zmod2_nonzero_eq_one
  intro hz0
  have hm : ratPadicInt q (by omega) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hz0
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖((ratPadicInt q (by omega) : ℤ_[2]) : ℚ_[2])‖ < 1 at hm
  change ‖(q : ℚ_[2])‖ < 1 at hm
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv] at hm
  norm_num at hm

private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 2 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[2])‖ < 1
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
    (by norm_num : (1 : ℝ) < 2)).2 (by omega)

private theorem val_pos_of_rational_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 2 q := by
  by_contra hnot
  have hv0 : padicValRat 2 q = 0 := by omega
  have hone := ratPadicInt_red_eq_one_of_val_zero hq hv0
  have heq : ratPadicInt q hqi = ratPadicInt q (by omega) := by
    apply Subtype.ext
    rfl
  rw [heq, hone] at hred
  norm_num at hred

private theorem val_zero_of_rational_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 2 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 2 q := lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi = ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

private noncomputable def E49DoubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + 4 * x ^ 2 + 8 * x + 1

private noncomputable def E49DoubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 10 * x ^ 4 - 22 * x ^ 3 -
    4 * x ^ 2 * y - 9 * x ^ 2 - 8 * x * y - 7 * x - y - 6

private theorem E49DoubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((E49DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((E49DoubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + 4 * (x : ℚ_[2]) ^ 2 +
      8 * (x : ℚ_[2]) + 1 =
    (((x ^ 4 + 4 * x ^ 2 + 8 * x + 1 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E49DoubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((E49DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((E49DoubleYNum x y : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 6 - 2 * (x : ℚ_[2]) ^ 5 -
      (x : ℚ_[2]) ^ 4 * (y : ℚ_[2]) - 10 * (x : ℚ_[2]) ^ 4 -
      22 * (x : ℚ_[2]) ^ 3 - 4 * (x : ℚ_[2]) ^ 2 * (y : ℚ_[2]) -
      9 * (x : ℚ_[2]) ^ 2 - 8 * (x : ℚ_[2]) * (y : ℚ_[2]) -
      7 * (x : ℚ_[2]) - (y : ℚ_[2]) - 6 =
    (((x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 10 * x ^ 4 - 22 * x ^ 3 -
      4 * x ^ 2 * y - 9 * x ^ 2 - 8 * x * y - 7 * x - y - 6 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E49DoubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (E49DoubleXNum x) := by
  have hnorm := (E49DoubleXNumPadic (ratPadicInt x hx)).2
  change ‖((E49DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E49DoubleXNumPadic_coe x hx,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E49DoubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (E49DoubleYNum x y) := by
  have hnorm := (E49DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((E49DoubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E49DoubleYNumPadic_coe x y hx hy,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E49_padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE49 x y) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 - (ratPadicInt x hx) ^ 2 -
        2 * ratPadicInt x hx - 1 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 - (x : ℚ_[2]) ^ 2 - 2 * (x : ℚ_[2]) - 1
  unfold OnE49 at hE
  exact_mod_cast hE

private theorem E49_mod2_coordinates (X Y : ZMod 2)
    (h : Y ^ 2 + X * Y = X ^ 3 - X - 1) :
    X = 0 ∧ Y = 1 := by
  by_cases hX : X = 0
  · subst X
    by_cases hY : Y = 0
    · subst Y
      exfalso
      have hz : (0 : ZMod 2) = 1 := by
        calc
          (0 : ZMod 2) = -1 := by simpa using h
          _ = 1 := by decide
      exact zero_ne_one hz
    · have hY1 := zmod2_nonzero_eq_one Y hY
      exact ⟨rfl, hY1⟩
  · have hX1 := zmod2_nonzero_eq_one X hX
    subst X
    by_cases hY : Y = 0
    · subst Y
      exfalso
      have hz : (0 : ZMod 2) = 1 := by
        calc
          (0 : ZMod 2) = -1 := by simpa using h
          _ = 1 := by decide
      exact zero_ne_one hz
    · have hY1 := zmod2_nonzero_eq_one Y hY
      subst Y
      exfalso
      have hz : (0 : ZMod 2) = 1 := by
        calc
          (0 : ZMod 2) = -1 := by
            simpa [show (2 : ZMod 2) = 0 by decide] using h
          _ = 1 := by decide
      exact zero_ne_one hz

@[simp] private theorem toZMod_2 :
    PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_6 :
    PadicInt.toZMod (6 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

private theorem E49_integral_red_coordinates {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE49 x y) :
    PadicInt.toZMod (ratPadicInt x hx) = 0 ∧
      PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (E49_padicInt_equation hx hy hE)
  apply E49_mod2_coordinates
  simpa [map_add, map_sub, map_mul, map_pow] using heq

private theorem E49DoubleXNumPadic_red_zero
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E49DoubleXNumPadic z) = 1 := by
  simp [E49DoubleXNumPadic, map_add, map_mul, map_pow, hz]

private theorem E49DoubleYNumPadic_red_zero_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (E49DoubleYNumPadic z w) = 1 := by
  simp [E49DoubleYNumPadic, map_sub, map_mul, map_pow, hz, hw]

private theorem ratPadicInt_E49DoubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (E49DoubleXNum x) (E49DoubleXNum_integral x hx) =
      E49DoubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (E49DoubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_E49DoubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x)
    (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (E49DoubleYNum x y) (E49DoubleYNum_integral x y hx hy) =
      E49DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (E49DoubleYNumPadic_coe x y hx hy).symm

private theorem val_two : padicValRat 2 (2 : ℚ) = 1 :=
  padicValRat.self (by norm_num : 1 < 2)

private theorem E49_double_formal_of_integral
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E49Curve x y}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    E49FormalAtTwo
      (2 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hE : OnE49 x y := (E49Curve_equation_iff x y).mp h.1
  have hxn : x ≠ 0 := by
    intro hzero
    rw [hzero] at hE
    norm_num [OnE49] at hE
    nlinarith [sq_nonneg y]
  obtain ⟨hxred, hyred⟩ := E49_integral_red_coordinates hx hy hE
  have hyn : y ≠ 0 := by
    intro hzero
    have : ratPadicInt y hy = 0 := by
      apply Subtype.ext
      change (y : ℚ_[2]) = 0
      simp [hzero]
    rw [this, map_zero] at hyred
    norm_num at hyred
  have hvx : 0 < padicValRat 2 x :=
    val_pos_of_rational_padicInt_red_zero hxn hx hxred
  have hvy : padicValRat 2 y = 0 := by
    apply val_zero_of_rational_padicInt_red_nonzero hyn hy
    rw [hyred]
    norm_num
  by_cases hd : E49DoubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = WeierstrassCurve.Affine.negY E49Curve x y := by
      simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at hd ⊢
      linarith
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hYeq]
    trivial
  · have hv2y : padicValRat 2 (2 * y) = 1 := by
      rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn,
        val_two, hvy]
      norm_num
    have hvd : 1 ≤ padicValRat 2 (E49DoubleDen x y) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := 2)
        (q := 2 * y) (r := x) (by simpa [E49DoubleDen] using hd)
      rw [hv2y, min_eq_left (by omega)] at hmin
      simpa [E49DoubleDen] using hmin
    have hNi := E49DoubleXNum_integral x hx
    have hYi := E49DoubleYNum_integral x y hx hy
    have hNred : PadicInt.toZMod
        (ratPadicInt (E49DoubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_E49DoubleXNum x hx]
      exact E49DoubleXNumPadic_red_zero hxred
    have hYred : PadicInt.toZMod
        (ratPadicInt (E49DoubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_E49DoubleYNum x y hx hy]
      exact E49DoubleYNumPadic_red_zero_one hxred hyred
    have hN : E49DoubleXNum x ≠ 0 := by
      intro hzero
      have : ratPadicInt (E49DoubleXNum x) hNi = 0 := by
        apply Subtype.ext
        change ((E49DoubleXNum x : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hNred
      norm_num at hNred
    have hY : E49DoubleYNum x y ≠ 0 := by
      intro hzero
      have : ratPadicInt (E49DoubleYNum x y) hYi = 0 := by
        apply Subtype.ext
        change ((E49DoubleYNum x y : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hYred
      norm_num at hYred
    have hvN : padicValRat 2 (E49DoubleXNum x) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hN hNi (by
        rw [hNred]
        norm_num)
    have hvY : padicValRat 2 (E49DoubleYNum x y) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hY hYi (by
        rw [hYred]
        norm_num)
    have hneg : y ≠ WeierstrassCurve.Affine.negY E49Curve x y := by
      intro heq
      apply hd
      simp [E49DoubleDen, E49Curve, WeierstrassCurve.Affine.negY] at heq ⊢
      linarith
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (E49DoubleDen x y), by omega, ?_, ?_⟩
    · rw [E49_doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN,
        padicValRat.pow hd]
      ring
    · rw [E49_doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY,
        padicValRat.pow hd]
      ring

/-- Doubling preserves the formal kernel at two. -/
theorem E49FormalAtTwo_double {P : E49Point}
    (hP : E49FormalAtTwo P) : E49FormalAtTwo (2 • P) := by
  rw [E49FormalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases E49FormalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-- Twice every rational point lies in the formal kernel at two. -/
theorem E49_two_nsmul_formal (P : E49Point) :
    E49FormalAtTwo (2 • P) := by
  rcases E49_formal_or_integral P with hformal | hintegral
  · exact E49FormalAtTwo_double hformal
  · cases P with
    | zero => trivial
    | some x y h =>
        exact E49_double_formal_of_integral hintegral.1 hintegral.2

private theorem E49FormalLevel_unique {P : E49Point} {k l : ℤ}
    (hk : E49FormalLevel P k) (hl : E49FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [E49FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

theorem E49FormalLevel_two_power {P : E49Point} {k : ℤ}
    (hP : E49FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + (n : ℤ) ≤ k' ∧
        E49FormalLevel ((2 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      right
      exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) • P =
          2 • ((2 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      rcases ih with hzero | ⟨l, hkl, hl⟩
      · left
        rw [hpow, hzero, nsmul_zero]
      · rcases E49FormalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [hpow, hzero]
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rwa [hpow]

/-- The two-adic formal kernel contains no nonzero point divisible by every
power of two through formal points. -/
theorem E49_formal_separated (P : E49Point)
    (hP : E49FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : E49Point,
      E49FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, E49FormalLevel P k := by
    rw [E49FormalAtTwo_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, E49FormalLevel Q l := by
    rw [E49FormalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x y h => exact hl.1
  rcases E49FormalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : E49FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := E49FormalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k :=
      Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat, heq] at hbound
    omega

/-- Weak descent and two-adic separatedness show that every point on the
split model is killed by two. -/
theorem ESplit_two_nsmul_eq_zero (P : ESplitPoint) : 2 • P = 0 := by
  let P0 : E49Point := E49SplitAddEquiv.symm P
  have hP0formal : E49FormalAtTwo (2 • P0) :=
    E49_two_nsmul_formal P0
  have hdiv : ∀ n : ℕ, ∃ Q0 : E49Point,
      E49FormalAtTwo Q0 ∧
        2 • P0 = (2 ^ n : ℕ) • Q0 := by
    intro n
    obtain ⟨Q, hQ⟩ := ESplit_two_nsmul_two_power_divisible P n
    refine ⟨2 • E49SplitAddEquiv.symm Q,
      E49_two_nsmul_formal (E49SplitAddEquiv.symm Q), ?_⟩
    have hm := congrArg E49SplitAddEquiv.symm hQ
    simpa only [map_nsmul, AddEquiv.symm_apply_apply, P0] using hm
  have hzero : 2 • P0 = 0 :=
    E49_formal_separated (2 • P0) hP0formal hdiv
  have hm := congrArg E49SplitAddEquiv hzero
  simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, P0] using hm

theorem E49_two_nsmul_eq_zero (P : E49Point) : 2 • P = 0 := by
  have h := ESplit_two_nsmul_eq_zero (E49SplitAddEquiv P)
  have hm := congrArg E49SplitAddEquiv.symm h
  simpa only [map_nsmul, AddEquiv.symm_apply_apply, map_zero] using hm

/-- Every affine rational point on `49a1` is its nonzero two-torsion point. -/
theorem affine_is_two_torsion {x y : ℚ} (hE : OnE49 x y) :
    2 * y + x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular E49Curve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E49Curve_equation_iff x y).mpr hE)
  have h2 := E49_two_nsmul_eq_zero
    (WeierstrassCurve.Affine.Point.some x y hns)
  have hadd :
      (WeierstrassCurve.Affine.Point.some x y hns : E49Point) +
        WeierstrassCurve.Affine.Point.some x y hns = 0 := by
    simpa only [two_nsmul] using h2
  have hneg := eq_neg_of_add_eq_zero_left hadd
  rw [WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hneg
  simp [E49Curve, WeierstrassCurve.Affine.negY] at hneg
  linarith [hneg]

end

end MazurProof.RationalPointsX049
