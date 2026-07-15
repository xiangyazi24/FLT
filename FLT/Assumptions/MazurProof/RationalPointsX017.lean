import FLT.Assumptions.MazurProof.RationalPointsN15Descent

/-!
# Rational points on `X₀(17)`

This file proves the rank-zero calculation for the minimal model

`y² + x*y + y = x³ - x² - x - 14`.

The proof uses the split model

`V² = U³ + 270*U² + 23409*U`

and its rational `2`-isogenous companion

`Z² = X³ - 540*X² - 20736*X`.
-/

namespace MazurProof.RationalPointsX017

noncomputable section

open RationalPointsN15Descent

def E17Curve : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := -1
  a₆ := -14

def ESplitCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 270
  a₃ := 0
  a₄ := 23409
  a₆ := 0

def EHatCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -540
  a₃ := 0
  a₄ := -20736
  a₆ := 0

def OnE17 (x y : ℚ) : Prop :=
  y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14

def OnESplit (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 + 270 * U ^ 2 + 23409 * U

def OnEHat (X Z : ℚ) : Prop :=
  Z ^ 2 = X ^ 3 - 540 * X ^ 2 - 20736 * X

theorem E17Curve_delta : E17Curve.Δ = (-83521 : ℚ) := by
  norm_num [E17Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem ESplitCurve_delta : ESplitCurve.Δ = (-181807037485056 : ℚ) := by
  norm_num [ESplitCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem EHatCurve_delta : EHatCurve.Δ = (2576753029545984 : ℚ) := by
  norm_num [EHatCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E17Curve_isElliptic : E17Curve.IsElliptic where
  isUnit := by rw [E17Curve_delta]; norm_num

instance ESplitCurve_isElliptic : ESplitCurve.IsElliptic where
  isUnit := by rw [ESplitCurve_delta]; norm_num

instance EHatCurve_isElliptic : EHatCurve.IsElliptic where
  isUnit := by rw [EHatCurve_delta]; norm_num

@[simp] theorem E17Curve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E17Curve x y ↔ OnE17 x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E17Curve, OnE17]
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

abbrev E17Point := WeierstrassCurve.Affine.Point E17Curve
abbrev ESplitPoint := WeierstrassCurve.Affine.Point ESplitCurve
abbrev EHatPoint := WeierstrassCurve.Affine.Point EHatCurve

theorem to_split_equation {x y : ℚ} (h : OnE17 x y) :
    OnESplit (36 * x - 99) (108 * (2 * y + x + 1)) := by
  unfold OnE17 at h
  unfold OnESplit
  linear_combination 46656 * h

theorem from_split_equation {U V : ℚ} (h : OnESplit U V) :
    OnE17 (U / 36 + 11 / 4) (V / 216 - U / 72 - 15 / 8) := by
  unfold OnESplit at h
  unfold OnE17
  linear_combination (1 / 46656 : ℚ) * h

/-! ## The explicit two-isogeny -/

def phiX (U V : ℚ) : ℚ := V ^ 2 / U ^ 2

def phiY (U V : ℚ) : ℚ := V * (23409 - U ^ 2) / U ^ 2

def dualX (X Z : ℚ) : ℚ := Z ^ 2 / (4 * X ^ 2)

def dualY (X Z : ℚ) : ℚ := Z * (-20736 - X ^ 2) / (8 * X ^ 2)

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
  (3 * U ^ 2 + 540 * U + 23409) / (2 * V)

private def EHatTangent (X Z : ℚ) : ℚ :=
  (3 * X ^ 2 - 1080 * X - 20736) / (2 * Z)

private def tangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

theorem dual_phi_x {U V : ℚ} (hU : U ≠ 0) (hV : V ≠ 0)
    (h : OnESplit U V) :
    dualX (phiX U V) (phiY U V) =
      tangentX 270 U (ESplitTangent U V) := by
  unfold dualX phiX phiY tangentX ESplitTangent
  unfold OnESplit at h
  field_simp [hU, hV]
  rw [h]
  ring

theorem dual_phi_y {U V : ℚ} (hU : U ≠ 0) (hV : V ≠ 0)
    (h : OnESplit U V) :
    dualY (phiX U V) (phiY U V) =
      -(ESplitTangent U V *
          (tangentX 270 U (ESplitTangent U V) - U) + V) := by
  unfold dualY phiX phiY tangentX ESplitTangent
  unfold OnESplit at h
  field_simp [hU, hV]
  have hV4 : V ^ 4 = (U ^ 3 + 270 * U ^ 2 + 23409 * U) ^ 2 := by
    calc
      V ^ 4 = (V ^ 2) ^ 2 := by ring
      _ = (U ^ 3 + 270 * U ^ 2 + 23409 * U) ^ 2 := by rw [h]
  rw [hV4, h]
  ring

theorem phi_dual_x {X Z : ℚ} (hX : X ≠ 0) (hZ : Z ≠ 0)
    (h : OnEHat X Z) :
    phiX (dualX X Z) (dualY X Z) =
      tangentX (-540) X (EHatTangent X Z) := by
  unfold phiX dualX dualY tangentX EHatTangent
  unfold OnEHat at h
  field_simp [hX, hZ]
  rw [h]
  ring

theorem phi_dual_y {X Z : ℚ} (hX : X ≠ 0) (hZ : Z ≠ 0)
    (h : OnEHat X Z) :
    phiY (dualX X Z) (dualY X Z) =
      -(EHatTangent X Z *
          (tangentX (-540) X (EHatTangent X Z) - X) + Z) := by
  unfold phiY dualX dualY tangentX EHatTangent
  unfold OnEHat at h
  field_simp [hX, hZ]
  have hZ4 : Z ^ 4 = (X ^ 3 - 540 * X ^ 2 - 20736 * X) ^ 2 := by
    calc
      Z ^ 4 = (Z ^ 2) ^ 2 := by ring
      _ = (X ^ 3 - 540 * X ^ 2 - 20736 * X) ^ 2 := by rw [h]
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
      tangentX 270 U (ESplitTangent U V) := by
  simp [ESplitCurve, tangentX]
  ring

private theorem EHatCurve_addX_tangent (X Z : ℚ) :
    WeierstrassCurve.Affine.addX EHatCurve X X (EHatTangent X Z) =
      tangentX (-540) X (EHatTangent X Z) := by
  simp [EHatCurve, tangentX]
  ring

private theorem ESplitCurve_addY_tangent (U V : ℚ) :
    WeierstrassCurve.Affine.addY ESplitCurve U U V (ESplitTangent U V) =
      -(ESplitTangent U V *
          (tangentX 270 U (ESplitTangent U V) - U) + V) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX tangentX
    ESplitCurve
  ring

private theorem EHatCurve_addY_tangent (X Z : ℚ) :
    WeierstrassCurve.Affine.addY EHatCurve X X Z (EHatTangent X Z) =
      -(EHatTangent X Z *
          (tangentX (-540) X (EHatTangent X Z) - X) + Z) := by
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
  270 + 2 * r ^ 2 - 2 * V / r

def dualPreimageY (r V : ℚ) : ℚ :=
  2 * r * dualPreimageX r V

def phiPreimageX (r Z : ℚ) : ℚ :=
  (r ^ 2 - 270 - Z / r) / 2

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
  have hcurve : V ^ 2 = U ^ 3 + 270 * U ^ 2 + 23409 * U := by
    exact (ESplitCurve_equation_iff U V).mp h.1
  have hcurveR : V ^ 2 = r ^ 6 + 270 * r ^ 4 + 23409 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := dualPreimageX r V
  let qy := dualPreimageY r V
  have hprod : qx * (270 + 2 * r ^ 2 + 2 * V / r) = -20736 := by
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : -20736 - qx ^ 2 = 4 * qx * V / r := by
    rw [← hprod]
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : OnEHat qx qy := by
    unfold OnEHat
    dsimp [qx, qy, dualPreimageX, dualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (2 * V - 2 * r ^ 3 - 270 * r) * hcurveR
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
  · change (2 * r * qx) * (-20736 - qx ^ 2) / (8 * qx ^ 2) = V
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
  have hcurve : Z ^ 2 = X ^ 3 - 540 * X ^ 2 - 20736 * X := by
    exact (EHatCurve_equation_iff X Z).mp h.1
  have hcurveR : Z ^ 2 = r ^ 6 - 540 * r ^ 4 - 20736 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := phiPreimageX r Z
  let py := phiPreimageY r Z
  have hprod : px * ((r ^ 2 - 270 + Z / r) / 2) = 23409 := by
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 23409 - px ^ 2 = px * Z / r := by
    rw [← hprod]
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    ring
  have hpeq : OnESplit px py := by
    unfold OnESplit
    dsimp [px, py, phiPreimageX, phiPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + 270 * r + Z) * hcurveR
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
  · change (r * px) * (23409 - px ^ 2) / px ^ 2 = Z
    rw [hnum]
    field_simp [hpx, hr0]

/-! ## The two Kummer images -/

theorem ESplit_integral_model {U V : ℚ} (h : OnESplit U V) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      U = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + 270 * A * B ^ 2 + 23409 * B ^ 4) := by
  have hcubic : V ^ 2 =
      U ^ 3 + ((270 : ℤ) : ℚ) * U ^ 2 + ((23409 : ℤ) : ℚ) * U := by
    simpa [OnESplit] using h
  exact integral_model_monic 270 23409 U V hcubic

theorem EHat_integral_model {X Z : ℚ} (h : OnEHat X Z) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      X = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 - 540 * A * B ^ 2 - 20736 * B ^ 4) := by
  have hcubic : Z ^ 2 =
      X ^ 3 + ((-540 : ℤ) : ℚ) * X ^ 2 + ((-20736 : ℤ) : ℚ) * X := by
    simpa [OnEHat, sub_eq_add_neg] using h
  simpa [sub_eq_add_neg] using
    integral_model_monic (-540) (-20736) X Z hcubic

private theorem squarefree_dvd_23409 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 23409) :
    d = 1 ∨ d = 3 ∨ d = 17 ∨ d = 51 := by
  have hpow : d ∣ 153 ^ 2 := by simpa using hdiv
  have hd153 : d ∣ 153 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  have hdle : d ≤ 153 := Nat.le_of_dvd (by norm_num) hd153
  have hnot9 : ¬ 3 * 3 ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.mp hd) 3 (by norm_num)
  interval_cases d <;> norm_num at hd153
  all_goals norm_num at hnot9
  all_goals simp

private theorem squarefree_dvd_20736 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 20736) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
  have hpow : d ∣ 144 ^ 2 := by simpa using hdiv
  have hd144 : d ∣ 144 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  have hdle : d ≤ 144 := Nat.le_of_dvd (by norm_num) hd144
  have hnot4 : ¬ 2 * 2 ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.mp hd) 2 Nat.prime_two
  have hnot9 : ¬ 3 * 3 ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.mp hd) 3 (by norm_num)
  interval_cases d <;> norm_num at hd144
  all_goals solve | norm_num at hnot4 | norm_num at hnot9 | simp

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

private theorem primitive_mod_two {r B : ℤ} (hcop : Int.gcd r B = 1) :
    reduce16to2 (r : ZMod 16) ≠ 0 ∨
      reduce16to2 (B : ZMod 16) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [reduce16to2, ZMod.castHom_apply] using hmod2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_ESplit_three_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 3 * r ^ 4 + 270 * r ^ 2 * B ^ 2 + 7803 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_ESplit_fifty_one_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 51 * r ^ 4 + 270 * r ^ 2 * B ^ 2 + 459 * B ^ 4 := by
  decide

private theorem no_primitive_ESplit_three (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 3 * r ^ 4 + 270 * r ^ 2 * B ^ 2 + 7803 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_ESplit_three_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem no_primitive_ESplit_fifty_one (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 51 * r ^ 4 + 270 * r ^ 2 * B ^ 2 + 459 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_ESplit_fifty_one_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem primitive_mod_seventeen {r B : ℤ} (hcop : Int.gcd r B = 1) :
    (r : ZMod 17) ≠ 0 ∨ (B : ZMod 17) ≠ 0 := by
  have hnot : ¬ ((17 : ℤ) ∣ r ∧ (17 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h17g : (17 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h17g
    norm_num at h17g
  by_contra h
  push Not at h
  exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 17).mp h.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd B 17).mp h.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_EHat_three_six_mod17 :
    (∀ r B z : ZMod 17, (r ≠ 0 ∨ B ≠ 0) →
      z ^ 2 ≠ 3 * r ^ 4 - 540 * r ^ 2 * B ^ 2 - 6912 * B ^ 4) ∧
    (∀ r B z : ZMod 17, (r ≠ 0 ∨ B ≠ 0) →
      z ^ 2 ≠ -3 * r ^ 4 - 540 * r ^ 2 * B ^ 2 + 6912 * B ^ 4) ∧
    (∀ r B z : ZMod 17, (r ≠ 0 ∨ B ≠ 0) →
      z ^ 2 ≠ 6 * r ^ 4 - 540 * r ^ 2 * B ^ 2 - 3456 * B ^ 4) ∧
    (∀ r B z : ZMod 17, (r ≠ 0 ∨ B ≠ 0) →
      z ^ 2 ≠ -6 * r ^ 4 - 540 * r ^ 2 * B ^ 2 + 3456 * B ^ 4) := by
  decide

private theorem no_primitive_EHat_pos_three (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 3 * r ^ 4 - 540 * r ^ 2 * B ^ 2 - 6912 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 17)) h
  push_cast at hm
  exact (no_EHat_three_six_mod17.1 _ _ _ (primitive_mod_seventeen hcop)) hm

private theorem no_primitive_EHat_neg_three (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -3 * r ^ 4 - 540 * r ^ 2 * B ^ 2 + 6912 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 17)) h
  push_cast at hm
  exact (no_EHat_three_six_mod17.2.1 _ _ _ (primitive_mod_seventeen hcop)) hm

private theorem no_primitive_EHat_pos_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 6 * r ^ 4 - 540 * r ^ 2 * B ^ 2 - 3456 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 17)) h
  push_cast at hm
  exact (no_EHat_three_six_mod17.2.2.1 _ _ _ (primitive_mod_seventeen hcop)) hm

private theorem no_primitive_EHat_neg_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -6 * r ^ 4 - 540 * r ^ 2 * B ^ 2 + 3456 * B ^ 4) :
    False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 17)) h
  push_cast at hm
  exact (no_EHat_three_six_mod17.2.2.2 _ _ _ (primitive_mod_seventeen hcop)) hm

private def reduce16to4 : ZMod 16 →+* ZMod 4 :=
  ZMod.castHom (by norm_num : 4 ∣ 16) (ZMod 4)

private def reduce64to8 : ZMod 64 →+* ZMod 8 :=
  ZMod.castHom (by norm_num : 8 ∣ 64) (ZMod 8)

private theorem reduce16to4_eq_zero_of_sq_zero (a : ZMod 16)
    (h : a ^ 2 = 0) : reduce16to4 a = 0 := by
  decide +revert

private theorem reduce64to8_eq_zero_of_sq_zero (a : ZMod 64)
    (h : a ^ 2 = 0) : reduce64to8 a = 0 := by
  decide +revert

private theorem four_dvd_of_sq_zero_mod16 (z : ℤ)
    (h : (z : ZMod 16) ^ 2 = 0) : (4 : ℤ) ∣ z := by
  have hz4 : reduce16to4 (z : ZMod 16) = 0 :=
    reduce16to4_eq_zero_of_sq_zero _ h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z 4).mp
  simpa [reduce16to4, ZMod.castHom_apply] using hz4

private theorem eight_dvd_of_sq_zero_mod64 (z : ℤ)
    (h : (z : ZMod 64) ^ 2 = 0) : (8 : ℤ) ∣ z := by
  have hz8 : reduce64to8 (z : ZMod 64) = 0 :=
    reduce64to8_eq_zero_of_sq_zero _ h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z 8).mp
  simpa [reduce64to8, ZMod.castHom_apply] using hz8

private theorem no_sq_two_mod4 (z : ZMod 4) : z ^ 2 ≠ 2 := by
  fin_cases z <;> decide

private theorem no_sq_128_mod256 (z : ZMod 256) : z ^ 2 ≠ 128 := by
  fin_cases z <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem EHat_two_edge_residues :
    (∀ k b : ZMod 16,
      2 * (2 * k) ^ 4 - 540 * (2 * k) ^ 2 * (2 * b + 1) ^ 2 -
        10368 * (2 * b + 1) ^ 4 = 0) ∧
    (∀ k b : ZMod 16,
      -2 * (2 * k) ^ 4 - 540 * (2 * k) ^ 2 * (2 * b + 1) ^ 2 +
        10368 * (2 * b + 1) ^ 4 = 0) ∧
    (∀ a b : ZMod 64,
      2 * (4 * a) ^ 4 - 540 * (4 * a) ^ 2 * (2 * b + 1) ^ 2 -
        10368 * (2 * b + 1) ^ 4 = 0) ∧
    (∀ a b : ZMod 64,
      -2 * (4 * a) ^ 4 - 540 * (4 * a) ^ 2 * (2 * b + 1) ^ 2 +
        10368 * (2 * b + 1) ^ 4 = 0) ∧
    (∀ c b : ZMod 256,
      2 * (8 * c) ^ 4 - 540 * (8 * c) ^ 2 * (2 * b + 1) ^ 2 -
        10368 * (2 * b + 1) ^ 4 = 128) ∧
    (∀ c b : ZMod 256,
      -2 * (8 * c) ^ 4 - 540 * (8 * c) ^ 2 * (2 * b + 1) ^ 2 +
        10368 * (2 * b + 1) ^ 4 = 128) ∧
    (∀ k B : ZMod 4,
      2 * (2 * k + 1) ^ 4 - 540 * (2 * k + 1) ^ 2 * B ^ 2 -
        10368 * B ^ 4 = 2) ∧
    (∀ k B : ZMod 4,
      -2 * (2 * k + 1) ^ 4 - 540 * (2 * k + 1) ^ 2 * B ^ 2 +
        10368 * B ^ 4 = 2) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_EHat_two_middle_residues :
    (∀ a b w : ZMod 16,
      w ^ 2 ≠ 2 * (2 * a + 1) ^ 4 -
        135 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 -
        648 * (2 * b + 1) ^ 4) ∧
    (∀ a b w : ZMod 16,
      w ^ 2 ≠ -2 * (2 * a + 1) ^ 4 -
        135 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 +
        648 * (2 * b + 1) ^ 4) ∧
    (∀ a b w : ZMod 8,
      w ^ 2 ≠ 8 * (2 * a + 1) ^ 4 -
        135 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 -
        162 * (2 * b + 1) ^ 4) ∧
    (∀ a b w : ZMod 8,
      w ^ 2 ≠ -8 * (2 * a + 1) ^ 4 -
        135 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 +
        162 * (2 * b + 1) ^ 4) := by
  decide

private theorem no_primitive_EHat_two (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (r B z : ℤ) (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = sign * 2 * r ^ 4 - 540 * r ^ 2 * B ^ 2 -
      sign * 10368 * B ^ 4) : False := by
  rcases hsign with rfl | rfl
  · rcases Int.even_or_odd' r with ⟨k, hr | hr⟩
    · subst r
      rcases Int.even_or_odd' B with ⟨b, hB | hB⟩
      · subst B
        have h2g : (2 : ℤ) ∣ ((Int.gcd (2 * k) (2 * b) : ℕ) : ℤ) :=
          Int.dvd_coe_gcd (dvd_mul_right 2 k) (dvd_mul_right 2 b)
        rw [hcop] at h2g
        norm_num at h2g
      · subst B
        have hz16 : (z : ZMod 16) ^ 2 = 0 := by
          have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
          push_cast at hm
          change (z : ZMod 16) ^ 2 =
            2 * (2 * (k : ZMod 16)) ^ 4 -
              540 * (2 * (k : ZMod 16)) ^ 2 * (2 * (b : ZMod 16) + 1) ^ 2 -
              10368 * (2 * (b : ZMod 16) + 1) ^ 4 at hm
          exact hm.trans (EHat_two_edge_residues.1 _ _)
        obtain ⟨w, hw⟩ := four_dvd_of_sq_zero_mod16 z hz16
        subst z
        have hdiv : w ^ 2 = 2 * k ^ 4 - 135 * k ^ 2 * (2 * b + 1) ^ 2 -
            648 * (2 * b + 1) ^ 4 := by nlinarith [h]
        rcases Int.even_or_odd' k with ⟨a, hk | hk⟩
        · subst k
          have hz64 : (w * 4 : ZMod 64) ^ 2 = 0 := by
            have hm := congrArg (fun n : ℤ => (n : ZMod 64)) h
            push_cast at hm
            calc
              (w * 4 : ZMod 64) ^ 2 =
                  2 * (2 * (2 * (a : ZMod 64))) ^ 4 -
                    540 * (2 * (2 * (a : ZMod 64))) ^ 2 *
                      (2 * (b : ZMod 64) + 1) ^ 2 -
                    10368 * (2 * (b : ZMod 64) + 1) ^ 4 := by simpa [mul_comm] using hm
              _ = 0 := by
                convert EHat_two_edge_residues.2.2.1 (a : ZMod 64) (b : ZMod 64) using 1
                all_goals ring
          have h8z : (8 : ℤ) ∣ 4 * w :=
            eight_dvd_of_sq_zero_mod64 (4 * w) (by simpa [mul_comm] using hz64)
          have h2w : (2 : ℤ) ∣ w := by omega
          obtain ⟨v, hv⟩ := h2w
          subst w
          have hdiv64 : v ^ 2 = 8 * a ^ 4 - 135 * a ^ 2 * (2 * b + 1) ^ 2 -
              162 * (2 * b + 1) ^ 4 := by nlinarith [hdiv]
          rcases Int.even_or_odd' a with ⟨c, ha | ha⟩
          · subst a
            have hm := congrArg (fun n : ℤ => (n : ZMod 256)) h
            push_cast at hm
            apply no_sq_128_mod256 (((8 * v : ℤ) : ZMod 256))
            calc
              (((8 * v : ℤ) : ZMod 256)) ^ 2 =
                  (4 * (2 * (v : ZMod 256))) ^ 2 := by push_cast; ring
              _ = 2 * (2 * (2 * (2 * (c : ZMod 256)))) ^ 4 -
                    540 * (2 * (2 * (2 * (c : ZMod 256)))) ^ 2 *
                      (2 * (b : ZMod 256) + 1) ^ 2 -
                    10368 * (2 * (b : ZMod 256) + 1) ^ 4 := hm
              _ = 128 := by
                convert EHat_two_edge_residues.2.2.2.2.1
                  (c : ZMod 256) (b : ZMod 256) using 1
                all_goals ring
          · subst a
            have hm := congrArg (fun n : ℤ => (n : ZMod 8)) hdiv64
            push_cast at hm
            exact (no_EHat_two_middle_residues.2.2.1 _ _ _) hm
        · subst k
          have hm := congrArg (fun n : ℤ => (n : ZMod 16)) hdiv
          push_cast at hm
          exact (no_EHat_two_middle_residues.1 _ _ _) hm
    · subst r
      have hm := congrArg (fun n : ℤ => (n : ZMod 4)) h
      push_cast at hm
      apply no_sq_two_mod4 (z : ZMod 4)
      change (z : ZMod 4) ^ 2 =
        2 * (2 * (k : ZMod 4) + 1) ^ 4 -
          540 * (2 * (k : ZMod 4) + 1) ^ 2 * (B : ZMod 4) ^ 2 -
          10368 * (B : ZMod 4) ^ 4 at hm
      exact hm.trans (EHat_two_edge_residues.2.2.2.2.2.2.1 _ _)
  · norm_num at h
    rcases Int.even_or_odd' r with ⟨k, hr | hr⟩
    · subst r
      rcases Int.even_or_odd' B with ⟨b, hB | hB⟩
      · subst B
        have h2g : (2 : ℤ) ∣ ((Int.gcd (2 * k) (2 * b) : ℕ) : ℤ) :=
          Int.dvd_coe_gcd (dvd_mul_right 2 k) (dvd_mul_right 2 b)
        rw [hcop] at h2g
        norm_num at h2g
      · subst B
        have hz16 : (z : ZMod 16) ^ 2 = 0 := by
          have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
          push_cast at hm
          calc
            (z : ZMod 16) ^ 2 =
                -(2 * (2 * (k : ZMod 16)) ^ 4) -
                  540 * (2 * (k : ZMod 16)) ^ 2 * (2 * (b : ZMod 16) + 1) ^ 2 +
                  10368 * (2 * (b : ZMod 16) + 1) ^ 4 := hm
            _ = 0 := by
              convert EHat_two_edge_residues.2.1 (k : ZMod 16) (b : ZMod 16) using 1
              all_goals ring
        obtain ⟨w, hw⟩ := four_dvd_of_sq_zero_mod16 z hz16
        subst z
        have hdiv : w ^ 2 = -2 * k ^ 4 - 135 * k ^ 2 * (2 * b + 1) ^ 2 +
            648 * (2 * b + 1) ^ 4 := by nlinarith [h]
        rcases Int.even_or_odd' k with ⟨a, hk | hk⟩
        · subst k
          have hz64 : (w * 4 : ZMod 64) ^ 2 = 0 := by
            have hm := congrArg (fun n : ℤ => (n : ZMod 64)) h
            push_cast at hm
            calc
              (w * 4 : ZMod 64) ^ 2 =
                  -(2 * (2 * (2 * (a : ZMod 64))) ^ 4) -
                    540 * (2 * (2 * (a : ZMod 64))) ^ 2 *
                      (2 * (b : ZMod 64) + 1) ^ 2 +
                    10368 * (2 * (b : ZMod 64) + 1) ^ 4 := by simpa [mul_comm] using hm
              _ = 0 := by
                convert EHat_two_edge_residues.2.2.2.1
                  (a : ZMod 64) (b : ZMod 64) using 1
                all_goals ring
          have h8z : (8 : ℤ) ∣ 4 * w :=
            eight_dvd_of_sq_zero_mod64 (4 * w) (by simpa [mul_comm] using hz64)
          have h2w : (2 : ℤ) ∣ w := by omega
          obtain ⟨v, hv⟩ := h2w
          subst w
          have hdiv64 : v ^ 2 = -8 * a ^ 4 - 135 * a ^ 2 * (2 * b + 1) ^ 2 +
              162 * (2 * b + 1) ^ 4 := by nlinarith [hdiv]
          rcases Int.even_or_odd' a with ⟨c, ha | ha⟩
          · subst a
            have hm := congrArg (fun n : ℤ => (n : ZMod 256)) h
            push_cast at hm
            apply no_sq_128_mod256 (((8 * v : ℤ) : ZMod 256))
            calc
              (((8 * v : ℤ) : ZMod 256)) ^ 2 =
                  (4 * (2 * (v : ZMod 256))) ^ 2 := by push_cast; ring
              _ = -(2 * (2 * (2 * (2 * (c : ZMod 256)))) ^ 4) -
                    540 * (2 * (2 * (2 * (c : ZMod 256)))) ^ 2 *
                      (2 * (b : ZMod 256) + 1) ^ 2 +
                    10368 * (2 * (b : ZMod 256) + 1) ^ 4 := hm
              _ = 128 := by
                convert EHat_two_edge_residues.2.2.2.2.2.1
                  (c : ZMod 256) (b : ZMod 256) using 1
                all_goals ring
          · subst a
            have hm := congrArg (fun n : ℤ => (n : ZMod 8)) hdiv64
            push_cast at hm
            exact (no_EHat_two_middle_residues.2.2.2 _ _ _) hm
        · subst k
          have hm := congrArg (fun n : ℤ => (n : ZMod 16)) hdiv
          push_cast at hm
          exact (no_EHat_two_middle_residues.2.1 _ _ _) hm
    · subst r
      have hm := congrArg (fun n : ℤ => (n : ZMod 4)) h
      push_cast at hm
      apply no_sq_two_mod4 (z : ZMod 4)
      calc
        (z : ZMod 4) ^ 2 = -(2 * (2 * (k : ZMod 4) + 1) ^ 4) -
            540 * (2 * (k : ZMod 4) + 1) ^ 2 * (B : ZMod 4) ^ 2 +
            10368 * (B : ZMod 4) ^ 4 := hm
        _ = 2 := by
          convert EHat_two_edge_residues.2.2.2.2.2.2.2
            (k : ZMod 4) (B : ZMod 4) using 1
          all_goals ring

private theorem ESplit_x_nonnegative {U V : ℚ} (h : OnESplit U V) : 0 ≤ U := by
  by_contra hU
  have hUneg : U < 0 := lt_of_not_ge hU
  have hquad : 0 < U ^ 2 + 270 * U + 23409 := by
    nlinarith [sq_nonneg (U + 135)]
  unfold OnESplit at h
  nlinarith [mul_neg_of_neg_of_pos hUneg hquad, sq_nonneg V]

/-- The Kummer image on the split curve consists of the classes `1` and `17`. -/
theorem ESplit_rational_x_squareclasses {U V : ℚ}
    (h : OnESplit U V) (hU0 : U ≠ 0) :
    ∃ q : ℚ, U = q ^ 2 ∨ U = 17 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hU, hmodel⟩ := ESplit_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hU0
    rw [hU, hA]
    norm_num
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel
  have hdiv23409 : d ∣ 23409 := by simpa using hdiv
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
  rcases squarefree_dvd_23409 hd hdiv23409 with rfl | rfl | rfl | rfl
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    simpa using rat_squareclass_of_integral hB0 hU hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 270) (b := 23409) (d := 3) (e := 7803)
      (by norm_num) hr0 (by norm_num) hA hmodel
    exact (no_primitive_ESplit_three _ _ _
      (root_coprime_denominator hcop hA) hz).elim
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    simpa using rat_squareclass_of_integral hB0 hU hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 270) (b := 23409) (d := 51) (e := 459)
      (by norm_num) hr0 (by norm_num) hA hmodel
    exact (no_primitive_ESplit_fifty_one _ _ _
      (root_coprime_denominator hcop hA) hz).elim

/-- The dual Kummer image consists of the classes `1` and `-1`. -/
theorem EHat_rational_x_squareclasses {X Z : ℚ}
    (h : OnEHat X Z) (hX0 : X ≠ 0) :
    ∃ q : ℚ, X = q ^ 2 ∨ X = -(q ^ 2) := by
  obtain ⟨A, B, C, hBpos, hcop, hX, hmodel⟩ := EHat_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hX0
    rw [hX, hA]
    norm_num
  have hmodel' :
      C ^ 2 = A * (A ^ 2 + (-540) * A * B ^ 2 + (-20736) * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  have hdiv20736 : d ∣ 20736 := by simpa using hdiv
  rcases squarefree_dvd_20736 hd hdiv20736 with rfl | rfl | rfl | rfl
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
      simpa using rat_squareclass_of_integral hB0 hX hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
      have hA' : A = (-1 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      simpa using rat_squareclass_of_integral hB0 hX hA'
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA, hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := 2) (e := -10368)
        (by norm_num) hr0 (by norm_num) hA hmodel'
      exact (no_primitive_EHat_two 1 (Or.inl rfl) _ _ _
        (root_coprime_denominator hcop hA) (by simpa [sub_eq_add_neg] using hz)).elim
    · have hA' : A = (-2 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA', hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := -2) (e := 10368)
        (by norm_num) hr0 (by norm_num) hA' hmodel'
      exact (no_primitive_EHat_two (-1) (Or.inr rfl) _ _ _
        (root_coprime_denominator hcop hA') (by simpa [sub_eq_add_neg] using hz)).elim
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA, hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := 3) (e := -6912)
        (by norm_num) hr0 (by norm_num) hA hmodel'
      exact (no_primitive_EHat_pos_three _ _ _
        (root_coprime_denominator hcop hA) (by simpa [sub_eq_add_neg] using hz)).elim
    · have hA' : A = (-3 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA', hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := -3) (e := 6912)
        (by norm_num) hr0 (by norm_num) hA' hmodel'
      exact (no_primitive_EHat_neg_three _ _ _
        (root_coprime_denominator hcop hA') (by simpa [sub_eq_add_neg] using hz)).elim
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA, hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := 6) (e := -3456)
        (by norm_num) hr0 (by norm_num) hA hmodel'
      exact (no_primitive_EHat_pos_six _ _ _
        (root_coprime_denominator hcop hA) (by simpa [sub_eq_add_neg] using hz)).elim
    · have hA' : A = (-6 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr; apply hA0; rw [hA', hr]; norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := -540) (b := -20736) (d := -6) (e := 3456)
        (by norm_num) hr0 (by norm_num) hA' hmodel'
      exact (no_primitive_EHat_neg_six _ _ _
        (root_coprime_denominator hcop hA') (by simpa [sub_eq_add_neg] using hz)).elim

/-! ## The weak two-descent -/

private def ESplitPointOf (U V : ℚ) (h : OnESplit U V) : ESplitPoint :=
  WeierstrassCurve.Affine.Point.some U V
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((ESplitCurve_equation_iff U V).mpr h))

private def EHatKernel : EHatPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((EHatCurve_equation_iff 0 0).mpr (by norm_num [OnEHat]))

private theorem EHatKernel_nonsingular :
    WeierstrassCurve.Affine.Nonsingular EHatCurve 0 0 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((EHatCurve_equation_iff 0 0).mpr (by norm_num [OnEHat]))

private theorem EHatKernel_two : 2 • EHatKernel = 0 :=
  EHat_double_eq_zero_of_y_zero _ rfl

private theorem EHat_slope_kernel {X Z : ℚ} (hX : X ≠ 0) :
    WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0 = Z / X := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hX]
  ring

private theorem EHat_add_kernel_x {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z) (hX : X ≠ 0) :
    WeierstrassCurve.Affine.addX EHatCurve X 0
        (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) = -20736 / X := by
  rw [EHat_slope_kernel hX]
  have heq := (EHatCurve_equation_iff X Z).mp h.1
  unfold OnEHat at heq
  unfold WeierstrassCurve.Affine.addX EHatCurve
  field_simp [hX]
  linear_combination heq

private theorem dual_translation_coordinates {X Z : ℚ} (hX : X ≠ 0) :
    dualX (-20736 / X) (20736 * Z / X ^ 2) = dualX X Z ∧
      dualY (-20736 / X) (20736 * Z / X ^ 2) = dualY X Z := by
  constructor
  · unfold dualX
    field_simp [hX]
  · unfold dualY
    field_simp [hX]
    ring

private theorem EHat_add_kernel_y {X Z : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular EHatCurve X Z) (hX : X ≠ 0) :
    WeierstrassCurve.Affine.addY EHatCurve X 0 Z
        (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) =
      20736 * Z / X ^ 2 := by
  rw [EHat_slope_kernel hX]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY
  have hX' : WeierstrassCurve.Affine.addX EHatCurve X 0 (Z / X) =
      -20736 / X := by
    rw [← EHat_slope_kernel hX]
    exact EHat_add_kernel_x h hX
  rw [hX']
  simp [EHatCurve]
  field_simp [hX]
  ring

private theorem dualPoint_add_kernel (P : EHatPoint) :
    dualPoint (P + EHatKernel) = dualPoint P := by
  cases P with
  | zero => rfl
  | some X Z h =>
      by_cases hX : X = 0
      · have hZ := EHat_y_zero_of_x_zero h hX
        subst X
        subst Z
        change dualPoint (EHatKernel + EHatKernel) = dualPoint EHatKernel
        rw [← two_nsmul, EHatKernel_two, dualPoint_zero]
        rfl
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
          have hX'sq : X' = (144 / r) ^ 2 := by
            change WeierstrassCurve.Affine.addX EHatCurve X 0
              (WeierstrassCurve.Affine.slope EHatCurve X 0 Z 0) = _
            rw [EHat_add_kernel_x hXZ hX, hr]
            field_simp [hr0]
            norm_num
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

private def ESplitGenerator : ESplitPoint :=
  ESplitPointOf 153 3672 (by norm_num [OnESplit])

private theorem ESplitGenerator_four : 4 • ESplitGenerator = 0 := by
  have htwo : 2 • ESplitGenerator = ESplitPointOf 0 0 (by norm_num [OnESplit]) := by
    change 2 • (WeierstrassCurve.Affine.Point.some 153 3672 _ : ESplitPoint) =
      WeierstrassCurve.Affine.Point.some 0 0 _
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by
      norm_num [ESplitCurve, WeierstrassCurve.Affine.negY])]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    norm_num [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      ESplitCurve]
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, htwo]
  exact ESplit_double_eq_zero_of_y_zero _ rfl

private theorem ESplit_y_eq_or_eq_neg_of_same_x
    {x y s : ℚ} (hy : OnESplit x y) (hs : OnESplit x s) :
    y = s ∨ y = -s := by
  have hsq : y ^ 2 = s ^ 2 := by rw [hy, hs]
  have hfac : (y - s) * (y + s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

private theorem ESplit_secant_x_square
    {x y t s q d r : ℚ}
    (hxy : OnESplit x y) (hts : OnESplit t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    WeierstrassCurve.Affine.addX ESplitCurve x t
        (WeierstrassCurve.Affine.slope ESplitCurve x t y (-s)) =
      ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxt]
  unfold WeierstrassCurve.Affine.addX
  simp only [ESplitCurve, zero_mul, sub_neg_eq_add]
  field_simp [sub_ne_zero.mpr hxt, hd, hq, hr]
  have hxdt : d ^ 2 * q ^ 2 * r ^ 2 = x * t := by
    rw [hx, ht]
    ring
  unfold OnESplit at hxy hts
  calc
    ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 270 -
        x * (x - t) ^ 2 - t * (x - t) ^ 2) * d ^ 2 * q ^ 2 * r ^ 2 =
      ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 270 -
        x * (x - t) ^ 2 - t * (x - t) ^ 2) *
        (d ^ 2 * q ^ 2 * r ^ 2) := by ring
    _ = ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 270 -
        x * (x - t) ^ 2 - t * (x - t) ^ 2) * (x * t) := by rw [hxdt]
    _ = (y * t + s * x) ^ 2 := by
      ring_nf
      rw [hxy, hts]
      ring

private theorem ESplit_descent_after_generator
    {x y q : ℚ}
    (hxy : WeierstrassCurve.Affine.Nonsingular ESplitCurve x y)
    (hx : x = 17 * q ^ 2) (hq : q ≠ 0) :
    ∃ T Q : ESplitPoint, 4 • T = 0 ∧
      WeierstrassCurve.Affine.Point.some x y hxy = T + 2 • Q := by
  let P : ESplitPoint := WeierstrassCurve.Affine.Point.some x y hxy
  let T : ESplitPoint := ESplitGenerator
  have hgen : OnESplit 153 3672 := by norm_num [OnESplit]
  by_cases hxt : x = 153
  · have hxeq : OnESplit x y := (ESplitCurve_equation_iff x y).mp hxy.1
    rw [hxt] at hxeq
    rcases ESplit_y_eq_or_eq_neg_of_same_x hxeq hgen with hy | hy
    · refine ⟨P, 0, ?_, by simp [P]⟩
      have hPT : P = T := by
        change WeierstrassCurve.Affine.Point.some x y hxy =
          WeierstrassCurve.Affine.Point.some 153 3672 _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨hxt, hy⟩
      rw [hPT]
      exact ESplitGenerator_four
    · refine ⟨P, 0, ?_, by simp [P]⟩
      have hPT : P = -T := by
        change WeierstrassCurve.Affine.Point.some x y hxy =
          -(WeierstrassCurve.Affine.Point.some 153 3672 _ : ESplitPoint)
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        simp [ESplitCurve, WeierstrassCurve.Affine.negY, hxt, hy]
      rw [hPT]
      simpa using ESplitGenerator_four
  · have hneg : WeierstrassCurve.Affine.Nonsingular ESplitCurve 153 (-3672) :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        ((ESplitCurve_equation_iff 153 (-3672)).mpr (by norm_num [OnESplit]))
    let m := WeierstrassCurve.Affine.slope ESplitCurve x 153 y (-3672)
    let z := WeierstrassCurve.Affine.addX ESplitCurve x 153 m
    let w := WeierstrassCurve.Affine.addY ESplitCurve x 153 y m
    have hR : WeierstrassCurve.Affine.Nonsingular ESplitCurve z w :=
      WeierstrassCurve.Affine.nonsingular_add hxy hneg (fun hbad => hxt hbad.1)
    have hzsq : z = ((y * 153 + 3672 * x) /
        ((x - 153) * 17 * q * 3)) ^ 2 := by
      exact ESplit_secant_x_square
        ((ESplitCurve_equation_iff x y).mp hxy.1) (by norm_num [OnESplit])
        hx (by norm_num) hxt (by norm_num) hq (by norm_num)
    have hsum : P - T = WeierstrassCurve.Affine.Point.some z w hR := by
      have hnegPoint : -T = WeierstrassCurve.Affine.Point.some 153 (-3672) hneg := by
        change -(WeierstrassCurve.Affine.Point.some 153 3672 _ : ESplitPoint) =
          WeierstrassCurve.Affine.Point.some 153 (-3672) hneg
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        simp [ESplitCurve, WeierstrassCurve.Affine.negY]
      dsimp only [P]
      rw [sub_eq_add_neg, hnegPoint]
      dsimp only [z, w, m]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxt
    by_cases hz : z = 0
    · have hw : w = 0 := ESplit_y_zero_of_x_zero hR hz
      let R : ESplitPoint := WeierstrassCurve.Affine.Point.some z w hR
      have hR2 : 2 • R = 0 := ESplit_double_eq_zero_of_y_zero hR hw
      have hP : P = T + R := by
        rw [sub_eq_iff_eq_add] at hsum
        simpa [R, add_comm] using hsum
      refine ⟨P, 0, ?_, by simp [P]⟩
      rw [hP, nsmul_add, ESplitGenerator_four,
        show 4 = 2 * 2 by norm_num, mul_nsmul, hR2, nsmul_zero, add_zero]
    · obtain ⟨Q, hQ⟩ := ESplit_exists_half_of_square_x hR hz ⟨_, hzsq⟩
      refine ⟨T, Q, ESplitGenerator_four, ?_⟩
      change P = T + 2 • Q
      rw [hQ, ← hsum]
      abel

/-- Every point on the split model is a four-torsion point plus twice another
rational point. -/
theorem ESplit_two_descent_step (P : ESplitPoint) :
    ∃ T Q : ESplitPoint, 4 • T = 0 ∧ P = T + 2 • Q := by
  cases P with
  | zero => exact ⟨0, 0, by simp, rfl⟩
  | some U V h =>
      by_cases hU : U = 0
      · have hV : V = 0 := ESplit_y_zero_of_x_zero h hU
        refine ⟨WeierstrassCurve.Affine.Point.some U V h, 0, ?_, by simp⟩
        rw [show 4 = 2 * 2 by norm_num, mul_nsmul,
          ESplit_double_eq_zero_of_y_zero h hV, nsmul_zero]
      · have heq : OnESplit U V := (ESplitCurve_equation_iff U V).mp h.1
        obtain ⟨q, hq | hq⟩ := ESplit_rational_x_squareclasses heq hU
        · obtain ⟨Q, hQ⟩ := ESplit_exists_half_of_square_x h hU ⟨q, hq⟩
          exact ⟨0, Q, by simp, by simpa using hQ.symm⟩
        · have hq0 : q ≠ 0 := by
            intro hq0; apply hU; rw [hq, hq0]; norm_num
          exact ESplit_descent_after_generator h hq hq0

/-- Iterating weak descent makes four times every rational point divisible by
every power of two. -/
theorem ESplit_four_nsmul_two_power_divisible (P : ESplitPoint) (n : ℕ) :
    ∃ Q : ESplitPoint, 4 • P = (2 ^ n : ℕ) • (4 • Q) := by
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

def E17toSplitChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 6 : ℚ) (by norm_num)
  r := 11 / 4
  s := -1 / 2
  t := -15 / 8

theorem E17toSplitChange_curve : E17toSplitChange • E17Curve = ESplitCurve := by
  ext <;>
    simp [E17toSplitChange, E17Curve, ESplitCurve,
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

noncomputable def E17SplitAddEquiv : E17Point ≃+ ESplitPoint :=
  (variableChangePointAddEquiv E17Curve E17toSplitChange).trans
    (curveEqAddEquiv E17toSplitChange_curve)

theorem E17SplitAddEquiv_some
    {x y : ℚ} {h0 : WeierstrassCurve.Affine.Nonsingular E17Curve x y}
    {h1 : WeierstrassCurve.Affine.Nonsingular ESplitCurve
      (36 * x - 99) (108 * (2 * y + x + 1))} :
    E17SplitAddEquiv (WeierstrassCurve.Affine.Point.some x y h0) =
      WeierstrassCurve.Affine.Point.some
        (36 * x - 99) (108 * (2 * y + x + 1)) h1 := by
  change (curveEqAddEquiv E17toSplitChange_curve)
      (variableChangePointMap E17Curve E17toSplitChange
        (WeierstrassCurve.Affine.Point.some x y h0)) = _
  change (curveEqAddEquiv E17toSplitChange_curve)
      (WeierstrassCurve.Affine.Point.some
        (variableChangePointX E17toSplitChange x)
        (variableChangePointY E17toSplitChange x y) _) = _
  have hx : variableChangePointX E17toSplitChange x = 36 * x - 99 := by
    norm_num [variableChangePointX, E17toSplitChange]
    ring
  have hy : variableChangePointY E17toSplitChange x y =
      108 * (2 * y + x + 1) := by
    norm_num [variableChangePointY, E17toSplitChange]
    ring
  have hvar0 : WeierstrassCurve.Affine.Nonsingular
      (E17toSplitChange • E17Curve)
      (variableChangePointX E17toSplitChange x)
      (variableChangePointY E17toSplitChange x y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (variableChangePoint_equation E17Curve E17toSplitChange h0.1)
  have hvar : WeierstrassCurve.Affine.Nonsingular ESplitCurve
      (variableChangePointX E17toSplitChange x)
      (variableChangePointY E17toSplitChange x y) := by
    rw [← E17toSplitChange_curve]
    exact hvar0
  calc
    (curveEqAddEquiv E17toSplitChange_curve)
        (WeierstrassCurve.Affine.Point.some
          (variableChangePointX E17toSplitChange x)
          (variableChangePointY E17toSplitChange x y) _) =
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX E17toSplitChange x)
        (variableChangePointY E17toSplitChange x y) hvar :=
      curveEqAddEquiv_some E17toSplitChange_curve
    _ = WeierstrassCurve.Affine.Point.some
        (36 * x - 99) (108 * (2 * y + x + 1)) h1 := by
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩

/-! ## Two-adic separatedness on the good model -/

private theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 2 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

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

def E17DoubleDen (x y : ℚ) : ℚ := 2 * y + x + 1

def E17DoubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + x ^ 2 + 110 * x - 41

def E17DoubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 5 * x ^ 4 - 4 * x ^ 3 * y -
    276 * x ^ 3 + 2 * x ^ 2 * y + 152 * x ^ 2 - 108 * x * y -
    95 * x + 96 * y - 1485

private theorem E17_doubleX_formula {x y : ℚ}
    (hd : E17DoubleDen x y ≠ 0) (hE : OnE17 x y) :
    WeierstrassCurve.Affine.addX E17Curve x x
        (WeierstrassCurve.Affine.slope E17Curve x x y y) =
      E17DoubleXNum x / E17DoubleDen x y ^ 2 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
    intro h
    apply hd
    simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E17Curve x x y y =
      (3 * x ^ 2 - 2 * x - y - 1) / E17DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E17Curve, E17DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addX E17DoubleXNum
  simp only [E17Curve]
  unfold OnE17 at hE
  field_simp [hd]
  unfold E17DoubleDen
  linear_combination (3 - 8 * x) * hE

private theorem E17_doubleY_formula {x y : ℚ}
    (hd : E17DoubleDen x y ≠ 0) (hE : OnE17 x y) :
    WeierstrassCurve.Affine.addY E17Curve x x y
        (WeierstrassCurve.Affine.slope E17Curve x x y y) =
      E17DoubleYNum x y / E17DoubleDen x y ^ 3 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
    intro h
    apply hd
    simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E17Curve x x y y =
      (3 * x ^ 2 - 2 * x - y - 1) / E17DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E17Curve, E17DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E17DoubleYNum
  simp [E17Curve]
  unfold OnE17 at hE
  field_simp [hd]
  unfold E17DoubleDen
  linear_combination
    (28 * x ^ 3 - 19 * x ^ 2 - x - 8 * y ^ 2 - 15 * y + 106) * hE

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

private theorem E17DoubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (E17DoubleXNum x) = -8 * k := by
  have hshape : E17DoubleXNum x =
      x ^ 4 + [x ^ 2, 110 * x, (-41 : ℚ)].sum := by
    simp [E17DoubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hge := val_monomial_ge hx hy 1 (by norm_num) 2 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 110 (by norm_num) 1 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-41)
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega

private theorem E17DoubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (E17DoubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [(-2 : ℚ) * x ^ 5, (-1 : ℚ) * x ^ 4 * y, -5 * x ^ 4,
      -4 * x ^ 3 * y, -276 * x ^ 3, 2 * x ^ 2 * y,
      152 * x ^ 2, -108 * x * y, -95 * x, 96 * y, (-1485 : ℚ)]
  have hshape : E17DoubleYNum x y = x ^ 6 + l.sum := by
    simp [E17DoubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow hx, hvx]
    · have hge := val_monomial_ge hx hy (-2) (by norm_num) 5 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-5) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-4) (by norm_num) 3 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-276) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 2 (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 152 (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-108) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-95) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 96 (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-1485)
      norm_num at hge ⊢
      omega

/-- A point is in the formal kernel at `2` when its affine coordinates have
valuations `(-2k,-3k)` for some `k>0`. -/
def E17FormalAtTwo : E17Point → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

def E17FormalLevel : E17Point → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

theorem E17FormalAtTwo_iff (P : E17Point) :
    E17FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, E17FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [E17FormalAtTwo, E17FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

theorem E17FormalLevel_double {P : E17Point} {k : ℤ}
    (hP : E17FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ E17FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [E17FormalLevel] at hP
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
      by_cases hd : E17DoubleDen x y = 0
      · left
        rw [two_nsmul]
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvx1 : padicValRat 2 (x + 1) = -2 * k := by
          rw [val_add_eq_left_of_lt hx (by rw [hvx, padicValRat.one]; omega), hvx]
        have hvdenLower : 1 - 3 * k ≤ padicValRat 2 (E17DoubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y) (r := x + 1) (by simpa [E17DoubleDen, add_assoc] using hd)
          rw [hv2y, hvx1, min_eq_left (by omega)] at hmin
          simpa [E17DoubleDen, add_assoc] using hmin
        let k' : ℤ := 4 * k + padicValRat 2 (E17DoubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := E17DoubleXNum_val hx hy hk hvx
        have hvY := E17DoubleYNum_val hx hy hk hvx hvy
        have hN : E17DoubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : E17DoubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE : OnE17 x y := (E17Curve_equation_iff x y).mp h.1
        have hxform := E17_doubleX_formula hd hE
        have hyform := E17_doubleY_formula hd hE
        have hvx2 : padicValRat 2
              (WeierstrassCurve.Affine.addX E17Curve x x
                (WeierstrassCurve.Affine.slope E17Curve x x y y)) =
            -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow hd]
          dsimp [k']
          ring
        have hvy2 : padicValRat 2
              (WeierstrassCurve.Affine.addY E17Curve x x y
                (WeierstrassCurve.Affine.slope E17Curve x x y y)) =
            -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
          intro heq
          apply hd
          simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at heq ⊢
          linarith
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- At the good prime `2`, a rational point is integral or lies in the
formal kernel. -/
theorem E17_formal_or_integral (P : E17Point) :
    E17FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE : OnE17 x y := (E17Curve_equation_iff x y).mp h.1
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
          [x * y, (1 : ℚ) * y, -(x ^ 3), x ^ 2, (1 : ℚ) * x, (14 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnE17 at hE
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · rw [hx0, zero_mul, padicValRat.zero, hlead]
              omega
            · rw [padicValRat.mul hx0 hy, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · rw [one_mul, hlead]
            dsimp [vy] at hvyneg ⊢
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
            · rw [one_mul, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · have hge := val_int_nonneg 14
            rw [hlead]
            norm_num at hge ⊢
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
            [y ^ 2, x * y, (1 : ℚ) * y, x ^ 2, (1 : ℚ) * x, (14 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnE17 at hE
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
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
            · by_cases hy0 : y = 0
              · rw [hy0, mul_zero, padicValRat.zero, hlead]
                omega
              · rw [one_mul, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · rw [padicValRat.pow hx, hlead]
              dsimp [vx] at hvxneg ⊢
              omega
            · rw [one_mul, hlead]
              dsimp [vx] at hvxneg ⊢
              omega
            · have hge := val_int_nonneg 14
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval := val_add_list_eq l (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        have hleftne : y ^ 2 + x * y + y ≠ 0 := by
          intro hz
          let l : List ℚ := [x * y, (1 : ℚ) * y]
          have hgt : ∀ a ∈ l,
              padicValRat 2 (y ^ 2) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl
            · rw [padicValRat.pow hy, padicValRat.mul hx hy]
              dsimp [vx, vy] at hvylt ⊢
              omega
            · rw [one_mul, padicValRat.pow hy]
              dsimp [vy] at hvylt ⊢
              omega
          have hv := val_add_list_eq l (pow_ne_zero 2 hy) hgt
          rw [show y ^ 2 + l.sum = y ^ 2 + x * y + y by simp [l]; ring,
            hz, padicValRat.zero, padicValRat.pow hy] at hv
          dsimp [vy] at hvylt hv
          omega
        have hvleft : padicValRat 2 (y ^ 2 + x * y + y) = 2 * vy := by
          let l : List ℚ := [x * y, (1 : ℚ) * y]
          have hgt : ∀ a ∈ l,
              padicValRat 2 (y ^ 2) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl
            · rw [padicValRat.pow hy, padicValRat.mul hx hy]
              dsimp [vx, vy] at hvylt ⊢
              omega
            · rw [one_mul, padicValRat.pow hy]
              dsimp [vy] at hvylt ⊢
              omega
          calc
            padicValRat 2 (y ^ 2 + x * y + y) =
                padicValRat 2 (y ^ 2 + l.sum) := by
              congr 1
              simp [l]
              ring
            _ = padicValRat 2 (y ^ 2) :=
              val_add_list_eq l (pow_ne_zero 2 hy) hgt
            _ = 2 * vy := by rw [padicValRat.pow hy]; rfl
        let l : List ℚ := [-(x ^ 2), -x, (-14 : ℚ)]
        have hrightshape : x ^ 3 + l.sum = x ^ 3 - x ^ 2 - x - 14 := by
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
          · rw [padicValRat.pow hx, padicValRat.neg]
            dsimp [vx] at hvxneg ⊢
            omega
          · have hge := val_int_nonneg (-14)
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
        have hvright0 := val_add_list_eq l (pow_ne_zero 3 hx) hrightgt
        have hvright : padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) =
            3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y + y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) := by rw [hE]
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

private noncomputable def E17DoubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + x ^ 2 + 110 * x - 41

private noncomputable def E17DoubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 5 * x ^ 4 - 4 * x ^ 3 * y -
    276 * x ^ 3 + 2 * x ^ 2 * y + 152 * x ^ 2 - 108 * x * y -
    95 * x + 96 * y - 1485

private theorem E17DoubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((E17DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((E17DoubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + (x : ℚ_[2]) ^ 2 +
      110 * (x : ℚ_[2]) - 41 =
    (((x ^ 4 + x ^ 2 + 110 * x - 41 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E17DoubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((E17DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((E17DoubleYNum x y : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 6 - 2 * (x : ℚ_[2]) ^ 5 -
      (x : ℚ_[2]) ^ 4 * (y : ℚ_[2]) - 5 * (x : ℚ_[2]) ^ 4 -
      4 * (x : ℚ_[2]) ^ 3 * (y : ℚ_[2]) - 276 * (x : ℚ_[2]) ^ 3 +
      2 * (x : ℚ_[2]) ^ 2 * (y : ℚ_[2]) + 152 * (x : ℚ_[2]) ^ 2 -
      108 * (x : ℚ_[2]) * (y : ℚ_[2]) - 95 * (x : ℚ_[2]) +
      96 * (y : ℚ_[2]) - 1485 =
    (((x ^ 6 - 2 * x ^ 5 - x ^ 4 * y - 5 * x ^ 4 - 4 * x ^ 3 * y -
      276 * x ^ 3 + 2 * x ^ 2 * y + 152 * x ^ 2 - 108 * x * y -
      95 * x + 96 * y - 1485 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E17DoubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (E17DoubleXNum x) := by
  have hnorm := (E17DoubleXNumPadic (ratPadicInt x hx)).2
  change ‖((E17DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E17DoubleXNumPadic_coe x hx,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E17DoubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (E17DoubleYNum x y) := by
  have hnorm := (E17DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((E17DoubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E17DoubleYNumPadic_coe x y hx hy,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E17_padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE17 x y) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy +
        ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 - (ratPadicInt x hx) ^ 2 -
        ratPadicInt x hx - 14 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) + (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 - (x : ℚ_[2]) ^ 2 - (x : ℚ_[2]) - 14
  unfold OnE17 at hE
  exact_mod_cast hE

private theorem toZMod_nat (n : ℕ) :
    PadicInt.toZMod (n : ℤ_[2]) = (n : ZMod 2) := by
  exact map_natCast (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) n

@[simp] private theorem toZMod_2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_4 : PadicInt.toZMod (4 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_5 : PadicInt.toZMod (5 : ℤ_[2]) = 1 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_14 : PadicInt.toZMod (14 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_41 : PadicInt.toZMod (41 : ℤ_[2]) = 1 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_95 : PadicInt.toZMod (95 : ℤ_[2]) = 1 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_96 : PadicInt.toZMod (96 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_108 : PadicInt.toZMod (108 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_110 : PadicInt.toZMod (110 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_152 : PadicInt.toZMod (152 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_276 : PadicInt.toZMod (276 : ℤ_[2]) = 0 := by
  rw [map_ofNat]; decide
@[simp] private theorem toZMod_1485 : PadicInt.toZMod (1485 : ℤ_[2]) = 1 := by
  rw [map_ofNat]; decide

private theorem E17_y_red_one_of_x_red_one {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE17 x y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx) = 1) :
    PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (E17_padicInt_equation hx hy hE)
  simp [map_add, map_sub, map_mul, map_pow, hxred] at heq
  by_cases hy0 : PadicInt.toZMod (ratPadicInt y hy) = 0
  · rw [hy0] at heq
    norm_num at heq
  · exact zmod2_nonzero_eq_one _ hy0

private theorem E17DoubleXNumPadic_red
    {z : ℤ_[2]} :
    PadicInt.toZMod (E17DoubleXNumPadic z) = 1 := by
  have hz : PadicInt.toZMod z = 0 ∨ PadicInt.toZMod z = 1 := by
    by_cases hz0 : PadicInt.toZMod z = 0
    · exact Or.inl hz0
    · exact Or.inr (zmod2_nonzero_eq_one _ hz0)
  rcases hz with hz | hz <;>
    simp [E17DoubleXNumPadic, map_add, map_sub, map_mul, map_pow,
      hz]

private theorem E17DoubleYNumPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E17DoubleYNumPadic z w) = 1 := by
  simp [E17DoubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    hz]

private theorem E17DoubleYNumPadic_red_one_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (E17DoubleYNumPadic z w) = 1 := by
  simp [E17DoubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    hz, hw]

private theorem ratPadicInt_E17DoubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (E17DoubleXNum x) (E17DoubleXNum_integral x hx) =
      E17DoubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (E17DoubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_E17DoubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x)
    (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (E17DoubleYNum x y) (E17DoubleYNum_integral x y hx hy) =
      E17DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (E17DoubleYNumPadic_coe x y hx hy).symm

private theorem val_two : padicValRat 2 (2 : ℚ) = 1 :=
  padicValRat.self (by norm_num : 1 < 2)

private theorem E17_double_formal_of_integral_x_unit
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E17Curve x y}
    (hx : padicValRat 2 x = 0) (hy : 0 ≤ padicValRat 2 y) :
    E17FormalAtTwo
      (2 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := by omega
  have hE : OnE17 x y := (E17Curve_equation_iff x y).mp h.1
  have hxn : x ≠ 0 := by
    intro hzero
    rw [hzero] at hE
    unfold OnE17 at hE
    norm_num at hE
    nlinarith [sq_nonneg (2 * y + 1)]
  have hxred := ratPadicInt_red_eq_one_of_val_zero hxn hx
  have hyred := E17_y_red_one_of_x_red_one hx0 hy hE hxred
  have hyn : y ≠ 0 := by
    intro hzero
    have : ratPadicInt y hy = 0 := by
      apply Subtype.ext
      change (y : ℚ_[2]) = 0
      simp [hzero]
    rw [this, map_zero] at hyred
    norm_num at hyred
  have hvy : padicValRat 2 y = 0 := by
    apply val_zero_of_rational_padicInt_red_nonzero hyn hy
    rw [hyred]
    norm_num
  by_cases hd : E17DoubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = WeierstrassCurve.Affine.negY E17Curve x y := by
      simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at hd ⊢
      linarith
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hYeq]
    trivial
  · have hv2y : padicValRat 2 (2 * y) = 1 := by
      rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn, val_two, hvy]
      norm_num
    have hx1i : 0 ≤ padicValRat 2 (x + 1) := by
      by_cases hx1 : x + 1 = 0
      · simp [hx1]
      · have hmin := padicValRat.min_le_padicValRat_add (p := 2)
          (q := x) (r := 1) hx1
        rw [hx, padicValRat.one, min_self] at hmin
        exact hmin
    have hx1red : PadicInt.toZMod (ratPadicInt (x + 1) hx1i) = 0 := by
      have heq : ratPadicInt (x + 1) hx1i = ratPadicInt x hx0 + 1 := by
        apply Subtype.ext
        change ((x + 1 : ℚ) : ℚ_[2]) = (x : ℚ_[2]) + 1
        push_cast
        ring
      rw [heq, map_add, map_one, hxred]
      decide
    have hvd : 1 ≤ padicValRat 2 (E17DoubleDen x y) := by
      by_cases hx1 : x + 1 = 0
      · have hv2y' : 1 ≤ padicValRat 2 (2 * y) := by omega
        simpa [E17DoubleDen, add_assoc, hx1] using hv2y'
      · have hvx1 : 1 ≤ padicValRat 2 (x + 1) := by
          have := val_pos_of_rational_padicInt_red_zero hx1 hx1i hx1red
          omega
        have hmin := padicValRat.min_le_padicValRat_add (p := 2)
          (q := 2 * y) (r := x + 1) (by simpa [E17DoubleDen, add_assoc] using hd)
        have hmin1 : 1 ≤ min (padicValRat 2 (2 * y)) (padicValRat 2 (x + 1)) :=
          le_min (by omega) hvx1
        simpa [E17DoubleDen, add_assoc] using le_trans hmin1 hmin
    have hNi := E17DoubleXNum_integral x hx0
    have hYi := E17DoubleYNum_integral x y hx0 hy
    have hNred : PadicInt.toZMod
        (ratPadicInt (E17DoubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_E17DoubleXNum x hx0]
      exact E17DoubleXNumPadic_red
    have hYred : PadicInt.toZMod
        (ratPadicInt (E17DoubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_E17DoubleYNum x y hx0 hy]
      exact E17DoubleYNumPadic_red_one_one hxred hyred
    have hN : E17DoubleXNum x ≠ 0 := by
      intro hzero
      have : ratPadicInt (E17DoubleXNum x) hNi = 0 := by
        apply Subtype.ext
        change ((E17DoubleXNum x : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hNred
      norm_num at hNred
    have hY : E17DoubleYNum x y ≠ 0 := by
      intro hzero
      have : ratPadicInt (E17DoubleYNum x y) hYi = 0 := by
        apply Subtype.ext
        change ((E17DoubleYNum x y : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hYred
      norm_num at hYred
    have hvN : padicValRat 2 (E17DoubleXNum x) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hN hNi (by rw [hNred]; norm_num)
    have hvY : padicValRat 2 (E17DoubleYNum x y) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hY hYi (by rw [hYred]; norm_num)
    have hneg : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
      intro heq
      apply hd
      simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at heq ⊢
      linarith
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (E17DoubleDen x y), by omega, ?_, ?_⟩
    · rw [E17_doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN, padicValRat.pow hd]
      ring
    · rw [E17_doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY, padicValRat.pow hd]
      ring

private theorem E17_four_formal_of_integral_x_pos
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E17Curve x y}
    (hx : 0 < padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    E17FormalAtTwo
      (4 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := le_of_lt hx
  have hE : OnE17 x y := (E17Curve_equation_iff x y).mp h.1
  have hxn : x ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hx
    omega
  have hxred := ratPadicInt_red_eq_zero_of_val_pos hxn hx
  have hqval : 1 ≤ padicValRat 2 (2 * y + x) ∨ 2 * y + x = 0 := by
    by_cases hq : 2 * y + x = 0
    · exact Or.inr hq
    · left
      by_cases hyn : y = 0
      · have hx1 : 1 ≤ padicValRat 2 x := by omega
        simpa [hyn] using hx1
      · have hv2y : 1 ≤ padicValRat 2 (2 * y) := by
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn, val_two]
          omega
        have hmin := padicValRat.min_le_padicValRat_add (p := 2)
          (q := 2 * y) (r := x) hq
        have hmin1 : 1 ≤ min (padicValRat 2 (2 * y)) (padicValRat 2 x) :=
          le_min hv2y (by omega)
        exact le_trans hmin1 hmin
  have hd : E17DoubleDen x y ≠ 0 := by
    intro hzero
    have hqeq : 2 * y + x = -1 := by
      unfold E17DoubleDen at hzero
      linarith
    rcases hqval with hqval | hqzero
    · rw [hqeq, padicValRat.neg, padicValRat.one] at hqval
      omega
    · rw [hqzero] at hqeq
      norm_num at hqeq
  have hvd : padicValRat 2 (E17DoubleDen x y) = 0 := by
    rcases hqval with hqval | hqzero
    · have hv := val_add_eq_left_of_lt (a := (1 : ℚ)) (b := 2 * y + x)
          (by norm_num) (by rw [padicValRat.one]; omega)
      simpa [E17DoubleDen, add_comm, add_left_comm, add_assoc] using hv
    · simp [E17DoubleDen, hqzero]
  have hNi := E17DoubleXNum_integral x hx0
  have hYi := E17DoubleYNum_integral x y hx0 hy
  have hNred : PadicInt.toZMod
      (ratPadicInt (E17DoubleXNum x) hNi) = 1 := by
    rw [ratPadicInt_E17DoubleXNum x hx0]
    exact E17DoubleXNumPadic_red
  have hYred : PadicInt.toZMod
      (ratPadicInt (E17DoubleYNum x y) hYi) = 1 := by
    rw [ratPadicInt_E17DoubleYNum x y hx0 hy]
    exact E17DoubleYNumPadic_red_zero hxred
  have hN : E17DoubleXNum x ≠ 0 := by
    intro hzero
    have : ratPadicInt (E17DoubleXNum x) hNi = 0 := by
      apply Subtype.ext
      change ((E17DoubleXNum x : ℚ) : ℚ_[2]) = 0
      simp [hzero]
    rw [this, map_zero] at hNred
    norm_num at hNred
  have hY : E17DoubleYNum x y ≠ 0 := by
    intro hzero
    have : ratPadicInt (E17DoubleYNum x y) hYi = 0 := by
      apply Subtype.ext
      change ((E17DoubleYNum x y : ℚ) : ℚ_[2]) = 0
      simp [hzero]
    rw [this, map_zero] at hYred
    norm_num at hYred
  have hvN : padicValRat 2 (E17DoubleXNum x) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hN hNi (by rw [hNred]; norm_num)
  have hvY : padicValRat 2 (E17DoubleYNum x y) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hY hYi (by rw [hYred]; norm_num)
  have hneg : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
    intro heq
    apply hd
    simp [E17DoubleDen, E17Curve, WeierstrassCurve.Affine.negY] at heq ⊢
    linarith
  have hfour : 4 • WeierstrassCurve.Affine.Point.some x y h =
      2 • (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) := by
    rw [← two_nsmul]
    norm_num [← mul_nsmul]
  rw [hfour, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
  apply E17_double_formal_of_integral_x_unit
  · rw [E17_doubleX_formula hd hE,
      padicValRat.div hN (pow_ne_zero 2 hd), hvN,
      padicValRat.pow hd, hvd]
    norm_num
  · rw [E17_doubleY_formula hd hE,
      padicValRat.div hY (pow_ne_zero 3 hd), hvY,
      padicValRat.pow hd, hvd]
    norm_num

/-- Doubling preserves the formal kernel at two. -/
theorem E17FormalAtTwo_double {P : E17Point}
    (hP : E17FormalAtTwo P) : E17FormalAtTwo (2 • P) := by
  rw [E17FormalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases E17FormalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-- Four times every rational point lies in the formal kernel at two. -/
theorem E17_four_nsmul_formal (P : E17Point) :
    E17FormalAtTwo (4 • P) := by
  rcases E17_formal_or_integral P with hformal | hintegral
  · have h2 := E17FormalAtTwo_double hformal
    have h4 := E17FormalAtTwo_double h2
    rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]]
    exact h4
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hx, hy⟩
        by_cases hxunit : padicValRat 2 x = 0
        · have h2 := E17_double_formal_of_integral_x_unit (h := h) hxunit hy
          have h4 := E17FormalAtTwo_double h2
          rw [show 4 • WeierstrassCurve.Affine.Point.some x y h =
              2 • (2 • WeierstrassCurve.Affine.Point.some x y h) by
                norm_num [← mul_nsmul]]
          exact h4
        · have hxpos : 0 < padicValRat 2 x := lt_of_le_of_ne hx (Ne.symm hxunit)
          exact E17_four_formal_of_integral_x_pos (h := h) hxpos hy

private theorem E17FormalLevel_unique {P : E17Point} {k l : ℤ}
    (hk : E17FormalLevel P k) (hl : E17FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [E17FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

theorem E17FormalLevel_two_power {P : E17Point} {k : ℤ}
    (hP : E17FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + (n : ℤ) ≤ k' ∧
        E17FormalLevel ((2 ^ n : ℕ) • P) k' := by
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
      · rcases E17FormalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [hpow, hzero]
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rwa [hpow]

/-- The two-adic formal kernel contains no nonzero point divisible by every
power of two through formal points. -/
theorem E17_formal_separated (P : E17Point)
    (hP : E17FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : E17Point,
      E17FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, E17FormalLevel P k := by
    rw [E17FormalAtTwo_iff] at hP
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
  have hlevelQ : ∃ l : ℤ, E17FormalLevel Q l := by
    rw [E17FormalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x y h => exact hl.1
  rcases E17FormalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : E17FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := E17FormalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k :=
      Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat, heq] at hbound
    omega

/-- Weak descent and two-adic separatedness show that every point on the
split model is killed by four. -/
theorem ESplit_four_nsmul_eq_zero (P : ESplitPoint) : 4 • P = 0 := by
  let P0 : E17Point := E17SplitAddEquiv.symm P
  have hP0formal : E17FormalAtTwo (4 • P0) :=
    E17_four_nsmul_formal P0
  have hdiv : ∀ n : ℕ, ∃ Q0 : E17Point,
      E17FormalAtTwo Q0 ∧
        4 • P0 = (2 ^ n : ℕ) • Q0 := by
    intro n
    obtain ⟨Q, hQ⟩ := ESplit_four_nsmul_two_power_divisible P n
    refine ⟨4 • E17SplitAddEquiv.symm Q,
      E17_four_nsmul_formal (E17SplitAddEquiv.symm Q), ?_⟩
    have hm := congrArg E17SplitAddEquiv.symm hQ
    simpa only [map_nsmul, AddEquiv.symm_apply_apply, P0] using hm
  have hzero : 4 • P0 = 0 :=
    E17_formal_separated (4 • P0) hP0formal hdiv
  have hm := congrArg E17SplitAddEquiv hzero
  simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, P0] using hm

theorem E17_four_nsmul_eq_zero (P : E17Point) : 4 • P = 0 := by
  have h := ESplit_four_nsmul_eq_zero (E17SplitAddEquiv P)
  have hm := congrArg E17SplitAddEquiv.symm h
  simpa only [map_nsmul, AddEquiv.symm_apply_apply, map_zero] using hm

private theorem E17_affine_two_torsion_coordinates
    {x y : ℚ} {hns : WeierstrassCurve.Affine.Nonsingular E17Curve x y}
    (hE : OnE17 x y)
    (h2 : 2 • (WeierstrassCurve.Affine.Point.some x y hns : E17Point) = 0) :
    x = 11 / 4 ∧ y = -15 / 8 := by
  have hadd :
      (WeierstrassCurve.Affine.Point.some x y hns : E17Point) +
        WeierstrassCurve.Affine.Point.some x y hns = 0 := by
    simpa only [two_nsmul] using h2
  have hneg := eq_neg_of_add_eq_zero_left hadd
  rw [WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hneg
  have hyneg := hneg.2
  simp [E17Curve, WeierstrassCurve.Affine.negY] at hyneg
  have hden : 2 * y + x + 1 = 0 := by linarith
  have hfactor : (4 * x - 11) * (x ^ 2 + 2 * x + 5) = 0 := by
    unfold OnE17 at hE
    linear_combination (2 * y + x + 1) * hden - 4 * hE
  have hquad : 0 < x ^ 2 + 2 * x + 5 := by
    nlinarith [sq_nonneg (x + 1)]
  have hx : x = 11 / 4 := by
    rcases mul_eq_zero.mp hfactor with hx | hx
    · norm_num at hx ⊢
      linarith
    · nlinarith
  refine ⟨hx, ?_⟩
  rw [hx] at hden
  norm_num at hden ⊢
  linarith

/-- The affine rational points on `X₀(17)` are exactly the three nonzero
points of its rational cyclic subgroup of order four. -/
theorem affine_rational_points {x y : ℚ} (hE : OnE17 x y) :
    (x = 7 ∧ y = 13) ∨
      (x = 11 / 4 ∧ y = -15 / 8) ∨
      (x = 7 ∧ y = -21) := by
  have hns : WeierstrassCurve.Affine.Nonsingular E17Curve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E17Curve_equation_iff x y).mpr hE)
  let P : E17Point := WeierstrassCurve.Affine.Point.some x y hns
  have h4 : 4 • P = 0 := E17_four_nsmul_eq_zero P
  have hQ2 : 2 • (2 • P) = 0 := by
    simpa only [← mul_nsmul, show 2 * 2 = 4 by norm_num] using h4
  generalize hQeq : 2 • P = Q at hQ2
  cases Q with
  | zero =>
      have hxy := E17_affine_two_torsion_coordinates hE hQeq
      exact Or.inr (Or.inl hxy)
  | some X Y hQ =>
      have hQE : OnE17 X Y := (E17Curve_equation_iff X Y).mp hQ.1
      have hQxy := E17_affine_two_torsion_coordinates hQE hQ2
      have hd : E17DoubleDen x y ≠ 0 := by
        intro hd
        have hzero : 2 • P = 0 := by
          rw [two_nsmul]
          apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
          simp [E17DoubleDen, E17Curve,
            WeierstrassCurve.Affine.negY] at hd ⊢
          linarith
        rw [hzero] at hQeq
        exact WeierstrassCurve.Affine.Point.some_ne_zero hQ hQeq.symm
      have hyne : y ≠ WeierstrassCurve.Affine.negY E17Curve x y := by
        intro hy
        apply hd
        simp [E17DoubleDen, E17Curve,
          WeierstrassCurve.Affine.negY] at hy ⊢
        linarith
      have hdouble := hQeq
      rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne,
        WeierstrassCurve.Affine.Point.some.injEq] at hdouble
      have hxdouble := hdouble.1
      rw [E17_doubleX_formula hd hE, hQxy.1] at hxdouble
      have hxpoly := hxdouble
      field_simp [hd] at hxpoly
      have hfactor : (x - 7) ^ 2 * (2 * x + 3) ^ 2 = 0 := by
        unfold E17DoubleXNum E17DoubleDen at hxpoly
        unfold OnE17 at hE
        linear_combination hxpoly + 44 * hE
      have hxcase : x = 7 ∨ x = -3 / 2 := by
        rcases mul_eq_zero.mp hfactor with hx | hx
        · left
          have := sq_eq_zero_iff.mp hx
          linarith
        · right
          have := sq_eq_zero_iff.mp hx
          norm_num at this ⊢
          linarith
      have hx : x = 7 := by
        rcases hxcase with hx | hx
        · exact hx
        · have hDsq : E17DoubleDen x y ^ 2 =
              (4 * x - 11) * (x ^ 2 + 2 * x + 5) := by
            unfold OnE17 at hE
            unfold E17DoubleDen
            linear_combination 4 * hE
          rw [hx] at hDsq
          norm_num at hDsq
          exfalso
          nlinarith [sq_nonneg (E17DoubleDen (-3 / 2) y)]
      have hyfactor : (y - 13) * (y + 21) = 0 := by
        have hE' := hE
        rw [hx] at hE'
        unfold OnE17 at hE'
        norm_num at hE'
        nlinarith
      rcases mul_eq_zero.mp hyfactor with hy | hy
      · left
        constructor
        · exact hx
        · linarith
      · right
        right
        constructor
        · exact hx
        · linarith

private theorem E17_nonsingular_7_13 :
    WeierstrassCurve.Affine.Nonsingular E17Curve 7 13 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((E17Curve_equation_iff 7 13).mpr (by norm_num [OnE17]))

private theorem E17_nonsingular_11_4_neg15_8 :
    WeierstrassCurve.Affine.Nonsingular E17Curve (11 / 4) (-15 / 8) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((E17Curve_equation_iff (11 / 4) (-15 / 8)).mpr (by norm_num [OnE17]))

private theorem E17_nonsingular_7_neg21 :
    WeierstrassCurve.Affine.Nonsingular E17Curve 7 (-21) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((E17Curve_equation_iff 7 (-21)).mpr (by norm_num [OnE17]))

def E17Generator : E17Point :=
  WeierstrassCurve.Affine.Point.some 7 13 E17_nonsingular_7_13

def E17TwoTorsion : E17Point :=
  WeierstrassCurve.Affine.Point.some (11 / 4) (-15 / 8)
    E17_nonsingular_11_4_neg15_8

def E17GeneratorNeg : E17Point :=
  WeierstrassCurve.Affine.Point.some 7 (-21) E17_nonsingular_7_neg21

/-- The complete list of rational points on `X₀(17)`. -/
theorem rational_points (P : E17Point) :
    P = 0 ∨ P = E17Generator ∨ P = E17TwoTorsion ∨ P = E17GeneratorNeg := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
      have hE : OnE17 x y := (E17Curve_equation_iff x y).mp h.1
      rcases affine_rational_points hE with hxy | hxy | hxy
      · rcases hxy with ⟨rfl, rfl⟩
        right
        left
        rw [E17Generator, WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨rfl, rfl⟩
      · rcases hxy with ⟨rfl, rfl⟩
        right
        right
        left
        rw [E17TwoTorsion, WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨rfl, rfl⟩
      · rcases hxy with ⟨rfl, rfl⟩
        right
        right
        right
        rw [E17GeneratorNeg, WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨rfl, rfl⟩

/-- The displayed generator has exact order four. -/
theorem E17Generator_exact_order_four :
    4 • E17Generator = 0 ∧ 2 • E17Generator ≠ 0 := by
  constructor
  · exact E17_four_nsmul_eq_zero E17Generator
  · intro h2
    have hxy := E17_affine_two_torsion_coordinates
      (hns := E17_nonsingular_7_13) (by norm_num [OnE17]) h2
    norm_num at hxy

end

end MazurProof.RationalPointsX017
