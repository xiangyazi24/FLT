import FLT.Assumptions.MazurProof.RationalPointsN15Descent

/-!
# The concrete two-isogeny on the order-15 genus-one model

This file realizes the two rational maps used by
`RationalPointsN15Descent` as total maps on the rational points of the
elliptic curves

`E  : y^2 = x^3 + 17*x^2 + 16*x`,
`E' : y^2 = x^3 - 34*x^2 + 225*x`.

The point at infinity and the respective kernel point `(0,0)` are handled
explicitly.  The two total maps are proved to compose to doubling on every
rational point.  This removes the rational-map and exceptional-point part of
the geometric boundary in the abstract exact-sequence layer.
-/

namespace MazurProof.RationalPointsN15Isogeny

open RationalPointsN15Descent
open WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

/-! ## The two elliptic curves -/

def fullTwoCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 17
  a₃ := 0
  a₄ := 16
  a₆ := 0

def isogenousCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -34
  a₃ := 0
  a₄ := 225
  a₆ := 0

theorem fullTwoCurve_delta : fullTwoCurve.Δ = (921600 : ℚ) := by
  norm_num [fullTwoCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem isogenousCurve_delta : isogenousCurve.Δ = (207360000 : ℚ) := by
  norm_num [isogenousCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance fullTwoCurve_isElliptic : fullTwoCurve.IsElliptic where
  isUnit := by rw [fullTwoCurve_delta]; norm_num

instance isogenousCurve_isElliptic : isogenousCurve.IsElliptic where
  isUnit := by rw [isogenousCurve_delta]; norm_num

@[simp] theorem fullTwoCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation fullTwoCurve x y ↔
      FullTwoEquation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold FullTwoEquation
  simp [fullTwoCurve]
  ring_nf

@[simp] theorem isogenousCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation isogenousCurve x y ↔
      IsogenousEquation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold IsogenousEquation
  simp [isogenousCurve]
  ring_nf

abbrev FullTwoPoint := WeierstrassCurve.Affine.Point fullTwoCurve
abbrev IsogenousPoint := WeierstrassCurve.Affine.Point isogenousCurve

/-! ## Affine formulae -/

def forwardX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2
def forwardY (x y : ℚ) : ℚ := y * (16 - x ^ 2) / x ^ 2

def dualX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4
def dualY (x y : ℚ) : ℚ := y * (225 - x ^ 2) / x ^ 2 / 8

theorem forward_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation fullTwoCurve x y) :
    WeierstrassCurve.Affine.Equation isogenousCurve
      (forwardX x y) (forwardY x y) := by
  rw [isogenousCurve_equation_iff]
  exact to_isogenous_curve hx ((fullTwoCurve_equation_iff x y).mp h)

theorem dual_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation isogenousCurve x y) :
    WeierstrassCurve.Affine.Equation fullTwoCurve
      (dualX x y) (dualY x y) := by
  rw [fullTwoCurve_equation_iff]
  exact from_isogenous_curve hx ((isogenousCurve_equation_iff x y).mp h)

/-! ## Total point maps -/

noncomputable def forwardPoint : FullTwoPoint → IsogenousPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (forward_equation hx (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

noncomputable def dualPoint : IsogenousPoint → FullTwoPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (dual_equation hx (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

@[simp] theorem forwardPoint_zero : forwardPoint 0 = 0 := rfl
@[simp] theorem dualPoint_zero : dualPoint 0 = 0 := rfl

@[simp] theorem forwardPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y)
    (hx : x = 0) :
    forwardPoint (.some x y h) = 0 := by
  rw [forwardPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] theorem dualPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular isogenousCurve x y)
    (hx : x = 0) :
    dualPoint (.some x y h) = 0 := by
  rw [dualPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

theorem forwardPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y)
    (hx : x ≠ 0) :
    forwardPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [forwardPoint, hx]

theorem dualPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular isogenousCurve x y)
    (hx : x ≠ 0) :
    dualPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [dualPoint, hx]

/-! ## Coordinate composition identities -/

@[simp] theorem fullTwoCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY fullTwoCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, fullTwoCurve]

@[simp] theorem isogenousCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY isogenousCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, isogenousCurve]

private def fullTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 34 * x + 16) / (2 * y)

private def isogenousTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 68 * x + 225) / (2 * y)

private def tangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

private def tangentY (a₂ x y m : ℚ) : ℚ :=
  -(m * (tangentX a₂ x m - x) + y)

theorem dual_forward_x {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : FullTwoEquation x y) :
    dualX (forwardX x y) (forwardY x y) =
      tangentX 17 x (fullTangent x y) := by
  unfold dualX forwardX forwardY tangentX fullTangent
  unfold FullTwoEquation at h
  field_simp [hx, hy]
  rw [h]
  ring

theorem dual_forward_y {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : FullTwoEquation x y) :
    dualY (forwardX x y) (forwardY x y) =
      tangentY 17 x y (fullTangent x y) := by
  unfold dualY forwardX forwardY tangentY tangentX fullTangent
  unfold FullTwoEquation at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x + 1) * (x + 16)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x * (x + 1) * (x + 16)) ^ 2 := by rw [h]
  rw [hy4]
  rw [h]
  ring

theorem forward_dual_x {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : IsogenousEquation x y) :
    forwardX (dualX x y) (dualY x y) =
      tangentX (-34) x (isogenousTangent x y) := by
  unfold forwardX dualX dualY tangentX isogenousTangent
  unfold IsogenousEquation at h
  field_simp [hx, hy]
  rw [h]
  ring

theorem forward_dual_y {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : IsogenousEquation x y) :
    forwardY (dualX x y) (dualY x y) =
      tangentY (-34) x y (isogenousTangent x y) := by
  unfold forwardY dualX dualY tangentY tangentX isogenousTangent
  unfold IsogenousEquation at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x - 9) * (x - 25)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x * (x - 9) * (x - 25)) ^ 2 := by rw [h]
  rw [hy4]
  rw [h]
  ring

/-! ## Identification with the affine group law -/

theorem fullTwoCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope fullTwoCurve x x y y =
      fullTangent x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY fullTwoCurve x y := by
    intro h
    apply hy
    rw [fullTwoCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [fullTwoCurve, fullTangent, WeierstrassCurve.Affine.negY]
  ring

theorem isogenousCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope isogenousCurve x x y y =
      isogenousTangent x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY isogenousCurve x y := by
    intro h
    apply hy
    rw [isogenousCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [isogenousCurve, isogenousTangent, WeierstrassCurve.Affine.negY]
  ring

theorem fullTwoCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX fullTwoCurve x x (fullTangent x y) =
      tangentX 17 x (fullTangent x y) := by
  simp [fullTwoCurve, tangentX]
  ring

theorem isogenousCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX isogenousCurve x x (isogenousTangent x y) =
      tangentX (-34) x (isogenousTangent x y) := by
  simp [isogenousCurve, tangentX]
  ring

theorem fullTwoCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY fullTwoCurve x x y (fullTangent x y) =
      tangentY 17 x y (fullTangent x y) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    tangentY tangentX fullTwoCurve
  ring

theorem isogenousCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY isogenousCurve x x y (isogenousTangent x y) =
      tangentY (-34) x y (isogenousTangent x y) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    tangentY tangentX isogenousCurve
  ring

private theorem fullTwo_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y)
    (hx : x = 0) : y = 0 := by
  have heq : FullTwoEquation x y :=
    (fullTwoCurve_equation_iff x y).mp h.1
  unfold FullTwoEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem isogenous_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular isogenousCurve x y)
    (hx : x = 0) : y = 0 := by
  have heq : IsogenousEquation x y :=
    (isogenousCurve_equation_iff x y).mp h.1
  unfold IsogenousEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem fullTwo_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular fullTwoCurve x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : FullTwoPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, fullTwoCurve])

private theorem isogenous_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular isogenousCurve x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : IsogenousPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, isogenousCurve])

private theorem fullTwo_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY fullTwoCurve x y := by
  intro h
  apply hy
  rw [fullTwoCurve_negY] at h
  linarith

private theorem isogenous_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY isogenousCurve x y := by
  intro h
  apply hy
  rw [isogenousCurve_negY] at h
  linarith

/-- The dual map after the forward map is multiplication by two, including
the point at infinity and all affine kernel points. -/
theorem dual_comp_forwardPoint (P : FullTwoPoint) :
    dualPoint (forwardPoint P) = 2 • P := by
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
          change dualPoint
              (.some (forwardX x y) (forwardY x y) _) = _
          rw [dualPoint_some_of_x_eq_zero _ hfx]
          exact (fullTwo_double_eq_zero_of_y_zero h hy).symm
        · have hfx : forwardX x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          change dualPoint
              (.some (forwardX x y) (forwardY x y) _) = _
          rw [dualPoint_some_of_x_ne_zero _ hfx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (fullTwo_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (dualX (forwardX x y) (forwardY x y))
              (dualY (forwardX x y) (forwardY x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX fullTwoCurve x x
                (WeierstrassCurve.Affine.slope fullTwoCurve x x y y))
              (WeierstrassCurve.Affine.addY fullTwoCurve x x y
                (WeierstrassCurve.Affine.slope fullTwoCurve x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : FullTwoEquation x y :=
            (fullTwoCurve_equation_iff x y).mp h.1
          constructor
          · rw [dual_forward_x hx hy heq, fullTwoCurve_slope_self hy,
              fullTwoCurve_addX_tangent]
          · rw [dual_forward_y hx hy heq, fullTwoCurve_slope_self hy,
              fullTwoCurve_addY_tangent]

/-- The forward map after the dual map is multiplication by two, including
the point at infinity and all affine kernel points. -/
theorem forward_comp_dualPoint (P : IsogenousPoint) :
    forwardPoint (dualPoint P) = 2 • P := by
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
          change forwardPoint (.some (dualX x y) (dualY x y) _) = _
          rw [forwardPoint_some_of_x_eq_zero _ hdx]
          exact (isogenous_double_eq_zero_of_y_zero h hy).symm
        · have hdx : dualX x y ≠ 0 := by
            exact div_ne_zero
              (div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx))
              (by norm_num)
          change forwardPoint (.some (dualX x y) (dualY x y) _) = _
          rw [forwardPoint_some_of_x_ne_zero _ hdx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (isogenous_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (forwardX (dualX x y) (dualY x y))
              (forwardY (dualX x y) (dualY x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX isogenousCurve x x
                (WeierstrassCurve.Affine.slope isogenousCurve x x y y))
              (WeierstrassCurve.Affine.addY isogenousCurve x x y
                (WeierstrassCurve.Affine.slope isogenousCurve x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : IsogenousEquation x y :=
            (isogenousCurve_equation_iff x y).mp h.1
          constructor
          · rw [forward_dual_x hx hy heq, isogenousCurve_slope_self hy,
              isogenousCurve_addX_tangent]
          · rw [forward_dual_y hx hy heq, isogenousCurve_slope_self hy,
              isogenousCurve_addY_tangent]

/-! ## Kernel and negation behavior -/

theorem forwardPoint_neg (P : FullTwoPoint) :
    forwardPoint (-P) = -forwardPoint P := by
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
            (forwardX x (WeierstrassCurve.Affine.negY fullTwoCurve x y))
            (forwardY x (WeierstrassCurve.Affine.negY fullTwoCurve x y)) _ =
          -WeierstrassCurve.Affine.Point.some
            (forwardX x y) (forwardY x y) _
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [forwardX, fullTwoCurve]
        · simp [forwardY, fullTwoCurve, isogenousCurve]
          ring

theorem dualPoint_neg (P : IsogenousPoint) :
    dualPoint (-P) = -dualPoint P := by
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
            (dualX x (WeierstrassCurve.Affine.negY isogenousCurve x y))
            (dualY x (WeierstrassCurve.Affine.negY isogenousCurve x y)) _ =
          -WeierstrassCurve.Affine.Point.some
            (dualX x y) (dualY x y) _
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · simp [dualX, isogenousCurve]
        · simp [dualY, isogenousCurve, fullTwoCurve]
          ring

def fullKernel : FullTwoPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((fullTwoCurve_equation_iff 0 0).mpr (by simp [FullTwoEquation]))

def isogenousKernel : IsogenousPoint :=
  WeierstrassCurve.Affine.Point.mk
    ((isogenousCurve_equation_iff 0 0).mpr (by simp [IsogenousEquation]))

@[simp] theorem forwardPoint_fullKernel : forwardPoint fullKernel = 0 := by
  rfl

@[simp] theorem dualPoint_isogenousKernel : dualPoint isogenousKernel = 0 := by
  rfl

theorem fullKernel_ne_zero : fullKernel ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem isogenousKernel_ne_zero : isogenousKernel ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

@[simp] theorem two_nsmul_fullKernel : 2 • fullKernel = 0 := by
  exact fullTwo_double_eq_zero_of_y_zero _ rfl

@[simp] theorem two_nsmul_isogenousKernel : 2 • isogenousKernel = 0 := by
  exact isogenous_double_eq_zero_of_y_zero _ rfl

theorem forwardPoint_eq_zero_iff (P : FullTwoPoint) :
    forwardPoint P = 0 ↔ P = 0 ∨ P = fullKernel := by
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
          rfl
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

theorem dualPoint_eq_zero_iff (P : IsogenousPoint) :
    dualPoint P = 0 ↔ P = 0 ∨ P = isogenousKernel := by
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
          rfl
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
    Function.comp dualPoint forwardPoint = fun P : FullTwoPoint => 2 • P := by
  funext P
  exact dual_comp_forwardPoint P

theorem forward_comp_dualPoint_fun :
    Function.comp forwardPoint dualPoint = fun P : IsogenousPoint => 2 • P := by
  funext P
  exact forward_comp_dualPoint P

end MazurProof.RationalPointsN15Isogeny
