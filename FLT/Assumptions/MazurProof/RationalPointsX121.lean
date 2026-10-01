import FLT.Assumptions.MazurProof.TateOrder18
import FLT.Assumptions.MazurProof.RationalPointsN15Descent
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Rational points on the order-21 quotient

This file proves the rational-point calculation needed for the cyclic
order-21 exclusion.  The first section records the explicit quotient of the
affine curve cut out by the order-three division polynomial and its map to

`E₀ : y² + x*y = x³ - 4*x - 1`.

The arithmetic descent and the finite-fibre calculation are developed below
these algebraic certificates.
-/

namespace MazurProof.RationalPointsX121

noncomputable section

/-! ## The affine order-21 curve and its diamond quotient -/

/-- The third-division equation on the Kubert order-seven family. -/
def G21 (t X : ℚ) : ℚ :=
  3 * X ^ 4
    + (t ^ 4 - 6 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * X ^ 3
    + (3 * t ^ 5 - 6 * t ^ 4 + 3 * t ^ 2) * X ^ 2
    + (3 * t ^ 6 - 6 * t ^ 5 + 3 * t ^ 4) * X
    - t ^ 9 + 3 * t ^ 8 - 3 * t ^ 7 + t ^ 6

/-- The completed-square equation on the same Tate family. -/
def D21 (t X : ℚ) : ℚ :=
  4 * X ^ 3
    + (t ^ 4 - 6 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * X ^ 2
    + (2 * t ^ 5 - 4 * t ^ 4 + 2 * t ^ 2) * X
    + t ^ 6 - 2 * t ^ 5 + t ^ 4

def q7 (t : ℚ) : ℚ := t ^ 2 - t + 1

def sigmaT (t : ℚ) : ℚ := (t - 1) / t

def sigmaX (t X : ℚ) : ℚ :=
  (X - t ^ 2 * (t - 1)) / t ^ 4

def s21 (t : ℚ) : ℚ :=
  (t ^ 3 - 3 * t + 1) / (t * (t - 1))

def r21 (t X : ℚ) : ℚ :=
  ((t ^ 2 - t + 1) * X - t ^ 2 * (t - 1)) /
    (t ^ 2 * (t - 1) ^ 2)

def R21 (s r : ℚ) : ℚ :=
  3 * r ^ 4 + (s ^ 2 - 7 * s + 9) * r ^ 3
    + 6 * (s - 3) * r ^ 2 + 12 * r - s

def w21 (s r : ℚ) : ℚ :=
  (2 * r ^ 3 * s - 7 * r ^ 3 + 6 * r ^ 2 - 1) /
    (r ^ 2 - r + 1)

def e21x (r : ℚ) : ℚ := -3 * r - 1

def e21y (s r : ℚ) : ℚ :=
  (3 * w21 s r + 3 * r + 1) / 2

def OnE21 (x y : ℚ) : Prop :=
  y ^ 2 + x * y = x ^ 3 - 4 * x - 1

theorem sigmaT_ne_zero {t : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    sigmaT t ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr ht1) ht0

theorem sigmaT_ne_one {t : ℚ} (ht0 : t ≠ 0) : sigmaT t ≠ 1 := by
  intro h
  dsimp [sigmaT] at h
  field_simp [ht0] at h
  linarith

theorem sigmaT_three (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    sigmaT (sigmaT (sigmaT t)) = t := by
  dsimp [sigmaT]
  field_simp [ht0, ht1]
  ring

theorem s21_sigma (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    s21 (sigmaT t) = s21 t := by
  dsimp [s21, sigmaT]
  field_simp [ht0, ht1]
  ring

theorem r21_sigma (t X : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    r21 (sigmaT t) (sigmaX t X) = r21 t X := by
  dsimp [r21, sigmaT, sigmaX]
  field_simp [ht0, ht1]
  ring

theorem G21_sigma (t X : ℚ) (ht0 : t ≠ 0) :
    t ^ 16 * G21 (sigmaT t) (sigmaX t X) = G21 t X := by
  dsimp [G21, sigmaT, sigmaX]
  field_simp [ht0]
  ring

theorem s21_cubic (t : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    t ^ 3 - s21 t * t ^ 2 + (s21 t - 3) * t + 1 = 0 := by
  dsimp [s21]
  field_simp [ht0, ht1]
  ring

/-- Cleared-denominator certificate for the degree-three quotient. -/
theorem quotient_certificate (t X : ℚ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    t ^ 8 * (t - 1) ^ 8 * R21 (s21 t) (r21 t X) =
      q7 t ^ 4 * G21 t X := by
  dsimp [s21, r21, R21, q7, G21]
  field_simp [ht0, ht1]
  ring

theorem quadDen_ne (r : ℚ) : r ^ 2 - r + 1 ≠ 0 := by
  intro h
  nlinarith [sq_nonneg (2 * r - 1)]

/-- Cleared-denominator certificate for the double-cover coordinate. -/
theorem w_certificate (s r : ℚ) :
    (r ^ 2 - r + 1) ^ 2 *
        (w21 s r ^ 2 + (r + 1) * (3 * r - 1) * (4 * r + 1)) =
      4 * r ^ 3 * R21 s r := by
  let d : ℚ := r ^ 2 - r + 1
  let n : ℚ := 2 * r ^ 3 * s - 7 * r ^ 3 + 6 * r ^ 2 - 1
  have hd : d ≠ 0 := by
    exact quadDen_ne r
  change d ^ 2 * ((n / d) ^ 2 +
      (r + 1) * (3 * r - 1) * (4 * r + 1)) =
    4 * r ^ 3 *
      (3 * r ^ 4 + (s ^ 2 - 7 * s + 9) * r ^ 3 +
        6 * (s - 3) * r ^ 2 + 12 * r - s)
  rw [mul_add]
  have hcancel : d ^ 2 * (n / d) ^ 2 = n ^ 2 := by
    field_simp [hd]
  rw [hcancel]
  dsimp [d, n]
  ring

/-- The quotient curve maps to the conductor-21 curve
`y² + x*y = x³ - 4*x - 1`. -/
theorem map_to_E21 (s r : ℚ) (hR : R21 s r = 0) :
    OnE21 (e21x r) (e21y s r) := by
  have hw := w_certificate s r
  rw [hR, mul_zero] at hw
  have hw0 :
      w21 s r ^ 2 + (r + 1) * (3 * r - 1) * (4 * r + 1) = 0 := by
    exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero 2 (quadDen_ne r))
  unfold OnE21 e21x e21y
  linear_combination (9 / 4 : ℚ) * hw0

/-! ## The conductor-21 curve and its explicit two-isogeny -/

def E21Curve : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -4
  a₆ := -1

def E1Curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 25
  a₃ := 0
  a₄ := 144
  a₆ := 0

def E2Curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -50
  a₃ := 0
  a₄ := 49
  a₆ := 0

theorem E21Curve_delta : E21Curve.Δ = (3969 : ℚ) := by
  norm_num [E21Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E1Curve_delta : E1Curve.Δ = (16257024 : ℚ) := by
  norm_num [E1Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E2Curve_delta : E2Curve.Δ = (88510464 : ℚ) := by
  norm_num [E2Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E21Curve_isElliptic : E21Curve.IsElliptic where
  isUnit := by rw [E21Curve_delta]; norm_num

instance E1Curve_isElliptic : E1Curve.IsElliptic where
  isUnit := by rw [E1Curve_delta]; norm_num

instance E2Curve_isElliptic : E2Curve.IsElliptic where
  isUnit := by rw [E2Curve_delta]; norm_num

def OnE1 (u W : ℚ) : Prop :=
  W ^ 2 = u * (u + 9) * (u + 16)

def OnE2 (v V : ℚ) : Prop :=
  V ^ 2 = v * (v - 1) * (v - 49)

@[simp] theorem E21Curve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E21Curve x y ↔ OnE21 x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E21Curve, OnE21]
  ring_nf

@[simp] theorem E1Curve_equation_iff (u W : ℚ) :
    WeierstrassCurve.Affine.Equation E1Curve u W ↔ OnE1 u W := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E1Curve, OnE1]
  ring_nf

@[simp] theorem E2Curve_equation_iff (v V : ℚ) :
    WeierstrassCurve.Affine.Equation E2Curve v V ↔ OnE2 v V := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E2Curve, OnE2]
  ring_nf

abbrev E21Point := WeierstrassCurve.Affine.Point E21Curve
abbrev E1Point := WeierstrassCurve.Affine.Point E1Curve
abbrev E2Point := WeierstrassCurve.Affine.Point E2Curve

theorem to_E1_equation {x y : ℚ} (h : OnE21 x y) :
    OnE1 (4 * (x - 2)) (4 * (2 * y + x)) := by
  unfold OnE21 at h
  unfold OnE1
  linear_combination 64 * h

theorem from_E1_equation {u W : ℚ} (h : OnE1 u W) :
    OnE21 (u / 4 + 2) (W / 8 - u / 8 - 1) := by
  unfold OnE1 at h
  unfold OnE21
  linear_combination (1 / 64 : ℚ) * h

/-- The degree-two isogeny `E₁ → E₂` away from its kernel. -/
def phiX (u W : ℚ) : ℚ := W ^ 2 / u ^ 2

def phiY (u W : ℚ) : ℚ := W * (144 - u ^ 2) / u ^ 2

/-- The dual isogeny `E₂ → E₁` away from its kernel. -/
def dualX (v V : ℚ) : ℚ := V ^ 2 / (4 * v ^ 2)

def dualY (v V : ℚ) : ℚ := V * (49 - v ^ 2) / (8 * v ^ 2)

theorem phi_on_curve {u W : ℚ} (hu : u ≠ 0) (h : OnE1 u W) :
    OnE2 (phiX u W) (phiY u W) := by
  unfold OnE1 at h
  unfold OnE2 phiX phiY
  field_simp [hu]
  rw [h]
  ring

theorem dual_on_curve {v V : ℚ} (hv : v ≠ 0) (h : OnE2 v V) :
    OnE1 (dualX v V) (dualY v V) := by
  unfold OnE2 at h
  unfold OnE1 dualX dualY
  field_simp [hv]
  rw [h]
  ring

/-! ### Total point maps -/

noncomputable def phiPoint : E1Point → E2Point
  | .zero => .zero
  | .some u _W h =>
      if hu : u = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E2Curve_equation_iff _ _ |>.2 <|
          phi_on_curve hu (E1Curve_equation_iff _ _ |>.1 h.1))

noncomputable def dualPoint : E2Point → E1Point
  | .zero => .zero
  | .some v _V h =>
      if hv : v = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E1Curve_equation_iff _ _ |>.2 <|
          dual_on_curve hv (E2Curve_equation_iff _ _ |>.1 h.1))

@[simp] theorem phiPoint_zero : phiPoint 0 = 0 := rfl

@[simp] theorem dualPoint_zero : dualPoint 0 = 0 := rfl

@[simp] theorem phiPoint_some_of_x_eq_zero {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hu : u = 0) :
    phiPoint (.some u W h) = 0 := by
  rw [phiPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] theorem dualPoint_some_of_x_eq_zero {v V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E2Curve v V)
    (hv : v = 0) :
    dualPoint (.some v V h) = 0 := by
  rw [dualPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

theorem phiPoint_some_of_x_ne_zero {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hu : u ≠ 0) :
    phiPoint (.some u W h) =
      WeierstrassCurve.Affine.Point.mk
        (E2Curve_equation_iff _ _ |>.2 <|
          phi_on_curve hu (E1Curve_equation_iff _ _ |>.1 h.1)) := by
  simp [phiPoint, hu]

theorem dualPoint_some_of_x_ne_zero {v V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E2Curve v V)
    (hv : v ≠ 0) :
    dualPoint (.some v V h) =
      WeierstrassCurve.Affine.Point.mk
        (E1Curve_equation_iff _ _ |>.2 <|
          dual_on_curve hv (E2Curve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualPoint, hv]

/-! ### The compositions are multiplication by two -/

private def E1Tangent (u W : ℚ) : ℚ :=
  (3 * u ^ 2 + 50 * u + 144) / (2 * W)

private def E2Tangent (v V : ℚ) : ℚ :=
  (3 * v ^ 2 - 100 * v + 49) / (2 * V)

private def tangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

private def tangentY (x y m : ℚ) : ℚ :=
  -(m * (tangentX 0 x m - x) + y)

theorem dual_phi_x {u W : ℚ} (hu : u ≠ 0) (hW : W ≠ 0)
    (h : OnE1 u W) :
    dualX (phiX u W) (phiY u W) =
      tangentX 25 u (E1Tangent u W) := by
  unfold dualX phiX phiY tangentX E1Tangent
  unfold OnE1 at h
  field_simp [hu, hW]
  rw [h]
  ring

theorem dual_phi_y {u W : ℚ} (hu : u ≠ 0) (hW : W ≠ 0)
    (h : OnE1 u W) :
    dualY (phiX u W) (phiY u W) =
      -(E1Tangent u W *
          (tangentX 25 u (E1Tangent u W) - u) + W) := by
  unfold dualY phiX phiY tangentX E1Tangent
  unfold OnE1 at h
  field_simp [hu, hW]
  have hW4 : W ^ 4 = (u * (u + 9) * (u + 16)) ^ 2 := by
    calc
      W ^ 4 = (W ^ 2) ^ 2 := by ring
      _ = (u * (u + 9) * (u + 16)) ^ 2 := by rw [h]
  rw [hW4, h]
  ring

theorem phi_dual_x {v V : ℚ} (hv : v ≠ 0) (hV : V ≠ 0)
    (h : OnE2 v V) :
    phiX (dualX v V) (dualY v V) =
      tangentX (-50) v (E2Tangent v V) := by
  unfold phiX dualX dualY tangentX E2Tangent
  unfold OnE2 at h
  field_simp [hv, hV]
  rw [h]
  ring

theorem phi_dual_y {v V : ℚ} (hv : v ≠ 0) (hV : V ≠ 0)
    (h : OnE2 v V) :
    phiY (dualX v V) (dualY v V) =
      -(E2Tangent v V *
          (tangentX (-50) v (E2Tangent v V) - v) + V) := by
  unfold phiY dualX dualY tangentX E2Tangent
  unfold OnE2 at h
  field_simp [hv, hV]
  have hV4 : V ^ 4 = (v * (v - 1) * (v - 49)) ^ 2 := by
    calc
      V ^ 4 = (V ^ 2) ^ 2 := by ring
      _ = (v * (v - 1) * (v - 49)) ^ 2 := by rw [h]
  rw [hV4, h]
  ring

@[simp] theorem E1Curve_negY (u W : ℚ) :
    WeierstrassCurve.Affine.negY E1Curve u W = -W := by
  simp [WeierstrassCurve.Affine.negY, E1Curve]

@[simp] theorem E2Curve_negY (v V : ℚ) :
    WeierstrassCurve.Affine.negY E2Curve v V = -V := by
  simp [WeierstrassCurve.Affine.negY, E2Curve]

private theorem E1Curve_slope_self {u W : ℚ} (hW : W ≠ 0) :
    WeierstrassCurve.Affine.slope E1Curve u u W W = E1Tangent u W := by
  have hneg : W ≠ WeierstrassCurve.Affine.negY E1Curve u W := by
    intro h
    apply hW
    rw [E1Curve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [E1Curve, E1Tangent, WeierstrassCurve.Affine.negY]
  ring

private theorem E2Curve_slope_self {v V : ℚ} (hV : V ≠ 0) :
    WeierstrassCurve.Affine.slope E2Curve v v V V = E2Tangent v V := by
  have hneg : V ≠ WeierstrassCurve.Affine.negY E2Curve v V := by
    intro h
    apply hV
    rw [E2Curve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [E2Curve, E2Tangent, WeierstrassCurve.Affine.negY]
  ring

private theorem E1Curve_addX_tangent (u W : ℚ) :
    WeierstrassCurve.Affine.addX E1Curve u u (E1Tangent u W) =
      tangentX 25 u (E1Tangent u W) := by
  simp [E1Curve, tangentX]
  ring

private theorem E2Curve_addX_tangent (v V : ℚ) :
    WeierstrassCurve.Affine.addX E2Curve v v (E2Tangent v V) =
      tangentX (-50) v (E2Tangent v V) := by
  simp [E2Curve, tangentX]
  ring

private theorem E1Curve_addY_tangent (u W : ℚ) :
    WeierstrassCurve.Affine.addY E1Curve u u W (E1Tangent u W) =
      -(E1Tangent u W *
          (tangentX 25 u (E1Tangent u W) - u) + W) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX tangentX E1Curve
  ring

private theorem E2Curve_addY_tangent (v V : ℚ) :
    WeierstrassCurve.Affine.addY E2Curve v v V (E2Tangent v V) =
      -(E2Tangent v V *
          (tangentX (-50) v (E2Tangent v V) - v) + V) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX tangentX E2Curve
  ring

private theorem E1_y_zero_of_x_zero {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hu : u = 0) : W = 0 := by
  have heq := (E1Curve_equation_iff u W).mp h.1
  unfold OnE1 at heq
  rw [hu] at heq
  norm_num at heq
  nlinarith

private theorem E2_y_zero_of_x_zero {v V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E2Curve v V)
    (hv : v = 0) : V = 0 := by
  have heq := (E2Curve_equation_iff v V).mp h.1
  unfold OnE2 at heq
  rw [hv] at heq
  norm_num at heq
  nlinarith

private theorem E1_double_eq_zero_of_y_zero {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hW : W = 0) :
    2 • (WeierstrassCurve.Affine.Point.some u W h : E1Point) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hW, E1Curve])

private theorem E2_double_eq_zero_of_y_zero {v V : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E2Curve v V)
    (hV : V = 0) :
    2 • (WeierstrassCurve.Affine.Point.some v V h : E2Point) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hV, E2Curve])

/-- `φ̂ ∘ φ = [2]` on every rational point of `E₁`. -/
theorem dual_comp_phiPoint (P : E1Point) :
    dualPoint (phiPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some u W h =>
      by_cases hu : u = 0
      · have hW : W = 0 := E1_y_zero_of_x_zero h hu
        rw [phiPoint_some_of_x_eq_zero h hu, dualPoint_zero]
        exact (E1_double_eq_zero_of_y_zero h hW).symm
      · rw [phiPoint_some_of_x_ne_zero h hu]
        by_cases hW : W = 0
        · have hpx : phiX u W = 0 := by simp [phiX, hW]
          change dualPoint (.some (phiX u W) (phiY u W) _) = _
          rw [dualPoint_some_of_x_eq_zero _ hpx]
          exact (E1_double_eq_zero_of_y_zero h hW).symm
        · have hpx : phiX u W ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hW) (pow_ne_zero 2 hu)
          change dualPoint (.some (phiX u W) (phiY u W) _) = _
          rw [dualPoint_some_of_x_ne_zero _ hpx]
          have hneg : W ≠ WeierstrassCurve.Affine.negY E1Curve u W := by
            intro heq
            simp [WeierstrassCurve.Affine.negY, E1Curve] at heq
            apply hW
            linarith
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
          change WeierstrassCurve.Affine.Point.some
              (dualX (phiX u W) (phiY u W))
              (dualY (phiX u W) (phiY u W)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX E1Curve u u
                (WeierstrassCurve.Affine.slope E1Curve u u W W))
              (WeierstrassCurve.Affine.addY E1Curve u u W
                (WeierstrassCurve.Affine.slope E1Curve u u W W)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq := (E1Curve_equation_iff u W).mp h.1
          constructor
          · rw [dual_phi_x hu hW heq, E1Curve_slope_self hW,
              E1Curve_addX_tangent]
          · rw [dual_phi_y hu hW heq, E1Curve_slope_self hW,
              E1Curve_addY_tangent]

/-- `φ ∘ φ̂ = [2]` on every rational point of `E₂`. -/
theorem phi_comp_dualPoint (P : E2Point) :
    phiPoint (dualPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some v V h =>
      by_cases hv : v = 0
      · have hV : V = 0 := E2_y_zero_of_x_zero h hv
        rw [dualPoint_some_of_x_eq_zero h hv, phiPoint_zero]
        exact (E2_double_eq_zero_of_y_zero h hV).symm
      · rw [dualPoint_some_of_x_ne_zero h hv]
        by_cases hV : V = 0
        · have hdx : dualX v V = 0 := by simp [dualX, hV]
          change phiPoint (.some (dualX v V) (dualY v V) _) = _
          rw [phiPoint_some_of_x_eq_zero _ hdx]
          exact (E2_double_eq_zero_of_y_zero h hV).symm
        · have hdx : dualX v V ≠ 0 := by
            exact div_ne_zero (pow_ne_zero 2 hV)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hv))
          change phiPoint (.some (dualX v V) (dualY v V) _) = _
          rw [phiPoint_some_of_x_ne_zero _ hdx]
          have hneg : V ≠ WeierstrassCurve.Affine.negY E2Curve v V := by
            intro heq
            simp [WeierstrassCurve.Affine.negY, E2Curve] at heq
            apply hV
            linarith
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
          change WeierstrassCurve.Affine.Point.some
              (phiX (dualX v V) (dualY v V))
              (phiY (dualX v V) (dualY v V)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX E2Curve v v
                (WeierstrassCurve.Affine.slope E2Curve v v V V))
              (WeierstrassCurve.Affine.addY E2Curve v v V
                (WeierstrassCurve.Affine.slope E2Curve v v V V)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq := (E2Curve_equation_iff v V).mp h.1
          constructor
          · rw [phi_dual_x hv hV heq, E2Curve_slope_self hV,
              E2Curve_addX_tangent]
          · rw [phi_dual_y hv hV heq, E2Curve_slope_self hV,
              E2Curve_addY_tangent]

/-! ### Explicit reconstruction of isogeny preimages -/

def dualPreimageX (r W : ℚ) : ℚ :=
  25 + 2 * r ^ 2 - 2 * W / r

def dualPreimageY (r W : ℚ) : ℚ :=
  2 * r * dualPreimageX r W

def phiPreimageX (r V : ℚ) : ℚ :=
  (r ^ 2 - 25 - V / r) / 2

def phiPreimageY (r V : ℚ) : ℚ :=
  r * phiPreimageX r V

theorem exists_dualPoint_preimage_of_x_eq_sq {u W r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hu : u ≠ 0) (hr : u = r ^ 2) :
    ∃ Q : E2Point,
      dualPoint Q = WeierstrassCurve.Affine.Point.some u W h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hu
    rw [hr, hrz]
    norm_num
  have hcurve : W ^ 2 = u ^ 3 + 25 * u ^ 2 + 144 * u := by
    have heq := (E1Curve_equation_iff u W).mp h.1
    unfold OnE1 at heq
    nlinarith
  have hcurveR : W ^ 2 = r ^ 6 + 25 * r ^ 4 + 144 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := dualPreimageX r W
  let qy := dualPreimageY r W
  have hprod :
      qx * (25 + 2 * r ^ 2 + 2 * W / r) = 49 := by
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : 49 - qx ^ 2 = 4 * qx * W / r := by
    rw [← hprod]
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : OnE2 qx qy := by
    unfold OnE2
    dsimp [qx, qy, dualPreimageX, dualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (2 * W - 2 * r ^ 3 - 25 * r) * hcurveR
  have hqns : WeierstrassCurve.Affine.Nonsingular E2Curve qx qy :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E2Curve_equation_iff qx qy).mpr hqeq)
  let Q : E2Point := WeierstrassCurve.Affine.Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [dualPoint_some_of_x_ne_zero hqns hqx]
  change WeierstrassCurve.Affine.Point.some (dualX qx qy) (dualY qx qy) _ =
    WeierstrassCurve.Affine.Point.some u W h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / (4 * qx ^ 2) = u
    rw [hr]
    field_simp [hqx]
    ring
  · change (2 * r * qx) * (49 - qx ^ 2) / (8 * qx ^ 2) = W
    rw [hnum]
    field_simp [hqx, hr0]
    ring

theorem exists_phiPoint_preimage_of_x_eq_sq {v V r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E2Curve v V)
    (hv : v ≠ 0) (hr : v = r ^ 2) :
    ∃ P : E1Point,
      phiPoint P = WeierstrassCurve.Affine.Point.some v V h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hv
    rw [hr, hrz]
    norm_num
  have hcurve : V ^ 2 = v ^ 3 - 50 * v ^ 2 + 49 * v := by
    have heq := (E2Curve_equation_iff v V).mp h.1
    unfold OnE2 at heq
    nlinarith
  have hcurveR : V ^ 2 = r ^ 6 - 50 * r ^ 4 + 49 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := phiPreimageX r V
  let py := phiPreimageY r V
  have hprod :
      px * ((r ^ 2 - 25 + V / r) / 2) = 144 := by
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 144 - px ^ 2 = px * V / r := by
    rw [← hprod]
    dsimp [px, phiPreimageX]
    field_simp [hr0]
    ring
  have hpeq : OnE1 px py := by
    unfold OnE1
    dsimp [px, py, phiPreimageX, phiPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + 25 * r + V) * hcurveR
  have hpns : WeierstrassCurve.Affine.Nonsingular E1Curve px py :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E1Curve_equation_iff px py).mpr hpeq)
  let P : E1Point := WeierstrassCurve.Affine.Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [phiPoint_some_of_x_ne_zero hpns hpx]
  change WeierstrassCurve.Affine.Point.some (phiX px py) (phiY px py) _ =
    WeierstrassCurve.Affine.Point.some v V h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = v
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (144 - px ^ 2) / px ^ 2 = V
    rw [hnum]
    field_simp [hpx, hr0]

/-! ## Kummer images -/

open RationalPointsN15Descent

theorem E1_integral_model {u W : ℚ} (h : OnE1 u W) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      u = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + 25 * A * B ^ 2 + 144 * B ^ 4) := by
  have hcubic : W ^ 2 =
      u ^ 3 + ((25 : ℤ) : ℚ) * u ^ 2 + ((144 : ℤ) : ℚ) * u := by
    unfold OnE1 at h
    norm_num at ⊢
    nlinarith
  exact integral_model_monic 25 144 u W hcubic

theorem E2_integral_model {v V : ℚ} (h : OnE2 v V) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      v = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 - 50 * A * B ^ 2 + 49 * B ^ 4) := by
  have hcubic : V ^ 2 =
      v ^ 3 + ((-50 : ℤ) : ℚ) * v ^ 2 + ((49 : ℤ) : ℚ) * v := by
    unfold OnE2 at h
    norm_num at ⊢
    nlinarith
  simpa [sub_eq_add_neg] using integral_model_monic (-50) 49 v V hcubic

private theorem squarefree_dvd_144 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 144) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
  have hpow : d ∣ 12 ^ 2 := by simpa using hdiv
  have hd12 : d ∣ 12 := (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  have hdle : d ≤ 12 := Nat.le_of_dvd (by norm_num) hd12
  have hnot4 : ¬ 2 * 2 ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.mp hd) 2 Nat.prime_two
  interval_cases d <;> norm_num at hd12
  all_goals norm_num at hnot4
  all_goals simp

private theorem squarefree_dvd_49 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 49) : d = 1 ∨ d = 7 := by
  have hpow : d ∣ 7 ^ 2 := by simpa using hdiv
  have hd7 : d ∣ 7 := (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  exact (Nat.dvd_prime (by norm_num)).mp hd7

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_E1_pos_two_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 2 * r ^ 4 + 25 * r ^ 2 * B ^ 2 + 72 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_E1_neg_two_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ -2 * r ^ 4 + 25 * r ^ 2 * B ^ 2 - 72 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_E1_pos_six_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 6 * r ^ 4 + 25 * r ^ 2 * B ^ 2 + 24 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_E1_neg_six_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ -6 * r ^ 4 + 25 * r ^ 2 * B ^ 2 - 24 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_E2_seven_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 7 * r ^ 4 - 50 * r ^ 2 * B ^ 2 + 7 * B ^ 4 := by
  decide

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

private theorem no_primitive_E1_pos_two (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 + 25 * r ^ 2 * B ^ 2 + 72 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_E1_pos_two_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem no_primitive_E1_neg_two (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -2 * r ^ 4 + 25 * r ^ 2 * B ^ 2 - 72 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_E1_neg_two_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem no_primitive_E1_pos_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 6 * r ^ 4 + 25 * r ^ 2 * B ^ 2 + 24 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_E1_pos_six_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem no_primitive_E1_neg_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -6 * r ^ 4 + 25 * r ^ 2 * B ^ 2 - 24 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_E1_neg_six_mod16 _ _ _ (primitive_mod_two hcop)) hm

private theorem no_primitive_E2_seven (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 7 * r ^ 4 - 50 * r ^ 2 * B ^ 2 + 7 * B ^ 4) : False := by
  have hm := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hm
  exact (no_E2_seven_mod16 _ _ _ (primitive_mod_two hcop)) hm

/-- The Kummer image on `E₁` consists of the four classes `±1, ±3`. -/
theorem E1_rational_x_squareclasses {u W : ℚ}
    (h : OnE1 u W) (hu0 : u ≠ 0) :
    ∃ q : ℚ,
      u = q ^ 2 ∨ u = -(q ^ 2) ∨
      u = 3 * q ^ 2 ∨ u = -(3 * q ^ 2) := by
  obtain ⟨A, B, C, hBpos, hcop, hu, hmodel⟩ := E1_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hu0
    rw [hu, hA]
    norm_num
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel
  have hdiv144 : d ∣ 144 := by simpa using hdiv
  rcases squarefree_dvd_144 hd hdiv144 with rfl | rfl | rfl | rfl
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
      simpa using rat_squareclass_of_integral hB0 hu hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr (Or.inl ?_)⟩
      have hA' : A = (-1 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      simpa using rat_squareclass_of_integral hB0 hu hA'
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA, hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := 25) (b := 144) (d := 2) (e := 72)
        (by norm_num) hr0 (by norm_num) hA hmodel
      exact (no_primitive_E1_pos_two _ _ _
        (root_coprime_denominator hcop hA) hz).elim
    · have hA' : A = (-2 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA', hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := 25) (b := 144) (d := -2) (e := -72)
        (by norm_num) hr0 (by norm_num) hA' hmodel
      have hz' : z ^ 2 =
          -2 * (r : ℤ) ^ 4 + 25 * (r : ℤ) ^ 2 * B ^ 2 - 72 * B ^ 4 := by
        calc
          z ^ 2 = (-2 : ℤ) * (r : ℤ) ^ 4 +
              25 * (r : ℤ) ^ 2 * B ^ 2 + (-72) * B ^ 4 := hz
          _ = _ := by ring
      exact (no_primitive_E1_neg_two _ _ _
        (root_coprime_denominator hcop hA') hz').elim
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr (Or.inr (Or.inl ?_))⟩
      simpa using rat_squareclass_of_integral hB0 hu hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr (Or.inr (Or.inr ?_))⟩
      have hA' : A = (-3 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      simpa using rat_squareclass_of_integral hB0 hu hA'
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA, hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := 25) (b := 144) (d := 6) (e := 24)
        (by norm_num) hr0 (by norm_num) hA hmodel
      exact (no_primitive_E1_pos_six _ _ _
        (root_coprime_denominator hcop hA) hz).elim
    · have hA' : A = (-6 : ℤ) * (r : ℤ) ^ 2 := by simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA', hr]
        norm_num
      obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
        (a := 25) (b := 144) (d := -6) (e := -24)
        (by norm_num) hr0 (by norm_num) hA' hmodel
      have hz' : z ^ 2 =
          -6 * (r : ℤ) ^ 4 + 25 * (r : ℤ) ^ 2 * B ^ 2 - 24 * B ^ 4 := by
        calc
          z ^ 2 = (-6 : ℤ) * (r : ℤ) ^ 4 +
              25 * (r : ℤ) ^ 2 * B ^ 2 + (-24) * B ^ 4 := hz
          _ = _ := by ring
      exact (no_primitive_E1_neg_six _ _ _
        (root_coprime_denominator hcop hA') hz').elim

private theorem E2_x_nonnegative {v V : ℚ} (h : OnE2 v V) : 0 ≤ v := by
  by_contra hv
  have hvneg : v < 0 := lt_of_not_ge hv
  unfold OnE2 at h
  have h1 : v - 1 < 0 := by linarith
  have h49 : v - 49 < 0 := by linarith
  have hp : 0 < v * (v - 1) := mul_pos_of_neg_of_neg hvneg h1
  nlinarith [mul_neg_of_pos_of_neg hp h49, sq_nonneg V]

/-- The Kummer image on `E₂` is trivial. -/
theorem E2_rational_x_square {v V : ℚ}
    (h : OnE2 v V) (hv0 : v ≠ 0) :
    ∃ q : ℚ, v = q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hv, hmodel⟩ := E2_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hA
    apply hv0
    rw [hv, hA]
    norm_num
  have hmodel' :
      C ^ 2 = A * (A ^ 2 + (-50) * A * B ^ 2 + 49 * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  have hdiv49 : d ∣ 49 := by simpa using hdiv
  have hvpos : 0 < v := lt_of_le_of_ne (E2_x_nonnegative h) (Ne.symm hv0)
  have hApos : 0 < A := by
    have hBq0 : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB0
    have hAq : (A : ℚ) = v * (B : ℚ) ^ 2 := by
      rw [hv]
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
  rcases squarefree_dvd_49 hd hdiv49 with rfl | rfl
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    simpa using rat_squareclass_of_integral hB0 hv hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := -50) (b := 49) (d := 7) (e := 7)
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (no_primitive_E2_seven _ _ _
      (root_coprime_denominator hcop hA) (by simpa [sub_eq_add_neg] using hz)).elim

/-! ## The four-coset descent step -/

private def E1PointOf (u W : ℚ) (h : OnE1 u W) : E1Point :=
  WeierstrassCurve.Affine.Point.some u W
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E1Curve_equation_iff u W).mpr h))

private def E1K0 : E1Point := E1PointOf 0 0 (by norm_num [OnE1])
private def E1Km16 : E1Point := E1PointOf (-16) 0 (by norm_num [OnE1])
private def E1Km12 : E1Point := E1PointOf (-12) (-12) (by norm_num [OnE1])
private def E1P12 : E1Point := E1PointOf 12 84 (by norm_num [OnE1])

private theorem E1_y_ne_negY {u W : ℚ} (hW : W ≠ 0) :
    W ≠ WeierstrassCurve.Affine.negY E1Curve u W := by
  intro h
  simp [E1Curve, WeierstrassCurve.Affine.negY] at h
  apply hW
  linarith

private theorem E1K0_two : 2 • E1K0 = 0 :=
  E1_double_eq_zero_of_y_zero _ rfl

private theorem E1Km16_two : 2 • E1Km16 = 0 :=
  E1_double_eq_zero_of_y_zero _ rfl

private theorem E1Km12_two : 2 • E1Km12 = E1K0 := by
  change 2 • (WeierstrassCurve.Affine.Point.some (-12) (-12) _ : E1Point) =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (E1_y_ne_negY (by norm_num : (-12 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX E1Curve (-12) (-12)
        (WeierstrassCurve.Affine.slope E1Curve (-12) (-12) (-12) (-12)))
      (WeierstrassCurve.Affine.addY E1Curve (-12) (-12) (-12)
        (WeierstrassCurve.Affine.slope E1Curve (-12) (-12) (-12) (-12))) _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    E1Curve]

private theorem E1P12_two : 2 • E1P12 = E1K0 := by
  change 2 • (WeierstrassCurve.Affine.Point.some 12 84 _ : E1Point) =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (E1_y_ne_negY (by norm_num : (84 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX E1Curve 12 12
        (WeierstrassCurve.Affine.slope E1Curve 12 12 84 84))
      (WeierstrassCurve.Affine.addY E1Curve 12 12 84
        (WeierstrassCurve.Affine.slope E1Curve 12 12 84 84)) _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    E1Curve]

private theorem E1K0_four : 4 • E1K0 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, E1K0_two, nsmul_zero]

private theorem E1Km16_four : 4 • E1Km16 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, E1Km16_two, nsmul_zero]

private theorem E1Km12_four : 4 • E1Km12 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, E1Km12_two, E1K0_two]

private theorem E1P12_four : 4 • E1P12 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, E1P12_two, E1K0_two]

private theorem E1_exists_half_of_square_x {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W)
    (hu : u ≠ 0) (hsq : ∃ q : ℚ, u = q ^ 2) :
    ∃ Q : E1Point,
      2 • Q = WeierstrassCurve.Affine.Point.some u W h := by
  obtain ⟨q, hq⟩ := hsq
  obtain ⟨S, hS⟩ := exists_dualPoint_preimage_of_x_eq_sq h hu hq
  cases S with
  | zero =>
      change dualPoint (0 : E2Point) = _ at hS
      rw [dualPoint_zero] at hS
      cases hS
  | some v V hv =>
      by_cases hv0 : v = 0
      · rw [dualPoint_some_of_x_eq_zero hv hv0] at hS
        cases hS
      · have hveq : OnE2 v V := (E2Curve_equation_iff v V).mp hv.1
        obtain ⟨r, hr⟩ := E2_rational_x_square hveq hv0
        obtain ⟨Q, hQ⟩ := exists_phiPoint_preimage_of_x_eq_sq hv hv0 hr
        refine ⟨Q, ?_⟩
        rw [← dual_comp_phiPoint Q, hQ, hS]

private theorem E1_secant_x_square
    {x y t s q d r : ℚ}
    (hxy : OnE1 x y) (hts : OnE1 t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    WeierstrassCurve.Affine.addX E1Curve x t
        (WeierstrassCurve.Affine.slope E1Curve x t y (-s)) =
      ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxt]
  unfold WeierstrassCurve.Affine.addX
  simp only [E1Curve, zero_mul, sub_neg_eq_add]
  have hxy' : y ^ 2 = x ^ 3 + 25 * x ^ 2 + 144 * x := by
    unfold OnE1 at hxy
    nlinarith
  have hts' : s ^ 2 = t ^ 3 + 25 * t ^ 2 + 144 * t := by
    unfold OnE1 at hts
    nlinarith
  field_simp [sub_ne_zero.mpr hxt, hd, hq, hr]
  have hxdt : d ^ 2 * q ^ 2 * r ^ 2 = x * t := by
    rw [hx, ht]
    ring
  calc
    ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 25 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * d ^ 2 * q ^ 2 * r ^ 2 =
        ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 25 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) *
          (d ^ 2 * q ^ 2 * r ^ 2) := by ring
    _ = ((y + s) ^ 2 + (x - t) ^ 2 * 0 - (x - t) ^ 2 * 25 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * (x * t) := by
      rw [hxdt]
    _ = (y * t + s * x) ^ 2 := by
      ring_nf
      rw [hxy', hts']
      ring

private theorem E1_y_eq_or_eq_neg_of_same_x
    {x y s : ℚ} (hy : OnE1 x y) (hs : OnE1 x s) :
    y = s ∨ y = -s := by
  have hsq : y ^ 2 = s ^ 2 := by rw [hy, hs]
  have hfac : (y - s) * (y + s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

private theorem four_nsmul_add_of_four_nsmul_eq_zero
    {T R : E1Point} (hT : 4 • T = 0) (hR : 2 • R = 0) :
    4 • (T + R) = 0 := by
  rw [nsmul_add, hT, show 4 = 2 * 2 by norm_num, mul_nsmul, hR,
    nsmul_zero, add_zero]

private theorem E1_descent_after_same_squareclass
    {x y t s q d r : ℚ}
    (hxy : WeierstrassCurve.Affine.Nonsingular E1Curve x y)
    (hts : WeierstrassCurve.Affine.Nonsingular E1Curve t s)
    (hT4 : 4 • (WeierstrassCurve.Affine.Point.some t s hts : E1Point) = 0)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    ∃ T Q : E1Point,
      4 • T = 0 ∧
      WeierstrassCurve.Affine.Point.some x y hxy = T + 2 • Q := by
  let P : E1Point := WeierstrassCurve.Affine.Point.some x y hxy
  let T0 : E1Point := WeierstrassCurve.Affine.Point.some t s hts
  by_cases hxt : x = t
  · have hxeq : OnE1 x y := (E1Curve_equation_iff x y).mp hxy.1
    have hteq : OnE1 t s := (E1Curve_equation_iff t s).mp hts.1
    rw [hxt] at hxeq
    rcases E1_y_eq_or_eq_neg_of_same_x hxeq hteq with hy | hy
    · have hPT : P = T0 := by
        dsimp [P, T0]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨hxt, hy⟩
      refine ⟨T0, 0, hT4, ?_⟩
      simp [P, hPT]
    · have hPT : P = -T0 := by
        change WeierstrassCurve.Affine.Point.some x y hxy =
          -(WeierstrassCurve.Affine.Point.some t s hts : E1Point)
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        simp [E1Curve, WeierstrassCurve.Affine.negY, hxt, hy]
      refine ⟨P, 0, ?_, ?_⟩
      · rw [hPT]
        simp
        exact hT4
      · change P = P + 2 • (0 : E1Point)
        simp
  · have hneg : WeierstrassCurve.Affine.Nonsingular E1Curve t (-s) := by
      have hn := (WeierstrassCurve.Affine.nonsingular_neg t s).mpr hts
      simpa [E1Curve, WeierstrassCurve.Affine.negY] using hn
    let m := WeierstrassCurve.Affine.slope E1Curve x t y (-s)
    let z := WeierstrassCurve.Affine.addX E1Curve x t m
    let w := WeierstrassCurve.Affine.addY E1Curve x t y m
    have hR : WeierstrassCurve.Affine.Nonsingular E1Curve z w :=
      WeierstrassCurve.Affine.nonsingular_add hxy hneg
        (fun hbad => hxt hbad.1)
    have hzsq : z = ((y * t + s * x) /
        ((x - t) * d * q * r)) ^ 2 := by
      exact E1_secant_x_square
        ((E1Curve_equation_iff x y).mp hxy.1)
        ((E1Curve_equation_iff t s).mp hts.1)
        hx ht hxt hd hq hr
    have hsum : P - T0 = WeierstrassCurve.Affine.Point.some z w hR := by
      have hnegPoint :
          -(WeierstrassCurve.Affine.Point.some t s hts : E1Point) =
            WeierstrassCurve.Affine.Point.some t (-s) hneg := by
        rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq]
        simp [WeierstrassCurve.Affine.negY, E1Curve]
      dsimp only [P, T0]
      rw [sub_eq_add_neg, hnegPoint]
      dsimp only [z, w, m]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxt
    by_cases hz : z = 0
    · have hw : w = 0 := by
        have heq := (E1Curve_equation_iff z w).mp hR.1
        unfold OnE1 at heq
        rw [hz] at heq
        norm_num at heq
        nlinarith
      let R : E1Point := WeierstrassCurve.Affine.Point.some z w hR
      have hR2 : 2 • R = 0 := E1_double_eq_zero_of_y_zero hR hw
      have hP : P = T0 + R := by
        rw [sub_eq_iff_eq_add] at hsum
        simpa [R, add_comm] using hsum
      refine ⟨P, 0, ?_, ?_⟩
      · rw [hP]
        exact four_nsmul_add_of_four_nsmul_eq_zero hT4 hR2
      · change P = P + 2 • (0 : E1Point)
        simp
    · obtain ⟨Q, hQ⟩ := E1_exists_half_of_square_x hR hz ⟨_, hzsq⟩
      refine ⟨T0, Q, hT4, ?_⟩
      change P = T0 + 2 • Q
      rw [hQ, ← hsum]
      abel

/-- Every rational point of `E₁` lies in one of four cosets modulo `2E₁(ℚ)`. -/
theorem E1_two_descent_step (P : E1Point) :
    ∃ T Q : E1Point, 4 • T = 0 ∧ P = T + 2 • Q := by
  cases P with
  | zero => exact ⟨0, 0, by simp only [nsmul_zero], rfl⟩
  | some u W h =>
      by_cases hu0 : u = 0
      · have hW0 : W = 0 := E1_y_zero_of_x_zero h hu0
        refine ⟨WeierstrassCurve.Affine.Point.some u W h, 0, ?_, by simp⟩
        rw [show 4 = 2 * 2 by norm_num, mul_nsmul,
          E1_double_eq_zero_of_y_zero h hW0, nsmul_zero]
      · have heq : OnE1 u W := (E1Curve_equation_iff u W).mp h.1
        obtain ⟨q, hsquare | hneg | hthree | hnegThree⟩ :=
          E1_rational_x_squareclasses heq hu0
        · obtain ⟨Q, hQ⟩ := E1_exists_half_of_square_x h hu0 ⟨q, hsquare⟩
          exact ⟨0, Q, by simp, by simpa using hQ.symm⟩
        · have hq : q ≠ 0 := by
            intro hq
            apply hu0
            rw [hneg, hq]
            norm_num
          have hx : u = (-1 : ℚ) * q ^ 2 := by simpa using hneg
          exact E1_descent_after_same_squareclass
            (d := -1) (r := 4) h _ E1Km16_four hx
            (by norm_num) (by norm_num) hq (by norm_num)
        · have hq : q ≠ 0 := by
            intro hq
            apply hu0
            rw [hthree, hq]
            norm_num
          exact E1_descent_after_same_squareclass
            (d := 3) (r := 2) h _ E1P12_four hthree
            (by norm_num) (by norm_num) hq (by norm_num)
        · have hq : q ≠ 0 := by
            intro hq
            apply hu0
            rw [hnegThree, hq]
            norm_num
          have hx : u = (-3 : ℚ) * q ^ 2 := by simpa using hnegThree
          exact E1_descent_after_same_squareclass
            (d := -3) (r := 2) h _ E1Km12_four hx
            (by norm_num) (by norm_num) hq (by norm_num)

/-- Iterating the four-coset statement makes `4P` divisible by every power
of two. -/
theorem E1_four_nsmul_two_power_divisible (P : E1Point) (n : ℕ) :
    ∃ Q : E1Point, 4 • P = (2 ^ n : ℕ) • (4 • Q) := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨T, R, hT, hdecomp⟩ := E1_two_descent_step Q
      refine ⟨R, ?_⟩
      rw [hQ, hdecomp, nsmul_add, hT, zero_add]
      simp only [← mul_nsmul]
      congr 1
      omega

/-! ### Integral good-reduction model at two -/

open Scratch.TateZ2xZ10Reduction

def E21toE1Change : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 2
  s := -1 / 2
  t := -1

theorem E21toE1Change_curve : E21toE1Change • E21Curve = E1Curve := by
  ext <;>
    simp [E21toE1Change, E21Curve, E1Curve,
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

noncomputable def E21E1AddEquiv : E21Point ≃+ E1Point :=
  (variableChangePointAddEquiv E21Curve E21toE1Change).trans
    (curveEqAddEquiv E21toE1Change_curve)

theorem E21E1AddEquiv_some
    {x y : ℚ} {h0 : WeierstrassCurve.Affine.Nonsingular E21Curve x y}
    {h1 : WeierstrassCurve.Affine.Nonsingular E1Curve
      (4 * (x - 2)) (4 * (2 * y + x))} :
    E21E1AddEquiv (WeierstrassCurve.Affine.Point.some x y h0) =
      WeierstrassCurve.Affine.Point.some
        (4 * (x - 2)) (4 * (2 * y + x)) h1 := by
  change (curveEqAddEquiv E21toE1Change_curve)
      (variableChangePointMap E21Curve E21toE1Change
        (WeierstrassCurve.Affine.Point.some x y h0)) = _
  change (curveEqAddEquiv E21toE1Change_curve)
      (WeierstrassCurve.Affine.Point.some
      (variableChangePointX E21toE1Change x)
      (variableChangePointY E21toE1Change x y) _) = _
  have hx : variableChangePointX E21toE1Change x = 4 * (x - 2) := by
    norm_num [variableChangePointX, E21toE1Change]
  have hy : variableChangePointY E21toE1Change x y =
      4 * (2 * y + x) := by
    norm_num [variableChangePointY, E21toE1Change]
    ring
  have hvar0 : WeierstrassCurve.Affine.Nonsingular
      (E21toE1Change • E21Curve)
      (variableChangePointX E21toE1Change x)
      (variableChangePointY E21toE1Change x y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (variableChangePoint_equation E21Curve E21toE1Change h0.1)
  have hvar : WeierstrassCurve.Affine.Nonsingular E1Curve
      (variableChangePointX E21toE1Change x)
      (variableChangePointY E21toE1Change x y) := by
    rw [← E21toE1Change_curve]
    exact hvar0
  calc
    (curveEqAddEquiv E21toE1Change_curve)
        (WeierstrassCurve.Affine.Point.some
          (variableChangePointX E21toE1Change x)
          (variableChangePointY E21toE1Change x y) _) =
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX E21toE1Change x)
        (variableChangePointY E21toE1Change x y) hvar :=
      curveEqAddEquiv_some E21toE1Change_curve
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

private theorem rat_unit_sub_one_pos {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat 2 q = 0) :
    q - 1 = 0 ∨ 0 < padicValRat 2 (q - 1) := by
  by_cases hq1 : q - 1 = 0
  · exact Or.inl hq1
  right
  have hqnonneg : 0 ≤ padicValRat 2 q := by omega
  let z : ℤ_[2] := ratPadicInt q hqnonneg
  have hzcoe : (z : ℚ_[2]) = (q : ℚ_[2]) := rfl
  have hzred0 : PadicInt.toZMod z ≠ 0 := by
    intro hz0
    have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod]
      exact hz0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd] at hm
    have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
    have hnorm : ‖(q : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hqcast,
        Padic.valuation_ratCast, hv]
      norm_num
    change ‖(z : ℚ_[2])‖ < 1 at hm
    rw [hzcoe, hnorm] at hm
    exact (lt_irrefl 1 hm)
  have hzred : PadicInt.toZMod z = 1 := zmod2_nonzero_eq_one _ hzred0
  have hdiffnonneg : 0 ≤ padicValRat 2 (q - 1) := by
    have hmin := padicValRat.min_le_padicValRat_add (p := 2)
      (q := q) (r := -1) (by simpa [sub_eq_add_neg] using hq1)
    rw [padicValRat.neg, hv, padicValRat.one, min_self] at hmin
    simpa [sub_eq_add_neg] using hmin
  let d : ℤ_[2] := ratPadicInt (q - 1) hdiffnonneg
  have hdcoe : (d : ℚ_[2]) = ((q - 1 : ℚ) : ℚ_[2]) := rfl
  have hdred : PadicInt.toZMod d = 0 := by
    change PadicInt.toZMod (ratPadicInt (q - 1) hdiffnonneg) = 0
    have hsub : ratPadicInt (q - 1) hdiffnonneg = z - 1 := by
      apply Subtype.ext
      change (((q - 1 : ℚ) : ℚ_[2])) = (z : ℚ_[2]) - 1
      rw [hzcoe]
      norm_cast
    rw [hsub, map_sub, map_one, hzred, sub_self]
  have hm : d ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hdred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  have hdiffcast : (((q - 1 : ℚ) : ℚ_[2])) ≠ 0 := by exact_mod_cast hq1
  change ‖(d : ℚ_[2])‖ < 1 at hm
  rw [hdcoe, Padic.norm_eq_zpow_neg_valuation hdiffcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)] at hm
  have hexp : -padicValRat 2 (q - 1) < (0 : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2)).mp (by simpa using hm)
  omega

def E21DoubleDen (x y : ℚ) : ℚ := 2 * y + x

def E21DoubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + 8 * x ^ 2 + 8 * x + 17

def E21DoubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 - x ^ 4 * y - 20 * x ^ 4 - 24 * x ^ 3 -
    8 * x ^ 2 * y - 89 * x ^ 2 - 8 * x * y - 33 * x - 17 * y + 60

private theorem E21_doubleX_formula {x y : ℚ}
    (hd : E21DoubleDen x y ≠ 0) (hE : OnE21 x y) :
    WeierstrassCurve.Affine.addX E21Curve x x
        (WeierstrassCurve.Affine.slope E21Curve x x y y) =
      E21DoubleXNum x / E21DoubleDen x y ^ 2 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E21Curve x y := by
    intro h
    apply hd
    simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E21Curve x x y y =
      (3 * x ^ 2 - y - 4) / E21DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E21Curve, E21DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addX E21DoubleXNum
  simp only [E21Curve]
  unfold OnE21 at hE
  field_simp [hd]
  unfold E21DoubleDen
  linear_combination
    (-8 * x - 1) * hE

private theorem E21_doubleY_formula {x y : ℚ}
    (hd : E21DoubleDen x y ≠ 0) (hE : OnE21 x y) :
    WeierstrassCurve.Affine.addY E21Curve x x y
        (WeierstrassCurve.Affine.slope E21Curve x x y y) =
      E21DoubleYNum x y / E21DoubleDen x y ^ 3 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E21Curve x y := by
    intro h
    apply hd
    simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E21Curve x x y y =
      (3 * x ^ 2 - y - 4) / E21DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E21Curve, E21DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E21DoubleYNum
  simp [E21Curve]
  unfold OnE21 at hE
  field_simp [hd]
  unfold E21DoubleDen
  linear_combination
    (28 * x ^ 3 + 9 * x ^ 2 - 15 * x - 8 * y ^ 2 + y + 4) * hE

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

private theorem E21DoubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (E21DoubleXNum x) = -8 * k := by
  have hshape : E21DoubleXNum x =
      x ^ 4 + [8 * x ^ 2, 8 * x, (17 : ℚ)].sum := by
    simp [E21DoubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hge := val_monomial_ge hx hy 8 (by norm_num) 2 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 8 (by norm_num) 1 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg 17
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega

private theorem E21DoubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (E21DoubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [(-1 : ℚ) * x ^ 4 * y, -20 * x ^ 4, -24 * x ^ 3,
      -8 * x ^ 2 * y, -89 * x ^ 2, -8 * x * y,
      -33 * x, -17 * y, (60 : ℚ)]
  have hshape : E21DoubleYNum x y = x ^ 6 + l.sum := by
    simp [E21DoubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow hx, hvx]
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-20) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-24) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-8) (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-89) (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-8) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-33) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-17) (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg 60
      norm_num at hge ⊢
      omega

/-- A point is in the formal kernel at `2` when its affine coordinates have
the standard valuations `(-2k,-3k)` for some `k>0`. -/
def E21FormalAtTwo : E21Point → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

def E21FormalLevel : E21Point → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

theorem E21FormalAtTwo_iff (P : E21Point) :
    E21FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, E21FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [E21FormalAtTwo, E21FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

/-- On the formal kernel, doubling raises the local-parameter valuation by
at least one.  This is the curve-specific form of
`v₂([2]z) ≥ v₂(z)+1`. -/
theorem E21FormalLevel_double {P : E21Point} {k : ℤ}
    (hP : E21FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ E21FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [E21FormalLevel] at hP
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
      by_cases hd : E21DoubleDen x y = 0
      · left
        rw [two_nsmul]
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvdenLower : 1 - 3 * k ≤ padicValRat 2 (E21DoubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y) (r := x) (by simpa [E21DoubleDen] using hd)
          rw [hv2y, hvx, min_eq_left (by omega)] at hmin
          simpa [E21DoubleDen] using hmin
        let k' : ℤ := 4 * k + padicValRat 2 (E21DoubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := E21DoubleXNum_val hx hy hk hvx
        have hvY := E21DoubleYNum_val hx hy hk hvx hvy
        have hN : E21DoubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : E21DoubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE : OnE21 x y := (E21Curve_equation_iff x y).mp h.1
        have hxform := E21_doubleX_formula hd hE
        have hyform := E21_doubleY_formula hd hE
        have hvx2 : padicValRat 2
              (WeierstrassCurve.Affine.addX E21Curve x x
                (WeierstrassCurve.Affine.slope E21Curve x x y y)) =
            -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow hd]
          dsimp [k']
          ring
        have hvy2 : padicValRat 2
              (WeierstrassCurve.Affine.addY E21Curve x x y
                (WeierstrassCurve.Affine.slope E21Curve x x y y)) =
            -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ WeierstrassCurve.Affine.negY E21Curve x y := by
          intro heq
          apply hd
          simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at heq ⊢
          linarith
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- Good reduction at two gives the usual dichotomy: an affine rational point
has integral coordinates, or lies in the formal kernel. -/
theorem E21_formal_or_integral (P : E21Point) :
    E21FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE : OnE21 x y := (E21Curve_equation_iff x y).mp h.1
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
        let l : List ℚ := [x * y, -(x ^ 3), 4 * x, (1 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnE21 at hE
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
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
            · rw [hx0, mul_zero, padicValRat.zero, hlead]
              omega
            · have hge := val_const_mul_ge 4 (by norm_num) hx0
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
          let l : List ℚ := [y ^ 2, x * y, 4 * x, (1 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnE21 at hE
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl
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
            · have hge := val_const_mul_ge 4 (by norm_num) hx
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
        let l : List ℚ := [-4 * x, (-1 : ℚ)]
        have hrightshape : x ^ 3 + l.sum = x ^ 3 - 4 * x - 1 := by
          simp [l]
          ring
        have hrightgt : ∀ a ∈ l,
            padicValRat 2 (x ^ 3) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have hge := val_const_mul_ge (-4) (by norm_num) hx
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · rw [padicValRat.pow hx, padicValRat.neg, padicValRat.one]
            dsimp [vx] at hvxneg ⊢
            omega
        have hvright0 := val_add_list_eq l (pow_ne_zero 3 hx) hrightgt
        have hvright : padicValRat 2 (x ^ 3 - 4 * x - 1) = 3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 - 4 * x - 1) := by rw [hE]
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

private noncomputable def E21DoubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + 8 * x ^ 2 + 8 * x + 17

private noncomputable def E21DoubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 - x ^ 4 * y - 20 * x ^ 4 - 24 * x ^ 3 -
    8 * x ^ 2 * y - 89 * x ^ 2 - 8 * x * y - 33 * x - 17 * y + 60

private theorem E21DoubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((E21DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((E21DoubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + 8 * (x : ℚ_[2]) ^ 2 +
      8 * (x : ℚ_[2]) + 17 =
    (((x ^ 4 + 8 * x ^ 2 + 8 * x + 17 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E21DoubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((E21DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((E21DoubleYNum x y : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 6 - (x : ℚ_[2]) ^ 4 * (y : ℚ_[2]) -
      20 * (x : ℚ_[2]) ^ 4 - 24 * (x : ℚ_[2]) ^ 3 -
      8 * (x : ℚ_[2]) ^ 2 * (y : ℚ_[2]) - 89 * (x : ℚ_[2]) ^ 2 -
      8 * (x : ℚ_[2]) * (y : ℚ_[2]) - 33 * (x : ℚ_[2]) -
      17 * (y : ℚ_[2]) + 60 =
    (((x ^ 6 - x ^ 4 * y - 20 * x ^ 4 - 24 * x ^ 3 -
      8 * x ^ 2 * y - 89 * x ^ 2 - 8 * x * y - 33 * x -
      17 * y + 60 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E21DoubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (E21DoubleXNum x) := by
  have hnorm := (E21DoubleXNumPadic (ratPadicInt x hx)).2
  change ‖((E21DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E21DoubleXNumPadic_coe x hx,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E21DoubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (E21DoubleYNum x y) := by
  have hnorm := (E21DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((E21DoubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E21DoubleYNumPadic_coe x y hx hy,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E21_padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE21 x y) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 - 4 * ratPadicInt x hx - 1 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 - 4 * (x : ℚ_[2]) - 1
  unfold OnE21 at hE
  exact_mod_cast hE

private theorem toZMod_nat (n : ℕ) :
    PadicInt.toZMod (n : ℤ_[2]) = (n : ZMod 2) := by
  exact map_natCast (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) n

@[simp] private theorem toZMod_8 : PadicInt.toZMod (8 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_17 : PadicInt.toZMod (17 : ℤ_[2]) = 1 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_20 : PadicInt.toZMod (20 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_24 : PadicInt.toZMod (24 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_89 : PadicInt.toZMod (89 : ℤ_[2]) = 1 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_33 : PadicInt.toZMod (33 : ℤ_[2]) = 1 := by
  rw [map_ofNat]
  decide

@[simp] private theorem toZMod_60 : PadicInt.toZMod (60 : ℤ_[2]) = 0 := by
  rw [map_ofNat]
  decide

private theorem E21DoubleXNumPadic_red_zero
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E21DoubleXNumPadic z) = 1 := by
  simp [E21DoubleXNumPadic, map_add, map_mul, map_pow, hz]

private theorem E21DoubleXNumPadic_red_one
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (E21DoubleXNumPadic z) = 0 := by
  simp [E21DoubleXNumPadic, map_add, map_mul, map_pow, hz] <;> decide

private theorem E21DoubleYNumPadic_red_zero_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (E21DoubleYNumPadic z w) = 1 := by
  simp [E21DoubleYNumPadic, map_add, map_sub, map_mul, map_pow, hz, hw]

private theorem E21DoubleYNumPadic_red_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (E21DoubleYNumPadic z w) = 1 := by
  have hw : PadicInt.toZMod w = 0 ∨ PadicInt.toZMod w = 1 := by
    by_cases hw0 : PadicInt.toZMod w = 0
    · exact Or.inl hw0
    · exact Or.inr (zmod2_nonzero_eq_one _ hw0)
  rcases hw with hw | hw <;>
    simp [E21DoubleYNumPadic, map_add, map_sub, map_mul, map_pow, hz, hw]

private theorem ratPadicInt_E21DoubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (E21DoubleXNum x) (E21DoubleXNum_integral x hx) =
      E21DoubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (E21DoubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_E21DoubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x)
    (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (E21DoubleYNum x y) (E21DoubleYNum_integral x y hx hy) =
      E21DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (E21DoubleYNumPadic_coe x y hx hy).symm

private theorem E21_y_red_one_of_x_red_zero
    {x y : ℚ} (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE21 x y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx) = 0) :
    PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (E21_padicInt_equation hx hy hE)
  simp [map_add, map_sub, map_mul, map_pow, hxred] at heq
  exact heq

private theorem val_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by norm_num : 1 < 2)

private theorem E21_double_formal_of_integral_x_pos
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E21Curve x y}
    (hx : 0 < padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    E21FormalAtTwo
      (2 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := le_of_lt hx
  have hE : OnE21 x y := (E21Curve_equation_iff x y).mp h.1
  have hxn : x ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hx
    omega
  have hxred := ratPadicInt_red_eq_zero_of_val_pos hxn hx
  have hyred := E21_y_red_one_of_x_red_zero hx0 hy hE hxred
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
  by_cases hd : E21DoubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = WeierstrassCurve.Affine.negY E21Curve x y := by
      simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at hd ⊢
      linarith
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hYeq]
    trivial
  · have hv2y : padicValRat 2 (2 * y) = 1 := by
      rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn,
        val_two, hvy]
      norm_num
    have hvd : 1 ≤ padicValRat 2 (E21DoubleDen x y) := by
      have hmin := padicValRat.min_le_padicValRat_add (p := 2)
        (q := 2 * y) (r := x) (by simpa [E21DoubleDen] using hd)
      rw [hv2y, min_eq_left (by omega)] at hmin
      simpa [E21DoubleDen] using hmin
    have hNi := E21DoubleXNum_integral x hx0
    have hYi := E21DoubleYNum_integral x y hx0 hy
    have hNred : PadicInt.toZMod
        (ratPadicInt (E21DoubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_E21DoubleXNum x hx0]
      exact E21DoubleXNumPadic_red_zero hxred
    have hYred : PadicInt.toZMod
        (ratPadicInt (E21DoubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_E21DoubleYNum x y hx0 hy]
      exact E21DoubleYNumPadic_red_zero_one hxred hyred
    have hN : E21DoubleXNum x ≠ 0 := by
      intro hzero
      have : ratPadicInt (E21DoubleXNum x) hNi = 0 := by
        apply Subtype.ext
        change ((E21DoubleXNum x : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hNred
      norm_num at hNred
    have hY : E21DoubleYNum x y ≠ 0 := by
      intro hzero
      have : ratPadicInt (E21DoubleYNum x y) hYi = 0 := by
        apply Subtype.ext
        change ((E21DoubleYNum x y : ℚ) : ℚ_[2]) = 0
        simp [hzero]
      rw [this, map_zero] at hYred
      norm_num at hYred
    have hvN : padicValRat 2 (E21DoubleXNum x) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hN hNi (by
        rw [hNred]
        norm_num)
    have hvY : padicValRat 2 (E21DoubleYNum x y) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hY hYi (by
        rw [hYred]
        norm_num)
    have hneg : y ≠ WeierstrassCurve.Affine.negY E21Curve x y := by
      intro heq
      apply hd
      simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at heq ⊢
      linarith
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (E21DoubleDen x y), by omega, ?_, ?_⟩
    · rw [E21_doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN,
        padicValRat.pow hd]
      ring
    · rw [E21_doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY,
        padicValRat.pow hd]
      ring

private theorem E21_four_formal_of_integral_x_zero
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E21Curve x y}
    (hx : padicValRat 2 x = 0) (hy : 0 ≤ padicValRat 2 y) :
    E21FormalAtTwo
      (4 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hE : OnE21 x y := (E21Curve_equation_iff x y).mp h.1
  have hxn : x ≠ 0 := by
    intro hzero
    rw [hzero] at hE
    unfold OnE21 at hE
    norm_num at hE
    nlinarith [sq_nonneg y]
  have hx0 : 0 ≤ padicValRat 2 x := by omega
  have hxred := ratPadicInt_red_eq_one_of_val_zero hxn hx
  have hd : E21DoubleDen x y ≠ 0 := by
    intro hdzero
    have heq : x = -(2 * y) := by
      unfold E21DoubleDen at hdzero
      linarith
    by_cases hyn : y = 0
    · rw [hyn] at heq
      norm_num at heq
      exact hxn heq
    · have hv2y : 1 ≤ padicValRat 2 (2 * y) := by
        rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn,
          val_two]
        omega
      rw [heq, padicValRat.neg] at hx
      omega
  have hvd : padicValRat 2 (E21DoubleDen x y) = 0 := by
    by_cases hyn : y = 0
    · simp [E21DoubleDen, hyn, hx]
    · have hv2y : 0 < padicValRat 2 (2 * y) := by
        rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hyn,
          val_two]
        omega
      have hv := val_add_eq_left_of_lt hxn (by simpa [hx] using hv2y)
      rw [hx] at hv
      simpa [E21DoubleDen, add_comm] using hv
  have hNi := E21DoubleXNum_integral x hx0
  have hYi := E21DoubleYNum_integral x y hx0 hy
  have hNred : PadicInt.toZMod
      (ratPadicInt (E21DoubleXNum x) hNi) = 0 := by
    rw [ratPadicInt_E21DoubleXNum x hx0]
    exact E21DoubleXNumPadic_red_one hxred
  have hYred : PadicInt.toZMod
      (ratPadicInt (E21DoubleYNum x y) hYi) = 1 := by
    rw [ratPadicInt_E21DoubleYNum x y hx0 hy]
    exact E21DoubleYNumPadic_red_one hxred
  have hN : E21DoubleXNum x ≠ 0 := by
    have hid : E21DoubleXNum x =
        (x ^ 2) ^ 2 + 2 * (2 * x + 1) ^ 2 + 15 := by
      unfold E21DoubleXNum
      ring
    rw [hid]
    positivity
  have hY : E21DoubleYNum x y ≠ 0 := by
    intro hzero
    have : ratPadicInt (E21DoubleYNum x y) hYi = 0 := by
      apply Subtype.ext
      change ((E21DoubleYNum x y : ℚ) : ℚ_[2]) = 0
      simp [hzero]
    rw [this, map_zero] at hYred
    norm_num at hYred
  have hvN : 0 < padicValRat 2 (E21DoubleXNum x) :=
    val_pos_of_rational_padicInt_red_zero hN hNi hNred
  have hvY : padicValRat 2 (E21DoubleYNum x y) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hY hYi (by
      rw [hYred]
      norm_num)
  have hneg : y ≠ WeierstrassCurve.Affine.negY E21Curve x y := by
    intro heq
    apply hd
    simp [E21DoubleDen, E21Curve, WeierstrassCurve.Affine.negY] at heq ⊢
    linarith
  have hfour : 4 • WeierstrassCurve.Affine.Point.some x y h =
      2 • (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) := by
    rw [← two_nsmul]
    norm_num [← mul_nsmul]
  rw [hfour, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
  apply E21_double_formal_of_integral_x_pos
  · rw [E21_doubleX_formula hd hE,
      padicValRat.div hN (pow_ne_zero 2 hd),
      padicValRat.pow hd, hvd]
    omega
  · rw [E21_doubleY_formula hd hE,
      padicValRat.div hY (pow_ne_zero 3 hd), hvY,
      padicValRat.pow hd, hvd]
    norm_num

/-- Doubling preserves the formal kernel at two. -/
theorem E21FormalAtTwo_double {P : E21Point}
    (hP : E21FormalAtTwo P) : E21FormalAtTwo (2 • P) := by
  rw [E21FormalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases E21FormalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-- Four times every rational point is in the formal kernel at two. -/
theorem E21_four_nsmul_formal (P : E21Point) :
    E21FormalAtTwo (4 • P) := by
  rcases E21_formal_or_integral P with hformal | hintegral
  · have h2 := E21FormalAtTwo_double hformal
    have h4 := E21FormalAtTwo_double h2
    rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]]
    exact h4
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hx, hy⟩
        by_cases hx0 : padicValRat 2 x = 0
        · exact E21_four_formal_of_integral_x_zero hx0 hy
        · have hxpos : 0 < padicValRat 2 x := lt_of_le_of_ne hx (Ne.symm hx0)
          have h2 := E21_double_formal_of_integral_x_pos
            (h := h) hxpos hy
          have h4 := E21FormalAtTwo_double h2
          rw [show 4 • WeierstrassCurve.Affine.Point.some x y h =
              2 • (2 • WeierstrassCurve.Affine.Point.some x y h) by
                norm_num [← mul_nsmul]]
          exact h4

private theorem E21FormalLevel_unique {P : E21Point} {k l : ℤ}
    (hk : E21FormalLevel P k) (hl : E21FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [E21FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Repeated doubling of a nonzero formal point raises its formal level by
at least the number of doublings. -/
theorem E21FormalLevel_two_power {P : E21Point} {k : ℤ}
    (hP : E21FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + (n : ℤ) ≤ k' ∧
        E21FormalLevel ((2 ^ n : ℕ) • P) k' := by
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
      · rcases E21FormalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [hpow, hzero]
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rwa [hpow]

/-- The two-adic formal kernel has no nonzero element divisible by every
power of two through points of the formal kernel. -/
theorem E21_formal_separated (P : E21Point)
    (hP : E21FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : E21Point,
      E21FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, E21FormalLevel P k := by
    rw [E21FormalAtTwo_iff] at hP
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
  have hlevelQ : ∃ l : ℤ, E21FormalLevel Q l := by
    rw [E21FormalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x y h => exact hl.1
  rcases E21FormalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : E21FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := E21FormalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k := by
      exact Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat] at hbound
    omega

/-- The two-isogeny descent and two-adic separatedness imply that every
rational point of `E₁` is killed by four. -/
theorem E1_four_nsmul_eq_zero (P : E1Point) : 4 • P = 0 := by
  let P0 : E21Point := E21E1AddEquiv.symm P
  have hP0formal : E21FormalAtTwo (4 • P0) :=
    E21_four_nsmul_formal P0
  have hdiv : ∀ n : ℕ, ∃ Q0 : E21Point,
      E21FormalAtTwo Q0 ∧
        4 • P0 = (2 ^ n : ℕ) • Q0 := by
    intro n
    obtain ⟨Q, hQ⟩ := E1_four_nsmul_two_power_divisible P n
    refine ⟨4 • E21E1AddEquiv.symm Q,
      E21_four_nsmul_formal (E21E1AddEquiv.symm Q), ?_⟩
    have hm := congrArg E21E1AddEquiv.symm hQ
    simpa only [map_nsmul, AddEquiv.symm_apply_apply, P0] using hm
  have hzero : 4 • P0 = 0 :=
    E21_formal_separated (4 • P0) hP0formal hdiv
  have hm := congrArg E21E1AddEquiv hzero
  simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, P0] using hm

private theorem E1_y_zero_of_double_zero {u W : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular E1Curve u W}
    (h2 : 2 • (WeierstrassCurve.Affine.Point.some u W h : E1Point) = 0) :
    W = 0 := by
  have hadd : (WeierstrassCurve.Affine.Point.some u W h : E1Point) +
      WeierstrassCurve.Affine.Point.some u W h = 0 := by
    simpa only [two_nsmul] using h2
  have hneg := eq_neg_of_add_eq_zero_left hadd
  rw [WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hneg
  simp [E1Curve, WeierstrassCurve.Affine.negY] at hneg
  linarith [hneg]

private theorem E1_doubleX_formula {u W : ℚ}
    (hW : W ≠ 0) (hE : OnE1 u W) :
    WeierstrassCurve.Affine.addX E1Curve u u
        (WeierstrassCurve.Affine.slope E1Curve u u W W) =
      (u ^ 2 - 144) ^ 2 / (4 * W ^ 2) := by
  rw [E1Curve_slope_self hW, E1Curve_addX_tangent]
  unfold tangentX E1Tangent OnE1 at *
  field_simp [hW]
  rw [hE]
  ring

/-- The rational affine points of `E₁` are exactly its seven nonzero
four-torsion points. -/
theorem E1_affine_exhaustion {u W : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E1Curve u W) :
    (u = 0 ∧ W = 0) ∨
    (u = -9 ∧ W = 0) ∨
    (u = -16 ∧ W = 0) ∨
    (u = -12 ∧ W = -12) ∨
    (u = -12 ∧ W = 12) ∨
    (u = 12 ∧ W = 84) ∨
    (u = 12 ∧ W = -84) := by
  have hE : OnE1 u W := (E1Curve_equation_iff u W).mp h.1
  by_cases hW : W = 0
  · have hprod : u * (u + 9) * (u + 16) = 0 := by
      unfold OnE1 at hE
      calc
        u * (u + 9) * (u + 16) = W ^ 2 := hE.symm
        _ = 0 := by rw [hW]; norm_num
    rcases mul_eq_zero.mp hprod with hleft | h16
    · rcases mul_eq_zero.mp hleft with hu | h9
      · exact Or.inl ⟨hu, hW⟩
      · right
        left
        exact ⟨by linarith, hW⟩
    · right
      right
      left
      exact ⟨by linarith, hW⟩
  · let P : E1Point := WeierstrassCurve.Affine.Point.some u W h
    have hfour : 2 • (2 • P) = 0 := by
      have h4 := E1_four_nsmul_eq_zero P
      rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]] at h4
      exact h4
    have hneg : W ≠ WeierstrassCurve.Affine.negY E1Curve u W :=
      E1_y_ne_negY hW
    dsimp only [P] at hfour
    simp only [two_nsmul] at hfour
    rw [
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg] at hfour
    let u2 := WeierstrassCurve.Affine.addX E1Curve u u
      (WeierstrassCurve.Affine.slope E1Curve u u W W)
    let W2 := WeierstrassCurve.Affine.addY E1Curve u u W
      (WeierstrassCurve.Affine.slope E1Curve u u W W)
    have hW2 : W2 = 0 := by
      apply E1_y_zero_of_double_zero
      simpa only [two_nsmul] using hfour
    have hns2 : WeierstrassCurve.Affine.Nonsingular E1Curve u2 W2 := by
      dsimp only [u2, W2]
      exact WeierstrassCurve.Affine.nonsingular_add h h
        (fun hbad => hneg hbad.2)
    have hE2 : OnE1 u2 W2 := (E1Curve_equation_iff u2 W2).mp hns2.1
    have hprod2 : u2 * (u2 + 9) * (u2 + 16) = 0 := by
      unfold OnE1 at hE2
      calc
        u2 * (u2 + 9) * (u2 + 16) = W2 ^ 2 := hE2.symm
        _ = 0 := by rw [hW2]; norm_num
    have hu2cases : u2 = 0 ∨ u2 = -9 ∨ u2 = -16 := by
      rcases mul_eq_zero.mp hprod2 with hleft | h16
      · rcases mul_eq_zero.mp hleft with hu0 | h9
        · exact Or.inl hu0
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    have hu2formula : u2 = (u ^ 2 - 144) ^ 2 / (4 * W ^ 2) := by
      exact E1_doubleX_formula hW hE
    have hu2nonneg : 0 ≤ u2 := by
      rw [hu2formula]
      positivity
    have hu2 : u2 = 0 := by
      rcases hu2cases with hu20 | hu29 | hu216
      · exact hu20
      · linarith
      · linarith
    have husq : u ^ 2 = 144 := by
      rw [hu2] at hu2formula
      have hden : 4 * W ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hW)
      have hnum : (u ^ 2 - 144) ^ 2 = 0 := by
        exact ((div_eq_zero_iff).mp hu2formula.symm).resolve_right hden
      nlinarith [sq_nonneg (u ^ 2 - 144)]
    have hufactor : (u - 12) * (u + 12) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hufactor with hu12 | hum12
    · have hu : u = 12 := by linarith
      have hWsq : W ^ 2 = 84 ^ 2 := by
        unfold OnE1 at hE
        rw [hu] at hE
        norm_num at hE ⊢
        exact hE
      have hWfactor : (W - 84) * (W + 84) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hWfactor with hWp | hWm
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hu, by linarith⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨hu, by linarith⟩)))))
    · have hu : u = -12 := by linarith
      have hWsq : W ^ 2 = 12 ^ 2 := by
        unfold OnE1 at hE
        rw [hu] at hE
        norm_num at hE ⊢
        exact hE
      have hWfactor : (W - 12) * (W + 12) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hWfactor with hWp | hWm
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hu, by linarith⟩))))
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hu, by linarith⟩)))

/-- The seven affine rational points on the good conductor-21 model.  Along
with the point at infinity this gives `#E₀(ℚ) = 8`. -/
theorem E21_affine_exhaustion {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E21Curve x y) :
    (x = -2 ∧ y = 1) ∨
    (x = 2 ∧ y = -1) ∨
    (x = -1 / 4 ∧ y = 1 / 8) ∨
    (x = -1 ∧ y = -1) ∨
    (x = -1 ∧ y = 2) ∨
    (x = 5 ∧ y = 8) ∨
    (x = 5 ∧ y = -13) := by
  have hE : OnE21 x y := (E21Curve_equation_iff x y).mp h.1
  have hOn1 : OnE1 (4 * (x - 2)) (4 * (2 * y + x)) := by
    unfold OnE1 OnE21 at *
    ring_nf at hE ⊢
    nlinarith
  have h1 : WeierstrassCurve.Affine.Nonsingular E1Curve
      (4 * (x - 2)) (4 * (2 * y + x)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E1Curve_equation_iff _ _).mpr hOn1)
  rcases E1_affine_exhaustion h1 with h0 | h9 | h16 |
      hm12m | hm12p | h12p | h12m
  · right; left
    constructor <;> linarith [h0.1, h0.2]
  · right; right; left
    constructor <;> linarith [h9.1, h9.2]
  · left
    constructor <;> linarith [h16.1, h16.2]
  · right; right; right; left
    constructor <;> linarith [hm12m.1, hm12m.2]
  · right; right; right; right; left
    constructor <;> linarith [hm12p.1, hm12p.2]
  · right; right; right; right; right; left
    constructor <;> linarith [h12p.1, h12p.2]
  · right; right; right; right; right; right
    constructor <;> linarith [h12m.1, h12m.2]

/-! ## The seven finite fibres -/

private theorem R_at_neg_one (s : ℚ) :
    R21 s (-1) = -(s - 6) ^ 2 := by
  unfold R21
  ring

private theorem R_at_neg_quarter (s : ℚ) :
    R21 s (-1 / 4) = -(2 * s + 33) ^ 2 / 256 := by
  unfold R21
  ring

private theorem R_at_zero (s : ℚ) : R21 s 0 = -s := by
  unfold R21
  ring

private theorem R_at_one_third (s : ℚ) :
    R21 s (1 / 3) = (s - 8) ^ 2 / 27 := by
  unfold R21
  ring

private theorem R_at_neg_two (s : ℚ) :
    R21 s (-2) = -(8 * s - 15) * (s - 8) := by
  unfold R21
  ring

private theorem w_at_neg_two (s : ℚ) :
    w21 s (-2) = (79 - 16 * s) / 7 := by
  norm_num [w21]
  ring

open Polynomial

private theorem monic_cubic_constant_one_root_pm_one
    (a b : ℤ) {t : ℚ}
    (h : t ^ 3 + (a : ℚ) * t ^ 2 + (b : ℚ) * t + 1 = 0) :
    t = 1 ∨ t = -1 := by
  let p : ℤ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C 1
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval t p = 0 := by
    dsimp only [p]
    simp only [aeval_def, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C]
    norm_cast
  rcases exists_integer_of_is_root_of_monic
      (A := ℤ) (K := ℚ) hpmonic hroot with ⟨z, htz, hzdiv⟩
  have hzdiv1 : z ∣ (1 : ℤ) := by
    simpa [p] using hzdiv
  have hunit : IsUnit z := isUnit_of_dvd_one hzdiv1
  rcases Int.isUnit_iff.mp hunit with hz | hz
  · left
    simpa [hz] using htz
  · right
    simpa [hz] using htz

private theorem int_dvd_two_cases {z : ℤ} (hz : z ∣ (2 : ℤ)) :
    z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  have habs : z.natAbs ∣ 2 := (Int.natAbs_dvd_natAbs).mpr hz
  have habsCases : z.natAbs = 1 ∨ z.natAbs = 2 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp habs
  rcases habsCases with h1 | h2
  · rcases Int.natAbs_eq_iff.mp h1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · rcases Int.natAbs_eq_iff.mp h2 with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))

private theorem nat_dvd_eight_cases {n : ℕ} (hn : n ∣ 8) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  have hn' : n ∣ 2 ^ 3 := by
    norm_num
    exact hn
  obtain ⟨k, hk, hnk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hn'
  rw [hnk]
  interval_cases k <;> norm_num

private theorem int_dvd_eight_cases {z : ℤ} (hz : z ∣ (8 : ℤ)) :
    z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 ∨
    z = 4 ∨ z = -4 ∨ z = 8 ∨ z = -8 := by
  have habs : z.natAbs ∣ 8 := (Int.natAbs_dvd_natAbs).mpr hz
  rcases nat_dvd_eight_cases habs with h1 | h2 | h4 | h8
  · rcases Int.natAbs_eq_iff.mp h1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · rcases Int.natAbs_eq_iff.mp h2 with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
  · rcases Int.natAbs_eq_iff.mp h4 with hz | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz)))))
  · rcases Int.natAbs_eq_iff.mp h8 with hz | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hz))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr hz))))))

private theorem cubic_six_ne_zero (t : ℚ) :
    t ^ 3 - 6 * t ^ 2 + 3 * t + 1 ≠ 0 := by
  intro h
  have hc := monic_cubic_constant_one_root_pm_one (-6) 3 (t := t) (by
    simpa [sub_eq_add_neg] using h)
  rcases hc with rfl | rfl <;> norm_num at h

private theorem cubic_zero_ne_zero (t : ℚ) :
    t ^ 3 - 3 * t + 1 ≠ 0 := by
  intro h
  have hc := monic_cubic_constant_one_root_pm_one 0 (-3) (t := t) (by
    simpa [sub_eq_add_neg] using h)
  rcases hc with rfl | rfl <;> norm_num at h

private theorem cubic_eight_ne_zero (t : ℚ) :
    t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0 := by
  intro h
  have hc := monic_cubic_constant_one_root_pm_one (-8) 5 (t := t) (by
    simpa [sub_eq_add_neg] using h)
  rcases hc with rfl | rfl <;> norm_num at h

private theorem cubic_neg_33_half_ne_zero (t : ℚ) :
    2 * t ^ 3 + 33 * t ^ 2 - 39 * t + 2 ≠ 0 := by
  intro h
  let p : ℤ[X] := C 2 * X ^ 3 + C 33 * X ^ 2 - C 39 * X + C 2
  have hroot : aeval t p = 0 := by
    simp [p, aeval_def]
    ring_nf at h ⊢
    exact h
  have hn : IsFractionRing.num ℤ t ∣ (2 : ℤ) := by
    simpa [p] using num_dvd_of_is_root hroot
  have hd : (IsFractionRing.den ℤ t : ℤ) ∣ (2 : ℤ) := by
    have hd0 := den_dvd_of_is_root hroot
    have hlc : p.leadingCoeff = 2 := by
      have hp : p = Cubic.toPoly (⟨2, 33, -39, 2⟩ : Cubic ℤ) := by
        simp [p, Cubic.toPoly]
        ring
      rw [hp]
      exact Cubic.leadingCoeff_of_a_ne_zero (by norm_num)
    rwa [hlc] at hd0
  have hfrac := IsFractionRing.mk'_num_den' ℤ t
  rcases int_dvd_two_cases hn with hn | hn | hn | hn <;>
    rcases int_dvd_two_cases hd with hd | hd | hd | hd <;>
    rw [hn, hd] at hfrac <;> norm_num at hfrac <;>
    rw [← hfrac] at h <;> norm_num at h

private theorem cubic_15_eighth_ne_zero (t : ℚ) :
    8 * t ^ 3 - 15 * t ^ 2 - 9 * t + 8 ≠ 0 := by
  intro h
  let p : ℤ[X] := C 8 * X ^ 3 - C 15 * X ^ 2 - C 9 * X + C 8
  have hroot : aeval t p = 0 := by
    simp [p, aeval_def]
    ring_nf at h ⊢
    exact h
  have hn : IsFractionRing.num ℤ t ∣ (8 : ℤ) := by
    simpa [p] using num_dvd_of_is_root hroot
  have hd : (IsFractionRing.den ℤ t : ℤ) ∣ (8 : ℤ) := by
    have hd0 := den_dvd_of_is_root hroot
    have hlc : p.leadingCoeff = 8 := by
      have hp : p = Cubic.toPoly (⟨8, -15, -9, 8⟩ : Cubic ℤ) := by
        simp [p, Cubic.toPoly]
        ring
      rw [hp]
      exact Cubic.leadingCoeff_of_a_ne_zero (by norm_num)
    rwa [hlc] at hd0
  have hfrac := IsFractionRing.mk'_num_den' ℤ t
  rcases int_dvd_eight_cases hn with hn | hn | hn | hn | hn | hn | hn | hn <;>
    rcases int_dvd_eight_cases hd with hd | hd | hd | hd | hd | hd | hd | hd <;>
    rw [hn, hd] at hfrac <;> norm_num at hfrac <;>
    rw [← hfrac] at h <;> norm_num at h

/-- There is no affine rational point on the order-21 quotient above a
nondegenerate order-seven parameter. -/
theorem G21_ne_zero_of_t_ne_zero_one
    (t X : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    G21 t X ≠ 0 := by
  intro hG
  let s : ℚ := s21 t
  let r : ℚ := r21 t X
  have hR : R21 s r = 0 := by
    have hc := quotient_certificate t X ht0 ht1
    rw [hG, mul_zero] at hc
    have hfac : t ^ 8 * (t - 1) ^ 8 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 8 ht0)
        (pow_ne_zero 8 (sub_ne_zero.mpr ht1))
    exact (mul_eq_zero.mp hc).resolve_left hfac
  have hE : OnE21 (e21x r) (e21y s r) := map_to_E21 s r hR
  have hns : WeierstrassCurve.Affine.Nonsingular E21Curve
      (e21x r) (e21y s r) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E21Curve_equation_iff _ _).mpr hE)
  have hcubic :
      t ^ 3 - s * t ^ 2 + (s - 3) * t + 1 = 0 := by
    simpa only [s] using s21_cubic t ht0 ht1
  rcases E21_affine_exhaustion hns with hneg2 | h2 | hquarter |
      hneg1neg | hneg1pos | h5pos | h5neg
  · have hr : r = 1 / 3 := by
      unfold e21x at hneg2
      linarith [hneg2.1]
    have hRs := hR
    rw [hr, R_at_one_third] at hRs
    have hs : s = 8 := by
      field_simp at hRs
      nlinarith [sq_nonneg (s - 8)]
    apply cubic_eight_ne_zero t
    rw [hs] at hcubic
    norm_num at hcubic ⊢
    exact hcubic
  · have hr : r = -1 := by
      unfold e21x at h2
      linarith [h2.1]
    have hRs := hR
    rw [hr, R_at_neg_one] at hRs
    have hs : s = 6 := by
      nlinarith [sq_nonneg (s - 6)]
    apply cubic_six_ne_zero t
    rw [hs] at hcubic
    norm_num at hcubic ⊢
    exact hcubic
  · have hr : r = -1 / 4 := by
      unfold e21x at hquarter
      linarith [hquarter.1]
    have hRs := hR
    rw [hr, R_at_neg_quarter] at hRs
    have hs : s = -33 / 2 := by
      field_simp at hRs
      nlinarith [sq_nonneg (2 * s + 33)]
    apply cubic_neg_33_half_ne_zero t
    rw [hs] at hcubic
    nlinarith
  · have hr : r = 0 := by
      unfold e21x at hneg1neg
      linarith [hneg1neg.1]
    have hRs := hR
    rw [hr, R_at_zero] at hRs
    have hs : s = 0 := by linarith
    apply cubic_zero_ne_zero t
    rw [hs] at hcubic
    simpa [sub_eq_add_neg] using hcubic
  · have hr : r = 0 := by
      unfold e21x at hneg1pos
      linarith [hneg1pos.1]
    have hy := hneg1pos.2
    rw [hr] at hy
    norm_num [e21y, w21] at hy
  · have hr : r = -2 := by
      unfold e21x at h5pos
      linarith [h5pos.1]
    have hy := h5pos.2
    rw [hr] at hy
    have hw : w21 s (-2) = 7 := by
      unfold e21y at hy
      linarith
    rw [w_at_neg_two] at hw
    have hs : s = 15 / 8 := by
      field_simp at hw
      linarith
    apply cubic_15_eighth_ne_zero t
    rw [hs] at hcubic
    nlinarith
  · have hr : r = -2 := by
      unfold e21x at h5neg
      linarith [h5neg.1]
    have hy := h5neg.2
    rw [hr] at hy
    have hw : w21 s (-2) = -7 := by
      unfold e21y at hy
      linarith
    rw [w_at_neg_two] at hw
    have hs : s = 8 := by
      field_simp at hw
      linarith
    apply cubic_eight_ne_zero t
    rw [hs] at hcubic
    norm_num at hcubic ⊢
    exact hcubic

end

end MazurProof.RationalPointsX121
