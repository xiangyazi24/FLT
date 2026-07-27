import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Vélu 2-isogeny construction

Explicit Vélu formulas for degree-2 isogenies of elliptic curves over ℚ,
replacing `exists_rational_two_isogeny_quotient`.

## Strategy

Work in short Weierstrass form y² = x³ + Ax + B with 2-torsion Q = (r, 0).
Vélu formulas:
- E' : y² = x³ + A'x + B', A' = A - 5t, B' = B - 7rt, t = 3r² + A
- φ(x,y) = (x + t/(x-r), y·((x-r)²-t)/(x-r)²)
- η = (-2r, 0) ∈ E'[2]

For general Weierstrass, reduce to short form via `VariableChangePointAddEquiv`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.VeluTwoIsogeny

noncomputable section

open WeierstrassCurve.Affine (Equation Nonsingular Point equation_iff_nonsingular
  equation_iff negY slope addX addY)

/-! ## Short Weierstrass definitions -/

@[reducible] def shortWS (A B : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0; a₄ := A; a₆ := B

def veluT (A r : ℚ) : ℚ := 3 * r ^ 2 + A

@[reducible] def veluQuotCurve (A B r : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0
  a₄ := A - 5 * veluT A r
  a₆ := B - 7 * r * veluT A r

/-! ## Equation lemmas -/

lemma shortWS_equation {A B x y : ℚ} :
    Equation (shortWS A B) x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  simp only [equation_iff, shortWS]; constructor <;> intro h <;> linarith

lemma veluQuotCurve_equation {A B r x y : ℚ} :
    Equation (veluQuotCurve A B r) x y ↔
    y ^ 2 = x ^ 3 + (A - 5 * veluT A r) * x + (B - 7 * r * veluT A r) := by
  simp only [equation_iff, veluQuotCurve]; constructor <;> intro h <;> linarith

/-! ## Well-definedness -/

lemma velu_equation {A B r x y : ℚ}
    (hcurve : Equation (shortWS A B) x y)
    (htors : r ^ 3 + A * r + B = 0)
    (hx : x ≠ r) :
    Equation (veluQuotCurve A B r)
      (x + veluT A r / (x - r))
      (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) := by
  rw [veluQuotCurve_equation]
  have hcurve' := shortWS_equation.mp hcurve
  have hd : x - r ≠ 0 := sub_ne_zero.mpr hx
  unfold veluT
  field_simp
  linear_combination
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     4 * r ^ 4 + 8 * r ^ 3 * x - 4 * r * x ^ 3 + x ^ 4) * hcurve' +
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     3 * r ^ 4 + 12 * r ^ 3 * x - 6 * r ^ 2 * x ^ 2) * htors

/-! ## IsElliptic instances -/

lemma shortWS_Δ (A B : ℚ) :
    (shortWS A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [shortWS, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma shortWS_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (shortWS A B).Δ = -16 * (A + 3 * r ^ 2) ^ 2 * (4 * A + 3 * r ^ 2) := by
  rw [shortWS_Δ]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (veluQuotCurve A B r).Δ = 256 * (A + 3 * r ^ 2) * (4 * A + 3 * r ^ 2) ^ 2 := by
  simp only [veluQuotCurve, veluT, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_isElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hE : (shortWS A B).IsElliptic) :
    (veluQuotCurve A B r).IsElliptic := by
  have hΔ := hE.isUnit
  rw [shortWS_Δ_factor htors] at hΔ
  have hne := isUnit_iff_ne_zero.mp hΔ
  have h1 : A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  have h2 : 4 * A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  constructor
  rw [veluQuotCurve_Δ_factor htors]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (256 : ℚ) ≠ 0) h1)
    (pow_ne_zero 2 h2)).isUnit

/-! ## The Vélu point map -/

def veluMapPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) → Point (veluQuotCurve A B r)
  | .zero => .zero
  | .some x y h =>
    if hx : x = r then .zero
    else
      .some (x + veluT A r / (x - r))
        (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2)
        (equation_iff_nonsingular.mp (velu_equation h.left htors hx))

@[simp] lemma veluMapPoint_zero {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    veluMapPoint htors (0 : Point (shortWS A B)) = 0 := rfl

/-! ## Kernel -/

lemma torsion_point_on_curve {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Nonsingular (shortWS A B) r 0 :=
  equation_iff_nonsingular.mp (shortWS_equation.mpr (by nlinarith))

def torsionPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Point (shortWS A B) :=
  .some r 0 (torsion_point_on_curve htors)

@[simp] lemma veluMapPoint_torsion {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    veluMapPoint htors (torsionPoint htors) = 0 := by
  show veluMapPoint htors (torsionPoint htors) = Point.zero
  unfold veluMapPoint torsionPoint; simp

lemma veluMapPoint_eq_zero_iff {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P : Point (shortWS A B)) :
    veluMapPoint htors P = 0 ↔
      P = 0 ∨ P = torsionPoint htors := by
  constructor
  · intro h
    match P with
    | .zero => exact Or.inl rfl
    | .some x y hns =>
      unfold veluMapPoint at h
      by_cases hx : x = r
      · right
        have hcurve := shortWS_equation.mp hns.left
        rw [hx] at hcurve
        have hy2 : y ^ 2 = 0 := by linarith
        have hy : y = 0 := by nlinarith [sq_nonneg y]
        subst hx; subst hy
        simp [torsionPoint]
      · simp only [hx, dite_false] at h
        exact absurd h (Point.some_ne_zero _)
  · rintro (rfl | rfl)
    · exact veluMapPoint_zero
    · exact veluMapPoint_torsion

private lemma point_some_congr {W : WeierstrassCurve ℚ} {a b c d : ℚ}
    {h₁ : Nonsingular W a b} {h₂ : Nonsingular W c d}
    (hx : a = c) (hy : b = d) :
    (Point.some a b h₁ : Point W) = Point.some c d h₂ := by
  subst hx; subst hy; rfl

/-! ## Homomorphism via the standard two-isogeny

Translate the rational 2-torsion point to `(0, 0)`.  The Vélu map then becomes
the standard degree-two map on `y² = x(x² + ax + b)`.  Its additivity is proved
from the dual-composition doubling identity and the description of its fibres as
cosets of the kernel; the final bridge is an additive change of variables.
-/

private lemma torsion_y_zero {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : Equation (shortWS A B) x y) (hx : x = r) : y = 0 := by
  have := shortWS_equation.mp hcurve
  rw [hx] at this
  nlinarith [sq_nonneg y]

namespace StandardTwoIsogeny

open WeierstrassCurve.Affine

/-! ### The standard model and its two maps -/

@[reducible] def curve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a
  a₃ := 0
  a₄ := b
  a₆ := 0

lemma curve_equation {a b x y : ℚ} :
    Equation (curve a b) x y ↔ y ^ 2 = x * (x ^ 2 + a * x + b) := by
  rw [equation_iff]
  simp only [curve]
  constructor <;> intro h <;> nlinarith

def fx (x y : ℚ) : ℚ := y ^ 2 / x ^ 2
def fy (b x y : ℚ) : ℚ := y * (b - x ^ 2) / x ^ 2
def dx (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4
def dy (a b x y : ℚ) : ℚ := y * ((a ^ 2 - 4 * b) - x ^ 2) / x ^ 2 / 8

lemma forward_equation {a b x y : ℚ}
    (h : Equation (curve a b) x y) (hx : x ≠ 0) :
    Equation (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x y) (fy b x y) := by
  rw [curve_equation]
  have heq := curve_equation.mp h
  unfold fx fy
  field_simp [hx]
  rw [heq]
  ring

lemma dual_equation {a b x y : ℚ}
    (h : Equation (curve (-2 * a) (a ^ 2 - 4 * b)) x y) (hx : x ≠ 0) :
    Equation (curve a b) (dx x y) (dy a b x y) := by
  rw [curve_equation]
  have heq := curve_equation.mp h
  unfold dx dy
  field_simp [hx]
  rw [heq]
  ring

def tangent (a b x y : ℚ) : ℚ := (3 * x ^ 2 + 2 * a * x + b) / (2 * y)
def tx (a x m : ℚ) : ℚ := m ^ 2 - a - 2 * x
def ty (a x y m : ℚ) : ℚ := -(m * (tx a x m - x) + y)

lemma dual_forward_x {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    dx (fx x y) (fy b x y) = tx a x (tangent a b x y) := by
  unfold dx fx fy tx tangent
  field_simp [hx, hy]
  rw [h]
  ring

lemma dual_forward_y {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    dy a b (fx x y) (fy b x y) = ty a x y (tangent a b x y) := by
  unfold dy fx fy ty tx tangent
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x ^ 2 + a * x + b)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  rw [hy4, h]
  ring

lemma forward_dual_x {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) :
    fx (dx x y) (dy a b x y) =
      tx (-2 * a) x (tangent (-2 * a) (a ^ 2 - 4 * b) x y) := by
  unfold fx dx dy tx tangent
  field_simp [hx, hy]
  rw [h]
  ring

lemma forward_dual_y {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) :
    fy b (dx x y) (dy a b x y) =
      ty (-2 * a) x y (tangent (-2 * a) (a ^ 2 - 4 * b) x y) := by
  unfold fy dx dy ty tx tangent
  field_simp [hx, hy]
  have hy4 :
      y ^ 4 = (x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  rw [hy4, h]
  ring

noncomputable def pointMap {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve a b) → Point (curve (-2 * a) (a ^ 2 - 4 * b))
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (fx x y) (fy b x y)
        (equation_iff_nonsingular.mp (forward_equation h.left hx))

noncomputable def dualPoint {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) → Point (curve a b)
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (dx x y) (dy a b x y)
        (equation_iff_nonsingular.mp (dual_equation h.left hx))

@[simp] lemma pointMap_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    pointMap (a := a) (b := b) 0 = 0 := rfl

@[simp] lemma dualPoint_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    dualPoint (a := a) (b := b) 0 = 0 := rfl

lemma pointMap_some {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    pointMap (a := a) (b := b) (.some x y h) =
      .some (fx x y) (fy b x y)
        (equation_iff_nonsingular.mp (forward_equation h.left hx)) := by
  simp [pointMap, hx]

lemma dualPoint_some {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b)) x y) (hx : x ≠ 0) :
    dualPoint (a := a) (b := b) (.some x y h) =
      .some (dx x y) (dy a b x y)
        (equation_iff_nonsingular.mp (dual_equation h.left hx)) := by
  simp [dualPoint, hx]

@[simp] lemma curve_negY (a b x y : ℚ) :
    negY (curve a b) x y = -y := by
  simp [negY, curve]

lemma y_zero_of_x_zero {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x = 0) : y = 0 := by
  have heq := curve_equation.mp h.left
  rw [hx] at heq
  nlinarith

lemma double_eq_zero_of_y_zero {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    (h : Nonsingular (curve a b) x y) (hy : y = 0) :
    2 • (Point.some x y h : Point (curve a b)) = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (by simp [hy, curve_negY])

lemma y_ne_negY {a b x y : ℚ} (hy : y ≠ 0) :
    y ≠ negY (curve a b) x y := by
  rw [curve_negY]
  intro h
  exact hy (by linarith)

lemma slope_self {a b x y : ℚ} (hy : y ≠ 0) :
    slope (curve a b) x x y y = tangent a b x y := by
  rw [slope_of_Y_ne rfl (y_ne_negY hy)]
  simp [curve, tangent, negY]
  ring

lemma addX_self (a b x y : ℚ) :
    addX (curve a b) x x (tangent a b x y) =
      tx a x (tangent a b x y) := by
  simp [curve, addX, tx]
  ring

lemma addY_self (a b x y : ℚ) :
    addY (curve a b) x x y (tangent a b x y) =
      ty a x y (tangent a b x y) := by
  simp only [curve, addY, WeierstrassCurve.Affine.negAddY, negY, addX, ty, tx,
    zero_mul, add_zero, sub_zero]
  ring

/-! ### Dual composition and doubling -/

lemma dual_comp_pointMap {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    dualPoint (a := a) (b := b) (pointMap P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hmap : pointMap (a := a) (b := b) (Point.some x y h) = 0 := by
          show pointMap (a := a) (b := b) (Point.some x y h) = Point.zero
          unfold pointMap
          exact dif_pos hx
        rw [hmap, dualPoint_zero]
        exact (double_eq_zero_of_y_zero h hy).symm
      · rw [pointMap_some h hx]
        by_cases hy : y = 0
        · have hfx : fx x y = 0 := by simp [fx, hy]
          simp only [dualPoint, hfx, dite_true]
          exact (double_eq_zero_of_y_zero h hy).symm
        · have hfx : fx x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          rw [dualPoint_some _ hfx, two_nsmul,
            Point.add_self_of_Y_ne (y_ne_negY hy)]
          rw [Point.some.injEq]
          have heq := curve_equation.mp h.left
          exact ⟨by
            rw [dual_forward_x hx hy heq, slope_self hy, addX_self],
            by rw [dual_forward_y hx hy heq, slope_self hy, addY_self]⟩

lemma pointMap_comp_dual {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve (-2 * a) (a ^ 2 - 4 * b))) :
    pointMap (a := a) (b := b) (dualPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hmap : dualPoint (a := a) (b := b) (Point.some x y h) = 0 := by
          show dualPoint (a := a) (b := b) (Point.some x y h) = Point.zero
          unfold dualPoint
          exact dif_pos hx
        rw [hmap, pointMap_zero]
        exact (double_eq_zero_of_y_zero h hy).symm
      · rw [dualPoint_some h hx]
        by_cases hy : y = 0
        · have hdx : dx x y = 0 := by simp [dx, hy]
          simp only [pointMap, hdx, dite_true]
          exact (double_eq_zero_of_y_zero h hy).symm
        · have hdx : dx x y ≠ 0 :=
            div_ne_zero
              (div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx))
              (by norm_num)
          rw [pointMap_some _ hdx, two_nsmul,
            Point.add_self_of_Y_ne (y_ne_negY hy)]
          rw [Point.some.injEq]
          have heq := curve_equation.mp h.left
          exact ⟨by
            rw [forward_dual_x hx hy heq, slope_self hy, addX_self],
            by rw [forward_dual_y hx hy heq, slope_self hy, addY_self]⟩

lemma pointMap_add_self {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + P) = pointMap P + pointMap P := by
  rw [← two_nsmul]
  calc
    pointMap (2 • P) = pointMap (dualPoint (pointMap P)) := by
      rw [dual_comp_pointMap]
    _ = 2 • pointMap P := pointMap_comp_dual _

/-! ### Kernel translations and fibres -/

def kernelPoint (a b : ℚ) [hE : (curve a b).IsElliptic] :
    Point (curve a b) :=
  .some 0 0 (equation_iff_nonsingular.mp (curve_equation.mpr (by ring)))

lemma b_ne_zero (a b : ℚ) [hE : (curve a b).IsElliptic] : b ≠ 0 := by
  have hns : Nonsingular (curve a b) 0 0 :=
    equation_iff_nonsingular.mp (curve_equation.mpr (by ring))
  have h := (nonsingular_zero (W := curve a b)).mp hns
  simpa [curve] using h.2

@[simp] lemma pointMap_kernel {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    pointMap (kernelPoint a b) = 0 := by
  show pointMap (a := a) (b := b) (kernelPoint a b) = Point.zero
  unfold pointMap kernelPoint
  exact dif_pos rfl

lemma kernel_add_self {a b : ℚ} [hE : (curve a b).IsElliptic] :
    kernelPoint a b + kernelPoint a b = 0 := by
  exact Point.add_self_of_Y_eq (by simp [kernelPoint, curve_negY])

lemma pointMap_neg {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (-P) = -pointMap P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [Point.neg_some, pointMap]
      by_cases hx : x = 0
      · simp only [hx, dite_true]
        rfl
      · simp only [hx, dite_false]
        rw [Point.neg_some]
        congr 1
        · simp [curve_negY, fx]
        · simp only [curve_negY, fy]
          ring

lemma slope_kernel {a b x y : ℚ} (hx : x ≠ 0) :
    slope (curve a b) x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

lemma add_kernel_x {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    addX (curve a b) x 0 (slope (curve a b) x 0 y 0) = b / x := by
  rw [slope_kernel hx]
  have heq := curve_equation.mp h.left
  simp only [addX, curve, zero_mul, add_zero, sub_zero]
  field_simp [hx]
  linear_combination heq

lemma add_kernel_y {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    addY (curve a b) x 0 y (slope (curve a b) x 0 y 0) =
      -(b * y / x ^ 2) := by
  rw [slope_kernel hx]
  have hX : addX (curve a b) x 0 (y / x) = b / x := by
    rw [← slope_kernel hx]
    exact add_kernel_x h hx
  simp only [addY, WeierstrassCurve.Affine.negAddY, curve_negY]
  rw [hX]
  field_simp [hx]
  ring

lemma translation_coordinates {b x y : ℚ}
    (hx : x ≠ 0) (hb : b ≠ 0) :
    fx (b / x) (-(b * y / x ^ 2)) = fx x y ∧
      fy b (b / x) (-(b * y / x ^ 2)) = fy b x y := by
  constructor
  · unfold fx
    field_simp [hx, hb]
  · unfold fy
    field_simp [hx, hb]
    ring

lemma pointMap_add_kernel {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + kernelPoint a b) = pointMap P := by
  cases P with
  | zero =>
      change pointMap (kernelPoint a b) = pointMap 0
      rw [pointMap_kernel, pointMap_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hP : (Point.some x y h : Point (curve a b)) = kernelPoint a b := by
          unfold kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx, hy⟩
        rw [hP, kernel_add_self, pointMap_zero, pointMap_kernel]
      · rw [show kernelPoint a b =
            Point.some 0 0 (equation_iff_nonsingular.mp
              (curve_equation.mpr (by ring))) by rfl]
        rw [Point.add_of_X_ne hx]
        have hb := b_ne_zero a b
        have hax : addX (curve a b) x 0 (slope (curve a b) x 0 y 0) ≠ 0 := by
          rw [add_kernel_x h hx]
          exact div_ne_zero hb hx
        rw [pointMap_some _ hax, pointMap_some h hx, Point.some.injEq]
        rw [add_kernel_x h hx, add_kernel_y h hx]
        exact translation_coordinates hx hb

lemma pointMap_kernel_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (kernelPoint a b + P) = pointMap P := by
  rw [add_comm, pointMap_add_kernel]

lemma pointMap_eq_zero_iff {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap P = 0 ↔ P = 0 ∨ P = kernelPoint a b := by
  constructor
  · intro hmap
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
        by_cases hx : x = 0
        · right
          unfold kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx, y_zero_of_x_zero h hx⟩
        · rw [pointMap_some h hx] at hmap
          exact (Point.some_ne_zero _ hmap).elim
  · rintro (rfl | rfl)
    · exact pointMap_zero
    · exact pointMap_kernel

lemma fx_secant_form {a b x y : ℚ}
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) (hx : x ≠ 0) :
    fx x y = x + a + b / x := by
  unfold fx
  rw [h]
  field_simp [hx]

lemma x_fibre_factor {a b x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hfx : fx x₁ y₁ = fx x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = b := by
  rw [fx_secant_form h₁ hx₁, fx_secant_form h₂ hx₂] at hfx
  have hprod : (x₁ - x₂) * (x₁ * x₂ - b) = 0 := by
    field_simp [hx₁, hx₂] at hfx
    linear_combination hfx
  rcases mul_eq_zero.mp hprod with h | h
  · left
    linarith
  · right
    linarith

lemma affine_fibre {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
      pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂)) :
    (Point.some x₂ y₂ h₂ : Point (curve a b)) = Point.some x₁ y₁ h₁ ∨
      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
        Point.some x₁ y₁ h₁ + kernelPoint a b := by
  rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂] at hmap
  have hcoords := Point.some.inj hmap
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hxf := x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (Point.some x₂ y₂ h₂ : Point (curve a b)) = Point.some x₁ y₁ h₁ ∨
        (Point.some x₂ y₂ h₂ : Point (curve a b)) =
          Point.some x₁ y₁ h₁ + kernelPoint a b := by
    rcases Y_eq_of_X_eq h₁.left h₂.left hxeq with hyeq | hyneg
    · left
      rw [Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hy₂ : y₂ = -y₁ := by
        rw [curve_negY] at hyneg
        linarith
      by_cases hy₁ : y₁ = 0
      · left
        rw [Point.some.injEq]
        exact ⟨hxeq.symm, by linarith⟩
      · have hY := hcoords.2
        rw [← hxeq] at hY
        unfold fy at hY
        field_simp [hx₁] at hY
        rw [hy₂] at hY
        have hprod : y₁ * (b - x₁ ^ 2) = 0 := by
          linear_combination (1 / 2 : ℚ) * hY
        have hsquare : x₁ ^ 2 = b := by
          have := (mul_eq_zero.mp hprod).resolve_left hy₁
          linarith
        right
        change Point.some x₂ y₂ h₂ =
          (Point.some x₁ y₁ h₁ : Point (curve a b)) +
            Point.some 0 0 _
        rw [Point.add_of_X_ne hx₁, Point.some.injEq]
        constructor
        · rw [add_kernel_x h₁ hx₁, ← hxeq]
          field_simp [hx₁]
          nlinarith
        · rw [add_kernel_y h₁ hx₁, hy₂]
          field_simp [hx₁]
          nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = b / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ b := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      rw [hx₂val] at hY
      have hb := b_ne_zero a b
      unfold fy at hY
      field_simp [hx₁, hb] at hY
      have hfac : (x₁ ^ 2 - b) * (x₁ ^ 2 * y₂ + b * y₁) = 0 := by
        calc
          (x₁ ^ 2 - b) * (x₁ ^ 2 * y₂ + b * y₁) =
              -(y₁ * b * (b - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - b)) := by ring
          _ = 0 := by rw [hY]; ring
      have hyrel : x₁ ^ 2 * y₂ + b * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change Point.some x₂ y₂ h₂ =
        (Point.some x₁ y₁ h₁ : Point (curve a b)) +
          Point.some 0 0 _
      rw [Point.add_of_X_ne hx₁, Point.some.injEq]
      constructor
      · rw [add_kernel_x h₁ hx₁, hx₂val]
      · rw [add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

lemma pointMap_eq_iff {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b)) :
    pointMap P = pointMap Q ↔ Q = P ∨ Q = P + kernelPoint a b := by
  constructor
  · intro hPQ
    by_cases hPzero : pointMap P = 0
    · have hQzero : pointMap Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (pointMap_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (pointMap_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left
        rw [hP, hQ]
      · right
        rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, kernel_add_self]
      · left
        rw [hP, hQ]
    · have hQzero : pointMap Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero pointMap_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero pointMap_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                show pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) = Point.zero
                unfold pointMap
                exact dif_pos hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                show pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) = Point.zero
                unfold pointMap
                exact dif_pos hx
              exact affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (pointMap_add_kernel P).symm

/-! ### The generic secant calculation

The two `secant_*_identity` lemmas package the only coordinate calculation.
They are low-degree consequences of the two curve equations and the equation of
the secant line; all exceptional configurations have already been classified as
kernel cosets.
-/

lemma secant_relations
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂) :
    x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁) = 0 ∧
      x₁ * x₂ * r - (y₁ - ℓ * x₁) ^ 2 = 0 := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  have h₂' := h₂
  rw [hline] at h₂'
  have hBmul :
      (x₁ - x₂) *
        (x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁)) = 0 := by
    rw [hrdef]
    linear_combination h₁ - h₂'
  have hB :
      x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁) = 0 :=
    (mul_eq_zero.mp hBmul).resolve_left (sub_ne_zero.mpr hx₁x₂)
  refine ⟨hB, ?_⟩
  linear_combination x₁ * hB - h₁ - x₁ ^ 2 * hrdef

lemma secant_x_identity
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂)
    (hr : r ≠ 0) (hb : x₁ * x₂ - b ≠ 0) :
    r + a + b / r =
      ((y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂))) ^ 2 +
        2 * a - (x₁ + a + b / x₁) - (x₂ + a + b / x₂) := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  obtain ⟨hB, hC⟩ := secant_relations h₁ h₂ hx₁x₂ hℓ hrdef
  have hCeq : r * x₁ * x₂ = (ℓ * x₁ - y₁) ^ 2 := by
    linear_combination hC
  have hu : ℓ * x₁ - y₁ ≠ 0 := by
    intro hu0
    have hprod : r * x₁ * x₂ ≠ 0 := mul_ne_zero (mul_ne_zero hr hx₁) hx₂
    apply hprod
    rw [hCeq, hu0]
    norm_num
  have hu' : -y₁ + x₁ * ℓ ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hu'' : x₁ * ℓ - y₁ ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hT :
      x₁ * x₂ + r * (x₁ + x₂) = b + 2 * ℓ * (ℓ * x₁ - y₁) := by
    linear_combination hB
  have hA : r + x₁ + x₂ + a = ℓ ^ 2 := by
    linear_combination hrdef
  have hFD_eq :
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
        (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
    field_simp [hx₁, hx₂]
    ring
  have hm₀ :
      (y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂)) =
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
        (x₁ * x₂ * (x₁ * x₂ - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx₁, hx₂, sub_ne_zero.mpr hx₁x₂, hb]
    ring
  have hcross :
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) *
          (ℓ * x₁ - y₁) +
        (ℓ * (ℓ * x₁ - y₁) + b) * (x₁ * x₂ * (x₁ * x₂ - b)) = 0 := by
    linear_combination (b * x₁ * x₂) * hB - (b * (x₁ + x₂)) * hC
  have hden : x₁ * x₂ * (x₁ * x₂ - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx₁ hx₂) hb
  have hm₁ :
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
          (x₁ * x₂ * (x₁ * x₂ - b)) =
        -(ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁) := by
    apply (div_eq_iff hden).2
    field_simp [hu, hu', hu'']
    linear_combination hcross
  have hsum :
      (r + a + b / r) + (x₁ + a + b / x₁) +
          (x₂ + a + b / x₂) - 2 * a =
        ((ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁)) ^ 2 := by
    calc
      (r + a + b / r) + (x₁ + a + b / x₁) +
            (x₂ + a + b / x₂) - 2 * a =
          r + x₁ + x₂ + a +
            b * (x₁ * x₂ + r * (x₁ + x₂)) / (r * x₁ * x₂) := by
        field_simp [hr, hx₁, hx₂]
        ring
      _ = ℓ ^ 2 +
            b * (x₁ * x₂ + r * (x₁ + x₂)) / (r * x₁ * x₂) := by rw [hA]
      _ = ℓ ^ 2 +
            b * (b + 2 * ℓ * (ℓ * x₁ - y₁)) /
              ((ℓ * x₁ - y₁) ^ 2) := by rw [hT, hCeq]
      _ = ((ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁)) ^ 2 := by
        field_simp [hu]
        ring
  rw [hm₀, hm₁]
  linear_combination hsum

lemma secant_y_identity
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂)
    (hr : r ≠ 0) (hb : x₁ * x₂ - b ≠ 0) :
    (ℓ * (x₁ - r) - y₁) * (b - r ^ 2) / r ^ 2 =
      ((y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂))) *
          ((x₁ + a + b / x₁) - (r + a + b / r)) -
        y₁ * (b - x₁ ^ 2) / x₁ ^ 2 := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  obtain ⟨hB, hC⟩ := secant_relations h₁ h₂ hx₁x₂ hℓ hrdef
  have hH :
      ℓ * r * x₁ ^ 2 - ℓ * r * x₁ * x₂ + ℓ * x₁ ^ 2 * x₂ -
          b * ℓ * x₁ - r * x₁ * y₁ - r * x₂ * y₁ - x₁ * x₂ * y₁ +
          b * y₁ = 0 := by
    linear_combination (ℓ * x₁ - y₁) * hB - 2 * ℓ * hC
  have hFD_eq :
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
        (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
    field_simp [hx₁, hx₂]
    ring
  have hm :
      (y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂)) =
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
        (x₁ * x₂ * (x₁ * x₂ - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx₁, hx₂, sub_ne_zero.mpr hx₁x₂, hb]
    ring
  rw [hm]
  apply sub_eq_zero.mp
  calc
    (ℓ * (x₁ - r) - y₁) * (b - r ^ 2) / r ^ 2 -
          ((-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
              (x₁ * x₂ * (x₁ * x₂ - b)) *
            ((x₁ + a + b / x₁) - (r + a + b / r)) -
          y₁ * (b - x₁ ^ 2) / x₁ ^ 2) =
        b * (x₁ - r) * (x₂ - r) *
            (ℓ * r * x₁ ^ 2 - ℓ * r * x₁ * x₂ + ℓ * x₁ ^ 2 * x₂ -
              b * ℓ * x₁ - r * x₁ * y₁ - r * x₂ * y₁ - x₁ * x₂ * y₁ +
              b * y₁) /
          (r ^ 2 * x₁ * x₂ * (x₁ * x₂ - b)) := by
      field_simp [hx₁, hx₂, hr, hb]
      ring
    _ = 0 := by rw [hH]; ring

/-! ### Additivity on the standard model -/

lemma pointMap_add_x_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    fx
        (addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂))
        (addY (curve a b) x₁ x₂ y₁ (slope (curve a b) x₁ x₂ y₁ y₂)) =
      addX (curve (-2 * a) (a ^ 2 - 4 * b))
        (fx x₁ y₁) (fx x₂ y₂)
        (slope (curve (-2 * a) (a ^ 2 - 4 * b))
          (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁) (fy b x₂ y₂)) := by
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  have hsumEq := curve_equation.mp hsum.left
  have hr' :
      ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂ ≠ 0 := by
    simpa [slope_of_X_ne hx₁x₂, addX, curve] using hr
  have hF' : x₁ + a + b / x₁ ≠ x₂ + a + b / x₂ := by
    simpa [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂] using hF
  have hb : x₁ * x₂ - b ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
          (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
        field_simp [hx₁, hx₂]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := secant_x_identity heq₁ heq₂ hx₁ hx₂ hx₁x₂
    (ℓ := (y₁ - y₂) / (x₁ - x₂))
    (r := ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂)
    rfl rfl hr' hb
  rw [fx_secant_form hsumEq hr]
  rw [slope_of_X_ne hx₁x₂, slope_of_X_ne hF]
  rw [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂]
  simp only [addX, curve, zero_mul, add_zero, fy]
  convert hid using 1 <;> ring

lemma pointMap_add_y_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    fy b
        (addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂))
        (addY (curve a b) x₁ x₂ y₁ (slope (curve a b) x₁ x₂ y₁ y₂)) =
      addY (curve (-2 * a) (a ^ 2 - 4 * b))
        (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁)
        (slope (curve (-2 * a) (a ^ 2 - 4 * b))
          (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁) (fy b x₂ y₂)) := by
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  have hsumEq := curve_equation.mp hsum.left
  have hr' :
      ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂ ≠ 0 := by
    simpa [slope_of_X_ne hx₁x₂, addX, curve] using hr
  have hF' : x₁ + a + b / x₁ ≠ x₂ + a + b / x₂ := by
    simpa [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂] using hF
  have hb : x₁ * x₂ - b ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
          (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
        field_simp [hx₁, hx₂]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := secant_y_identity heq₁ heq₂ hx₁ hx₂ hx₁x₂
    (ℓ := (y₁ - y₂) / (x₁ - x₂))
    (r := ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂)
    rfl rfl hr' hb
  have hX := pointMap_add_x_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF
  unfold addY WeierstrassCurve.Affine.negAddY
  rw [curve_negY, curve_negY]
  rw [← hX]
  rw [fx_secant_form hsumEq hr]
  rw [slope_of_X_ne hx₁x₂, slope_of_X_ne hF]
  rw [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂]
  simp only [fy, addX, curve, zero_mul, add_zero]
  convert hid using 1 <;> ring

lemma pointMap_add_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    pointMap
        ((Point.some x₁ y₁ h₁ : Point (curve a b)) + Point.some x₂ y₂ h₂) =
      pointMap (Point.some x₁ y₁ h₁) + pointMap (Point.some x₂ y₂ h₂) := by
  rw [Point.add_of_X_ne hx₁x₂]
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  rw [pointMap_some hsum hr, pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
  rw [Point.add_of_X_ne hF, Point.some.injEq]
  exact ⟨pointMap_add_x_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF,
    pointMap_add_y_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF⟩

lemma pointMap_add_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + 0) = pointMap P + pointMap 0 := by
  rw [add_zero, pointMap_zero, add_zero]

lemma pointMap_zero_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (0 + P) = pointMap 0 + pointMap P := by
  rw [zero_add, pointMap_zero, zero_add]

lemma pointMap_add_neg {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + -P) = pointMap P + pointMap (-P) := by
  rw [add_neg_cancel, pointMap_zero, pointMap_neg, add_neg_cancel]

lemma pointMap_add_kernelTranslate {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + (P + kernelPoint a b)) =
      pointMap P + pointMap (P + kernelPoint a b) := by
  rw [← add_assoc, pointMap_add_kernel, pointMap_add_kernel, pointMap_add_self]

lemma pointMap_add_neg_kernelTranslate {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + (-P + kernelPoint a b)) =
      pointMap P + pointMap (-P + kernelPoint a b) := by
  rw [← add_assoc, add_neg_cancel, zero_add, pointMap_kernel,
    pointMap_add_kernel, pointMap_neg, add_neg_cancel]

lemma pointMap_add_of_basic_or_kernel_relation {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b))
    (hQ : Q = 0 ∨ Q = kernelPoint a b ∨ Q = P ∨ Q = -P ∨
      Q = P + kernelPoint a b ∨ Q = -P + kernelPoint a b) :
    pointMap (P + Q) = pointMap P + pointMap Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact pointMap_add_zero P
  · rw [hQ, pointMap_add_kernel, pointMap_kernel, add_zero]
  · rw [hQ]
    exact pointMap_add_self P
  · rw [hQ]
    exact pointMap_add_neg P
  · rw [hQ]
    exact pointMap_add_kernelTranslate P
  · rw [hQ]
    exact pointMap_add_neg_kernelTranslate P

lemma kernel_neg {a b : ℚ} [hE : (curve a b).IsElliptic] :
    -(kernelPoint a b) = kernelPoint a b := by
  rw [neg_eq_iff_add_eq_zero]
  exact kernel_add_self

lemma pointMap_add_of_fx_eq {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hF : fx x₁ y₁ = fx x₂ y₂) :
    pointMap
        ((Point.some x₁ y₁ h₁ : Point (curve a b)) + Point.some x₂ y₂ h₂) =
      pointMap (Point.some x₁ y₁ h₁) + pointMap (Point.some x₂ y₂ h₂) := by
  have hf₁ : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x₁ y₁) (fy b x₁ y₁) :=
    equation_iff_nonsingular.mp (forward_equation h₁.left hx₁)
  have hf₂ : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x₂ y₂) (fy b x₂ y₂) :=
    equation_iff_nonsingular.mp (forward_equation h₂.left hx₂)
  rcases (Point.X_eq_iff (h₁ := hf₁) (h₂ := hf₂)).mp hF with hsame | hneg
  · have hmap :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) := by
      rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
      exact hsame
    rcases (pointMap_eq_iff
      (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂)).mp hmap with hQ | hQ
    · exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inl hQ)))
    · exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  · have hmapneg :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          -pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) := by
      rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
      exact hneg
    have hmap :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          pointMap (a := a) (b := b) (-(Point.some x₂ y₂ h₂)) := by
      rw [pointMap_neg]
      exact hmapneg
    rcases (pointMap_eq_iff
      (Point.some x₁ y₁ h₁) (-(Point.some x₂ y₂ h₂))).mp hmap with hQ | hQ
    · have hQ' :
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
            -(Point.some x₁ y₁ h₁) := by
        calc
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
              -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
          _ = -(Point.some x₁ y₁ h₁) := congrArg Neg.neg hQ
      exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inl hQ'))))
    · have hQ' :
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
            -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
        calc
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
              -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
          _ = -((Point.some x₁ y₁ h₁ : Point (curve a b)) +
                kernelPoint a b) := by rw [hQ]
          _ = -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
            rw [neg_add_rev, kernel_neg, add_comm]
      exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ')))))

theorem pointMap_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b)) :
    pointMap (P + Q) = pointMap P + pointMap Q := by
  cases P with
  | zero => exact pointMap_zero_add Q
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero => exact pointMap_add_zero _
      | some x₂ y₂ h₂ =>
          by_cases hx₁ : x₁ = 0
          · have hy₁ := y_zero_of_x_zero h₁ hx₁
            have hP :
                (Point.some x₁ y₁ h₁ : Point (curve a b)) = kernelPoint a b := by
              unfold kernelPoint
              rw [Point.some.injEq]
              exact ⟨hx₁, hy₁⟩
            rw [hP, pointMap_kernel_add, pointMap_kernel, zero_add]
          · by_cases hx₂ : x₂ = 0
            · have hy₂ := y_zero_of_x_zero h₂ hx₂
              have hQ :
                  (Point.some x₂ y₂ h₂ : Point (curve a b)) = kernelPoint a b := by
                unfold kernelPoint
                rw [Point.some.injEq]
                exact ⟨hx₂, hy₂⟩
              rw [hQ, pointMap_add_kernel, pointMap_kernel, add_zero]
            · by_cases hx₁x₂ : x₁ = x₂
              · rcases (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx₁x₂ with hsame | hneg
                · rw [← hsame]
                  exact pointMap_add_self _
                · have hQ :
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                        -(Point.some x₁ y₁ h₁) := by
                    calc
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                          -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
                      _ = -(Point.some x₁ y₁ h₁) := (congrArg Neg.neg hneg).symm
                  rw [hQ]
                  exact pointMap_add_neg _
              · by_cases hr :
                    addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) = 0
                · have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
                  have hsumY := y_zero_of_x_zero hsum hr
                  have hsumK :
                      (Point.some x₁ y₁ h₁ : Point (curve a b)) +
                          Point.some x₂ y₂ h₂ = kernelPoint a b := by
                    change
                      (Point.some x₁ y₁ h₁ : Point (curve a b)) +
                          Point.some x₂ y₂ h₂ = Point.some 0 0 _
                    rw [Point.add_of_X_ne hx₁x₂, Point.some.injEq]
                    exact ⟨hr, hsumY⟩
                  have hQ :
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                        -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
                    calc
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                          -(Point.some x₁ y₁ h₁) +
                            ((Point.some x₁ y₁ h₁ : Point (curve a b)) +
                              Point.some x₂ y₂ h₂) := by
                        symm
                        rw [← add_assoc, neg_add_cancel, zero_add]
                      _ = -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
                        rw [hsumK]
                  exact pointMap_add_of_basic_or_kernel_relation _ _
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))
                · by_cases hF : fx x₁ y₁ = fx x₂ y₂
                  · exact pointMap_add_of_fx_eq h₁ h₂ hx₁ hx₂ hF
                  · exact pointMap_add_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF

/-! ### Conjugating the Vélu formula to the standard model -/

open MazurProof.N18RouteC.VariableChangePoints

def sourceChange (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := r
  s := 0
  t := 0

def targetChange (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := -1
  r := -2 * r
  s := 0
  t := 0

lemma sourceChange_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    sourceChange r • shortWS A B = curve (3 * r) (veluT A r) := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [sourceChange, shortWS, curve, veluT] <;> nlinarith

lemma targetChange_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    targetChange r • veluQuotCurve A B r =
      curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r) := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [targetChange, veluQuotCurve, curve, veluT] <;> nlinarith

noncomputable def curveCastAddEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂) :
    Point W₁ ≃+ Point W₂ :=
  AddEquiv.mk
    { toFun := fun P => h ▸ P
      invFun := fun P => h.symm ▸ P
      left_inv := by subst h; intro P; rfl
      right_inv := by subst h; intro P; rfl }
    (by subst h; intro P Q; rfl)

@[reducible] def sourceStdIsElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    (curve (3 * r) (veluT A r)).IsElliptic :=
  sourceChange_eq htors ▸
    (inferInstance : (sourceChange r • shortWS A B).IsElliptic)

@[reducible] def targetStdIsElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
  targetChange_eq htors ▸
    (inferInstance : (targetChange r • veluQuotCurve A B r).IsElliptic)

noncomputable def sourceEquiv {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Point (shortWS A B) ≃+ Point (curve (3 * r) (veluT A r)) :=
  haveI hstd : (curve (3 * r) (veluT A r)).IsElliptic :=
    sourceStdIsElliptic htors
  (variableChangePointAddEquiv (shortWS A B) (sourceChange r)).trans
    (curveCastAddEquiv (sourceChange_eq htors))

noncomputable def targetEquiv {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) ≃+
      Point (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)) :=
  haveI hstd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
    targetStdIsElliptic htors
  (variableChangePointAddEquiv (veluQuotCurve A B r) (targetChange r)).trans
    (curveCastAddEquiv (targetChange_eq htors))

lemma standard_x_eq {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y ^ 2 = x ^ 3 + A * x + B)
    (hxr : x ≠ r) :
    fx (x - r) y = x + veluT A r / (x - r) + 2 * r := by
  have hB : B = -(r ^ 3 + A * r) := by
    linarith [htors]
  have hfactor :
      y ^ 2 = (x - r) * (x ^ 2 + x * r + r ^ 2 + A) := by
    rw [hcurve, hB]
    ring
  unfold fx veluT
  field_simp [sub_ne_zero.mpr hxr]
  rw [hfactor]
  ring

@[simp] lemma sourceChange_x (r x : ℚ) :
    variableChangePointX (sourceChange r) x = x - r := by
  simp [variableChangePointX, sourceChange]

@[simp] lemma sourceChange_y (r x y : ℚ) :
    variableChangePointY (sourceChange r) x y = y := by
  simp [variableChangePointY, sourceChange]

@[simp] lemma targetChange_x (r x : ℚ) :
    variableChangePointX (targetChange r) x = x + 2 * r := by
  simp [variableChangePointX, targetChange]

@[simp] lemma targetChange_y (r x y : ℚ) :
    variableChangePointY (targetChange r) x y = -y := by
  simp [variableChangePointY, targetChange]
  ring

lemma variableChangeEquiv_some
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ} (hns : Nonsingular W x y) :
    (variableChangePointAddEquiv W C) (Point.some x y hns) =
      Point.some (variableChangePointX C x) (variableChangePointY C x y)
        (equation_iff_nonsingular.mp
          (variableChangePoint_equation W C hns.left)) := by
  show variableChangePointMap W C (Point.some x y hns) = _
  unfold variableChangePointMap
  rfl

lemma curveCastAddEquiv_some {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂)
    {x y : ℚ} (hns : Nonsingular W₁ x y) :
    curveCastAddEquiv h (Point.some x y hns) =
      Point.some x y (h ▸ hns) := by
  subst h
  rfl

@[simp] lemma sourceEquiv_zero {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    sourceEquiv htors 0 = 0 :=
  map_zero _

@[simp] lemma targetEquiv_zero {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    targetEquiv htors 0 = 0 :=
  map_zero _

lemma sourceEquiv_some {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hstd : (curve (3 * r) (veluT A r)).IsElliptic]
    (hns : Nonsingular (shortWS A B) x y) :
    sourceEquiv htors (Point.some x y hns) =
      Point.some (variableChangePointX (sourceChange r) x)
        (variableChangePointY (sourceChange r) x y)
        ((sourceChange_eq htors) ▸
          equation_iff_nonsingular.mp
            (variableChangePoint_equation (shortWS A B) (sourceChange r) hns.left)) := by
  unfold sourceEquiv
  rw [AddEquiv.trans_apply, variableChangeEquiv_some, curveCastAddEquiv_some]

lemma targetEquiv_some {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic]
    [hstd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic]
    (hns : Nonsingular (veluQuotCurve A B r) x y) :
    targetEquiv htors (Point.some x y hns) =
      Point.some (variableChangePointX (targetChange r) x)
        (variableChangePointY (targetChange r) x y)
        ((targetChange_eq htors) ▸
          equation_iff_nonsingular.mp
            (variableChangePoint_equation (veluQuotCurve A B r) (targetChange r) hns.left)) := by
  unfold targetEquiv
  rw [AddEquiv.trans_apply, variableChangeEquiv_some, curveCastAddEquiv_some]

lemma map_conjugacy {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    [hsourceStd : (curve (3 * r) (veluT A r)).IsElliptic]
    [htargetStd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic]
    (P : Point (shortWS A B)) :
    targetEquiv htors (veluMapPoint htors P) =
      pointMap (sourceEquiv htors P) := by
  cases P with
  | zero =>
      change targetEquiv htors 0 = pointMap (sourceEquiv htors 0)
      rw [targetEquiv_zero, sourceEquiv_zero, pointMap_zero]
  | some x y h =>
      by_cases hxr : x = r
      · have hmap : veluMapPoint htors (Point.some x y h) = 0 := by
          show veluMapPoint htors (Point.some x y h) = Point.zero
          unfold veluMapPoint
          exact dif_pos hxr
        rw [hmap, targetEquiv_zero, sourceEquiv_some]
        have hx0 : variableChangePointX (sourceChange r) x = 0 := by
          simp [hxr]
        simp only [pointMap, hx0, dite_true]
        rfl
      · have hvns := equation_iff_nonsingular.mp (velu_equation h.left htors hxr)
        have hmap :
            veluMapPoint htors (Point.some x y h) =
              Point.some (x + veluT A r / (x - r))
                (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns := by
          unfold veluMapPoint
          exact dif_neg hxr
        rw [hmap, targetEquiv_some, sourceEquiv_some]
        rw [pointMap_some]
        · rw [Point.some.injEq]
          constructor
          · simp only [targetChange_x, sourceChange_x, sourceChange_y]
            exact (standard_x_eq htors (shortWS_equation.mp h.left) hxr).symm
          · simp only [targetChange_x, targetChange_y, sourceChange_x,
              sourceChange_y, fy]
            ring
        · simpa only [sourceChange_x] using sub_ne_zero.mpr hxr

theorem conjugated_veluMapPoint_add {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) = veluMapPoint htors P + veluMapPoint htors Q := by
  letI hsourceStd : (curve (3 * r) (veluT A r)).IsElliptic :=
    sourceStdIsElliptic htors
  letI htargetStd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
    targetStdIsElliptic htors
  apply (targetEquiv htors).injective
  calc
    targetEquiv htors (veluMapPoint htors (P + Q)) =
        pointMap (sourceEquiv htors (P + Q)) :=
      map_conjugacy htors (P + Q)
    _ = pointMap (sourceEquiv htors P + sourceEquiv htors Q) := by
      rw [map_add]
    _ = pointMap (sourceEquiv htors P) + pointMap (sourceEquiv htors Q) :=
      pointMap_add _ _
    _ = targetEquiv htors (veluMapPoint htors P) +
        targetEquiv htors (veluMapPoint htors Q) := by
      rw [map_conjugacy, map_conjugacy]
    _ = targetEquiv htors (veluMapPoint htors P + veluMapPoint htors Q) := by
      rw [map_add]


end StandardTwoIsogeny

lemma veluMapPoint_add {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) =
      veluMapPoint htors P + veluMapPoint htors Q :=
  StandardTwoIsogeny.conjugated_veluMapPoint_add htors P Q

def veluMapHom {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) →+ Point (veluQuotCurve A B r) where
  toFun := veluMapPoint htors
  map_zero' := veluMapPoint_zero
  map_add' := veluMapPoint_add

/-! ## η = (-2r, 0) on E' -/

lemma eta_on_curve {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    Equation (veluQuotCurve A B r) (-2 * r) 0 := by
  rw [veluQuotCurve_equation]
  unfold veluT
  nlinarith

lemma eta_nonsingular {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Nonsingular (veluQuotCurve A B r) (-2 * r) 0 :=
  equation_iff_nonsingular.mp (eta_on_curve htors)

def etaPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) :=
  .some (-2 * r) 0 (eta_nonsingular htors)

lemma etaPoint_add_self {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    etaPoint htors + etaPoint htors = 0 := by
  exact Point.add_self_of_Y_eq (by simp [negY, veluQuotCurve])

lemma etaPoint_ne_zero {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    etaPoint htors ≠ 0 :=
  Point.some_ne_zero _

lemma etaPoint_order {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    addOrderOf (etaPoint htors) = 2 := by
  exact addOrderOf_eq_prime (by rw [two_nsmul]; exact etaPoint_add_self htors)
    (etaPoint_ne_zero htors)

/-! ## Dual isogeny helpers -/

private def eqCastHom {W₁ W₂ : WeierstrassCurve ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (h : W₁ = W₂) : Point W₁ →+ Point W₂ where
  toFun P := h ▸ P
  map_zero' := by subst h; rfl
  map_add' a b := by subst h; rfl

private lemma ns_eq {W : WeierstrassCurve.Affine ℚ} {x y : ℚ}
    (hns : Nonsingular W x y) : Equation W x y := hns.left

private lemma eqCastHom_some {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic]
    (h : W₁ = W₂) {x y : ℚ} (hns : Nonsingular W₁ x y) :
    eqCastHom h (Point.some x y hns) = Point.some x y (h ▸ hns) := by
  show h ▸ Point.some x y hns = _; subst h; rfl

private lemma varChangeEquiv_some
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ} (hns : Nonsingular W x y) :
    (N18RouteC.VariableChangePoints.variableChangePointAddEquiv W C)
      (Point.some x y hns) =
    Point.some (N18RouteC.VariableChangePoints.variableChangePointX C x)
      (N18RouteC.VariableChangePoints.variableChangePointY C x y)
      (equation_iff_nonsingular.mp
        (N18RouteC.VariableChangePoints.variableChangePoint_equation W C (ns_eq hns))) := by
  show N18RouteC.VariableChangePoints.variableChangePointMap W C (Point.some x y hns) = _
  unfold N18RouteC.VariableChangePoints.variableChangePointMap; rfl

private def scaleChangeInv : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (2 : ℚ)⁻¹ (by norm_num)
  r := 0; s := 0; t := 0

private lemma scaleInv_eq {A B : ℚ} :
    scaleChangeInv • shortWS A B = shortWS (16 * A) (64 * B) := by
  rw [WeierstrassCurve.variableChange_def]
  simp only [scaleChangeInv, shortWS]
  ext <;> simp <;> norm_num <;> ring

private def scaleChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (2 : ℚ) (by norm_num)
  r := 0; s := 0; t := 0

private lemma scale_eq {A B : ℚ} :
    scaleChange • shortWS (16 * A) (64 * B) = shortWS A B := by
  rw [WeierstrassCurve.variableChange_def]
  simp only [scaleChange, shortWS]
  ext <;> simp <;> norm_num <;> ring

private lemma scaleChange_pointX (z : ℚ) :
    N18RouteC.VariableChangePoints.variableChangePointX scaleChange z = z / 4 := by
  simp [N18RouteC.VariableChangePoints.variableChangePointX, scaleChange,
    Units.val_inv_eq_inv_val]; ring

private lemma scaleChange_pointY (z w : ℚ) :
    N18RouteC.VariableChangePoints.variableChangePointY scaleChange z w = w / 8 := by
  simp [N18RouteC.VariableChangePoints.variableChangePointY, scaleChange,
    Units.val_inv_eq_inv_val]; ring

private lemma dual_torsion {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (-2 * r) ^ 3 + (A - 5 * veluT A r) * (-2 * r) +
    (B - 7 * r * veluT A r) = 0 := by
  unfold veluT; nlinarith

private lemma dual_quotient_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    veluQuotCurve (A - 5 * veluT A r) (B - 7 * r * veluT A r) (-2 * r) =
    shortWS (16 * A) (64 * B) := by
  simp only [veluQuotCurve, shortWS, veluT]
  ext <;> simp <;> nlinarith

/-! ## Dual isogeny

The dual φ̂ : E' → E is the Vélu map from E' with kernel ⟨η⟩ = ⟨(-2r,0)⟩,
composed with the scaling isomorphism shortWS(16A,64B) ≃ shortWS(A,B). -/

open N18RouteC.VariableChangePoints in
noncomputable def dualMapHom {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) →+ Point (shortWS A B) :=
  haveI h16 : (shortWS (16 * A) (64 * B)).IsElliptic :=
    scaleInv_eq (A := A) (B := B) ▸ (inferInstance : (scaleChangeInv • shortWS A B).IsElliptic)
  haveI : (veluQuotCurve (A - 5 * veluT A r) (B - 7 * r * veluT A r) (-2 * r)).IsElliptic :=
    (dual_quotient_eq htors) ▸ h16
  haveI : (scaleChange • shortWS (16 * A) (64 * B)).IsElliptic := inferInstance
  haveI : (shortWS (A - 5 * veluT A r) (B - 7 * r * veluT A r)).IsElliptic := hE'
  (eqCastHom scale_eq).comp
    ((variableChangePointAddHom (shortWS (16 * A) (64 * B)) scaleChange).comp
      ((eqCastHom (dual_quotient_eq htors)).comp
        (veluMapHom (dual_torsion htors))))

/-! ## Properties -/

lemma dual_eta_eq_zero {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    dualMapHom htors (etaPoint htors) = 0 := by
  haveI h16 : (shortWS (16 * A) (64 * B)).IsElliptic :=
    scaleInv_eq (A := A) (B := B) ▸ (inferInstance : (scaleChangeInv • shortWS A B).IsElliptic)
  haveI : (veluQuotCurve (A - 5 * veluT A r) (B - 7 * r * veluT A r) (-2 * r)).IsElliptic :=
    (dual_quotient_eq htors) ▸ h16
  haveI : (shortWS (A - 5 * veluT A r) (B - 7 * r * veluT A r)).IsElliptic := hE'
  haveI : (scaleChange • shortWS (16 * A) (64 * B)).IsElliptic := inferInstance
  have h1 : veluMapHom (dual_torsion htors) (etaPoint htors) = 0 := by
    change veluMapPoint (dual_torsion htors) (etaPoint htors) = 0
    unfold etaPoint veluMapPoint; simp; rfl
  show eqCastHom scale_eq
    ((N18RouteC.VariableChangePoints.variableChangePointAddHom
        (shortWS (16 * A) (64 * B)) scaleChange)
      (eqCastHom (dual_quotient_eq htors)
        (veluMapHom (dual_torsion htors) (etaPoint htors)))) = 0
  rw [h1, map_zero, map_zero, map_zero]

private lemma quad_factor {A B r x : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    x ^ 3 + A * x + B = (x - r) * (x ^ 2 + x * r + r ^ 2 + A) := by
  linear_combination htors

private lemma torsion_y_zero' {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y ^ 2 = x ^ 3 + A * x + B) (hxr : x ≠ r) (hy : y = 0) :
    x ^ 2 + x * r + r ^ 2 + A = 0 := by
  rw [hy, sq, mul_zero] at hcurve
  rw [quad_factor htors] at hcurve
  exact (mul_eq_zero.mp hcurve.symm).resolve_left (sub_ne_zero.mpr hxr)

private lemma quad_ne_zero_of_y_ne {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y ^ 2 = x ^ 3 + A * x + B) (hy : y ≠ 0) :
    x ^ 2 + x * r + r ^ 2 + A ≠ 0 := by
  intro hq
  apply hy
  have : y ^ 2 = 0 := by rw [hcurve, quad_factor htors, hq, mul_zero]
  nlinarith [sq_nonneg y]

private lemma velu_x_eq_neg2r {A B r x : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hxr : x ≠ r) (hq : x ^ 2 + x * r + r ^ 2 + A = 0) :
    x + veluT A r / (x - r) = -2 * r := by
  have hne : (x - r : ℚ) ≠ 0 := sub_ne_zero.mpr hxr
  field_simp; unfold veluT; nlinarith [hq]

lemma dual_comp_phi {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P : Point (shortWS A B)) :
    dualMapHom htors (veluMapHom htors P) = 2 • P := by
  haveI h16 : (shortWS (16 * A) (64 * B)).IsElliptic :=
    scaleInv_eq (A := A) (B := B) ▸ (inferInstance : (scaleChangeInv • shortWS A B).IsElliptic)
  haveI : (veluQuotCurve (A - 5 * veluT A r) (B - 7 * r * veluT A r) (-2 * r)).IsElliptic :=
    (dual_quotient_eq htors) ▸ h16
  haveI : (shortWS (A - 5 * veluT A r) (B - 7 * r * veluT A r)).IsElliptic := hE'
  haveI : (scaleChange • shortWS (16 * A) (64 * B)).IsElliptic := inferInstance
  cases P with
  | zero =>
    change dualMapHom htors (veluMapHom htors 0) = 2 • (0 : Point (shortWS A B))
    simp only [map_zero, nsmul_zero]
  | some x y hns =>
    have hcurve : y ^ 2 = x ^ 3 + A * x + B :=
      shortWS_equation.mp hns.left
    by_cases hxr : x = r
    · -- x = r: P is the 2-torsion kernel point (r, 0)
      have hy : y = 0 := torsion_y_zero htors hns.left hxr
      subst hy
      have hphi : veluMapHom htors (Point.some x 0 hns) = 0 := by
        show veluMapPoint htors (Point.some x 0 hns) = 0
        unfold veluMapPoint; simp [hxr]; rfl
      rw [hphi, map_zero, two_nsmul]
      exact (Point.add_self_of_Y_eq (by simp [negY, shortWS])).symm
    · -- x ≠ r
      by_cases hy : y = 0
      · -- y = 0, x ≠ r: other 2-torsion point
        subst hy
        -- φ(x,0) has x-coord x₁ = x + veluT/(x-r) = -2r
        have hq : x ^ 2 + x * r + r ^ 2 + A = 0 :=
          torsion_y_zero' htors hcurve hxr rfl
        have hx1 : x + veluT A r / (x - r) = -2 * r :=
          velu_x_eq_neg2r htors hxr hq
        -- So φ(P) has x-coord = -2r = kernel of dual, hence φ̂(φ(P)) = 0
        -- And 2 • P = 0 since P is 2-torsion
        rw [two_nsmul]
        have h_pp : (Point.some x 0 hns : Point (shortWS A B)) +
            Point.some x 0 hns = 0 :=
          Point.add_self_of_Y_eq (by simp [negY, shortWS])
        rw [h_pp]
        -- Show dualMapHom htors (veluMapHom htors (.some x 0 hns)) = 0
        have hphi : veluMapHom htors (Point.some x 0 hns) =
            etaPoint htors := by
          show veluMapPoint htors (Point.some x 0 hns) = etaPoint htors
          simp only [veluMapPoint, hxr, dite_false, etaPoint]
          apply point_some_congr
          · exact hx1
          · simp [mul_comm, mul_zero, zero_mul, sub_self, zero_div]
        rw [hphi]
        exact dual_eta_eq_zero
      · -- y ≠ 0, x ≠ r: generic case — coordinate identity
        have hxr_ne : (x - r : ℚ) ≠ 0 := sub_ne_zero.mpr hxr
        have hq_ne : x ^ 2 + x * r + r ^ 2 + A ≠ 0 := quad_ne_zero_of_y_ne htors hcurve hy
        -- Pre-extract proofs before show (avoids .left under instances transparency)
        have heq : Equation (shortWS A B) x y := ns_eq hns
        have hvns1 := equation_iff_nonsingular.mp (velu_equation heq htors hxr)
        -- Step 1: x₁ ≠ -2r
        have hx1_ne : x + veluT A r / (x - r) ≠ -2 * r := by
          intro h_eq; apply hq_ne
          have : x + veluT A r / (x - r) + 2 * r = 0 := by linarith
          unfold veluT at this; field_simp at this; nlinarith
        have heq1 := ns_eq hvns1
        have hvns2 := equation_iff_nonsingular.mp (velu_equation heq1 (dual_torsion htors) hx1_ne)
        -- Step 2: Compute φ(P)
        have h_phi : veluMapHom htors (Point.some x y hns) =
            Point.some (x + veluT A r / (x - r))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns1 := by
          show veluMapPoint htors (Point.some x y hns) =
            Point.some (x + veluT A r / (x - r))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns1
          unfold veluMapPoint; simp [hxr]
        -- Step 3: Show trick to decompose dualMapHom
        show eqCastHom scale_eq
          ((N18RouteC.VariableChangePoints.variableChangePointAddHom
              (shortWS (16 * A) (64 * B)) scaleChange)
            (eqCastHom (dual_quotient_eq htors)
              (veluMapHom (dual_torsion htors)
                (veluMapHom htors (Point.some x y hns))))) = 2 • Point.some x y hns
        -- Step 4: Compute the dual Vélu on the image
        have h_dual : veluMapHom (dual_torsion htors)
            (Point.some (x + veluT A r / (x - r))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns1) =
            Point.some (x + veluT A r / (x - r) +
                veluT (A - 5 * veluT A r) (-2 * r) /
                (x + veluT A r / (x - r) - (-2 * r)))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2 *
                ((x + veluT A r / (x - r) - (-2 * r)) ^ 2 -
                  veluT (A - 5 * veluT A r) (-2 * r)) /
                (x + veluT A r / (x - r) - (-2 * r)) ^ 2) hvns2 := by
          show veluMapPoint (dual_torsion htors)
            (Point.some (x + veluT A r / (x - r))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns1) =
            Point.some (x + veluT A r / (x - r) +
                veluT (A - 5 * veluT A r) (-2 * r) /
                (x + veluT A r / (x - r) - (-2 * r)))
              (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2 *
                ((x + veluT A r / (x - r) - (-2 * r)) ^ 2 -
                  veluT (A - 5 * veluT A r) (-2 * r)) /
                (x + veluT A r / (x - r) - (-2 * r)) ^ 2) hvns2
          dsimp only [veluMapPoint]
          split_ifs with h
          · exfalso; exact hx1_ne (by linarith)
          · rfl
        rw [h_phi, h_dual]
        -- Step 5: Push through eqCastHom and variableChange
        simp only [N18RouteC.VariableChangePoints.variableChangePointAddHom_apply]
        rw [eqCastHom_some, varChangeEquiv_some]
        simp only [scaleChange_pointX, scaleChange_pointY, eqCastHom_some]
        -- Step 6: Compute 2P
        have hy_ne_neg : y ≠ negY (shortWS A B) x y := by
          simp only [negY, shortWS, mul_zero, zero_mul, sub_zero]
          intro h; exact hy (by linarith)
        rw [two_nsmul, Point.add_self_of_Y_ne hy_ne_neg]
        -- Step 7: Match coordinates
        have hslope : WeierstrassCurve.Affine.slope (shortWS A B) x x y y =
            (3 * x ^ 2 + A) / (2 * y) := by
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_neg]
          simp only [negY, shortWS, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
          ring
        have hfactor : (x - r) * (x ^ 2 + x * r + r ^ 2 + A) = y ^ 2 := by
          linear_combination -hcurve - htors
        apply point_some_congr
        · -- X-coordinate identity
          simp only [addX, negY, shortWS, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
            veluT, hslope]
          have hq_ne : x ^ 2 + x * r + r ^ 2 + A ≠ 0 := by
            intro h; rw [h, mul_zero] at hfactor
            exact absurd hfactor.symm (pow_ne_zero 2 hy)
          have h_cdenom : x + (3 * r ^ 2 + A) / (x - r) - -2 * r =
              (x ^ 2 + x * r + r ^ 2 + A) / (x - r) := by
            field_simp; ring
          rw [h_cdenom]
          have h_tp : (3 * (-2 * r) ^ 2 + (A - 5 * (3 * r ^ 2 + A))) =
              -3 * r ^ 2 - 4 * A := by ring
          rw [h_tp, div_div_eq_mul_div]
          have h1 : (-3 * r ^ 2 - 4 * A) * (x - r) / (x ^ 2 + x * r + r ^ 2 + A) =
              (-3 * r ^ 2 - 4 * A) * (x - r) ^ 2 / y ^ 2 := by
            rw [← hfactor]; field_simp
          rw [h1]
          field_simp
          linear_combination
            (4 * A + 12 * r ^ 2 - 36 * r * x + 36 * x ^ 2) * hcurve +
            (4 * A + 12 * r ^ 2 - 36 * r * x + 36 * x ^ 2) * htors
        · -- Y-coordinate identity
          simp only [addX, addY, WeierstrassCurve.Affine.negAddY, negY, shortWS,
            mul_zero, zero_mul, sub_zero, add_zero, zero_add, veluT, hslope]
          have hq_ne : x ^ 2 + x * r + r ^ 2 + A ≠ 0 := by
            intro h; rw [h, mul_zero] at hfactor
            exact absurd hfactor.symm (pow_ne_zero 2 hy)
          have h_cdenom : x + (3 * r ^ 2 + A) / (x - r) - -2 * r =
              (x ^ 2 + x * r + r ^ 2 + A) / (x - r) := by
            field_simp; ring
          have h_tp : (3 * (-2 * r) ^ 2 + (A - 5 * (3 * r ^ 2 + A))) =
              -3 * r ^ 2 - 4 * A := by ring
          rw [h_tp, h_cdenom, div_pow]
          have hq_eq : x ^ 2 + x * r + r ^ 2 + A = y ^ 2 / (x - r) := by
            rw [eq_div_iff hxr_ne]; linarith [hfactor]
          rw [hq_eq]
          field_simp
          linear_combination
            (8 * A ^ 2 * r - 8 * A ^ 2 * x - 40 * A * r ^ 3 + 96 * A * r ^ 2 * x -
              24 * A * r * x ^ 2 - 32 * A * x ^ 3 - 8 * A * y ^ 2 - 48 * r ^ 5 +
              144 * r ^ 4 * x - 72 * r ^ 3 * x ^ 2 - 240 * r ^ 2 * x ^ 3 +
              48 * r ^ 2 * y ^ 2 + 432 * r * x ^ 4 - 144 * r * x * y ^ 2 -
              216 * x ^ 5 + 72 * x ^ 2 * y ^ 2) * hcurve +
            (8 * A ^ 2 * r - 8 * A ^ 2 * x - 40 * A * r ^ 3 + 96 * A * r ^ 2 * x -
              24 * A * r * x ^ 2 - 32 * A * x ^ 3 - 8 * A * y ^ 2 - 48 * r ^ 5 +
              144 * r ^ 4 * x - 72 * r ^ 3 * x ^ 2 - 240 * r ^ 2 * x ^ 3 +
              48 * r ^ 2 * y ^ 2 + 432 * r * x ^ 4 - 144 * r * x * y ^ 2 -
              216 * x ^ 5 + 72 * x ^ 2 * y ^ 2) * htors

/-! ## General Weierstrass → Short WS reduction -/

section GeneralToShort

variable (E : WeierstrassCurve ℚ)

def toShortWSChange : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := -(E.a₁ ^ 2 + 4 * E.a₂) / 12
  s := -E.a₁ / 2
  t := -(E.a₃ + (-(E.a₁ ^ 2 + 4 * E.a₂) / 12) * E.a₁) / 2

lemma toShortWSChange_isShortWS :
    (toShortWSChange E • E).a₁ = 0 ∧
    (toShortWSChange E • E).a₂ = 0 ∧
    (toShortWSChange E • E).a₃ = 0 := by
  simp only [toShortWSChange, WeierstrassCurve.variableChange_def]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

end GeneralToShort

/-! ## Bridge theorem helpers -/

private lemma eqCastHom_symm_cancel {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂) (P : Point W₁) :
    eqCastHom h.symm (eqCastHom h P) = P := by subst h; rfl

private lemma eqCastHom_injective {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂) :
    Function.Injective (eqCastHom h) := by subst h; exact fun _ _ h => h

private lemma velu_ker_iff {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (hns_r : Nonsingular (shortWS A B) r 0)
    (P : Point (shortWS A B)) :
    veluMapHom htors P = 0 ↔ P = 0 ∨ P = Point.some r 0 hns_r := by
  constructor
  · intro h
    cases P with
    | zero => exact Or.inl rfl
    | some x y hns =>
      by_cases hxr : x = r
      · right; subst hxr
        have hcurve := shortWS_equation.mp hns.left
        have : y = 0 := sq_eq_zero_iff.mp (by linarith)
        subst this; rfl
      · exfalso
        have : veluMapHom htors (Point.some x y hns) ≠ 0 := by
          show veluMapPoint htors (Point.some x y hns) ≠ 0
          simp only [veluMapPoint, dif_neg hxr]; exact Point.some_ne_zero _
        exact this h
  · rintro (rfl | rfl)
    · exact map_zero _
    · show veluMapPoint htors (Point.some r 0 hns_r) = 0
      simp only [veluMapPoint, dite_true]; rfl

/-! ## Main theorem -/

theorem exists_rational_two_isogeny_quotient_proved
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {Q : (E⁄ℚ).Point} (hQ : addOrderOf Q = 2) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (phi : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
      (dual : (E'⁄ℚ).Point →+ (E⁄ℚ).Point)
      (eta : (E'⁄ℚ).Point),
      addOrderOf eta = 2 ∧
      (∀ R, phi R = 0 ↔ R = 0 ∨ R = Q) ∧
      (∀ R, dual (phi R) = 2 • R) ∧ dual eta = 0 := by
  -- Step 1: Short Weierstrass reduction
  set C := toShortWSChange E with hC_def
  obtain ⟨ha₁, ha₂, ha₃⟩ := toShortWSChange_isShortWS E
  set A := (C • E).a₄ with hA_def
  set B := (C • E).a₆ with hB_def
  have hEs : C • E = shortWS A B := by
    ext <;> first | exact ha₁ | exact ha₂ | exact ha₃ | rfl
  haveI : (shortWS A B).IsElliptic := hEs ▸ (inferInstance : (C • E).IsElliptic)
  -- Step 2: Variable change isomorphism
  let σ := N18RouteC.VariableChangePoints.variableChangePointAddEquiv E C
  -- Step 3: Map Q to short form, extract torsion root
  have hσord : addOrderOf (eqCastHom hEs (σ Q)) = 2 := by
    rw [addOrderOf_injective (eqCastHom hEs) (eqCastHom_injective hEs),
        N18RouteC.VariableChangePoints.variableChangePointAddEquiv_addOrderOf]
    exact hQ
  have hσne : eqCastHom hEs (σ Q) ≠ 0 := by
    intro h; simp [h] at hσord
  generalize heq : eqCastHom hEs (σ Q) = Qs at hσord hσne
  cases Qs with
  | zero => exact absurd rfl hσne
  | some r y₀ hns₀ =>
    -- 2-torsion implies y₀ = 0 on short Weierstrass
    have h_two : Point.some r y₀ hns₀ + Point.some r y₀ hns₀ = 0 := by
      rw [← two_nsmul, ← hσord]; exact addOrderOf_nsmul_eq_zero _
    have : y₀ = negY (shortWS A B) r y₀ := by
      by_contra h; rw [Point.add_self_of_Y_ne h] at h_two; exact absurd h_two (Point.some_ne_zero _)
    have hy₀ : y₀ = 0 := by
      simp only [negY, shortWS, mul_zero, zero_mul, sub_zero] at this; linarith
    subst hy₀
    -- Torsion equation for r
    have htors : r ^ 3 + A * r + B = 0 := by
      have := shortWS_equation.mp hns₀.left; nlinarith [sq_nonneg (0 : ℚ)]
    haveI : (veluQuotCurve A B r).IsElliptic :=
      veluQuotCurve_isElliptic htors ‹(shortWS A B).IsElliptic›
    -- Step 4: Construct witnesses and prove properties
    refine ⟨veluQuotCurve A B r, inferInstance,
      (veluMapHom htors).comp ((eqCastHom hEs).comp
        (N18RouteC.VariableChangePoints.variableChangePointAddHom E C)),
      (N18RouteC.VariableChangePoints.variableChangePointAddHom_symm E C).comp
        ((eqCastHom hEs.symm).comp (dualMapHom htors)),
      etaPoint htors, etaPoint_order htors, ?_, ?_, ?_⟩
    · -- Kernel characterization: phi R = 0 ↔ R = 0 ∨ R = Q
      intro R
      change veluMapHom htors (eqCastHom hEs (σ R)) = 0 ↔ R = 0 ∨ R = Q
      rw [velu_ker_iff htors hns₀]
      constructor
      · rintro (h | h)
        · left
          have h1 : σ R = 0 := by
            have := eqCastHom_symm_cancel hEs (σ R)
            rw [h, map_zero] at this; exact this.symm
          exact σ.injective (h1.trans (map_zero σ).symm)
        · right
          exact σ.injective (eqCastHom_injective hEs (h.trans heq.symm))
      · rintro (rfl | rfl)
        · left; exact map_zero ((eqCastHom hEs).comp
            (N18RouteC.VariableChangePoints.variableChangePointAddHom E C))
        · right; exact heq
    · -- Dual composition: dual (phi R) = 2 • R
      suffices ∀ R' : Point E, σ.symm (eqCastHom hEs.symm (dualMapHom htors
        (veluMapHom htors (eqCastHom hEs (σ R'))))) = 2 • R' from fun R =>
          this R
      intro R'
      have h := @dual_comp_phi A B r htors _ _ (eqCastHom hEs (σ R'))
      rw [h, map_nsmul, eqCastHom_symm_cancel, map_nsmul,
          AddEquiv.symm_apply_apply]
    · -- Dual of eta
      change σ.symm (eqCastHom hEs.symm (dualMapHom htors (etaPoint htors))) = 0
      rw [dual_eta_eq_zero, map_zero, map_zero]

end
end MazurProof.VeluTwoIsogeny
