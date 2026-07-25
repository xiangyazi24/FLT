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

/-! ## Homomorphism -/

private lemma veluMapPoint_neg {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P : Point (shortWS A B)) :
    veluMapPoint htors (-P) = -(veluMapPoint htors P) := by
  match P with
  | .zero =>
    show veluMapPoint htors (-(0 : Point (shortWS A B))) = -(veluMapPoint htors 0)
    simp
  | .some x y h =>
    simp only [Point.neg_some, veluMapPoint]
    simp only [negY, shortWS]
    by_cases hx : x = r
    · simp only [hx, dite_true]; exact (neg_zero).symm
    · simp only [hx, dite_false]
      rw [Point.neg_some]
      congr 1
      simp [negY, veluQuotCurve]
      ring

private lemma veluT_ne_zero {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0) [hE : (shortWS A B).IsElliptic] :
    veluT A r ≠ 0 := by
  intro h
  have hΔ := hE.isUnit
  rw [shortWS_Δ_factor htors] at hΔ
  have h1 : A + 3 * r ^ 2 = 0 := by unfold veluT at h; linarith
  exact absurd (show -16 * (A + 3 * r ^ 2) ^ 2 * (4 * A + 3 * r ^ 2) = 0 by rw [h1]; ring)
    (isUnit_iff_ne_zero.mp hΔ)

private lemma torsion_y_zero {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : Equation (shortWS A B) x y) (hx : x = r) : y = 0 := by
  have := shortWS_equation.mp hcurve
  rw [hx] at this; nlinarith [sq_nonneg y]

private lemma coset_x_identity {A B r x₂ y₂ : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)
    (hx : x₂ ≠ r) :
    let s := (0 - y₂) / (r - x₂)
    let x₃ := s ^ 2 - r - x₂
    (x₃ - r) * (x₂ - r) = veluT A r := by
  simp only
  unfold veluT
  have hd : r - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination (x₂ - r) * hcurve + (x₂ - r) * htors

private lemma coset_y_identity {A B r x₂ y₂ : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)
    (hx : x₂ ≠ r) :
    let s := (0 - y₂) / (r - x₂)
    let x₃ := s ^ 2 - r - x₂
    s * (r - x₃) = -y₂ * veluT A r / (x₂ - r) ^ 2 := by
  simp only
  unfold veluT
  have hd : r - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  linear_combination y₂ * (r - x₂) ^ 2 * hcurve + y₂ * (r - x₂) ^ 2 * htors

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
lemma veluMapPoint_add {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) =
      veluMapPoint htors P + veluMapPoint htors Q := by
  match P, Q with
  | .zero, _ =>
    show veluMapPoint htors (0 + _) = veluMapPoint htors 0 + veluMapPoint htors _
    rw [zero_add, veluMapPoint_zero, zero_add]
  | _, .zero =>
    show veluMapPoint htors (_ + 0) = veluMapPoint htors _ + veluMapPoint htors 0
    rw [add_zero, veluMapPoint_zero, add_zero]
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    by_cases hxy : x₁ = x₂ ∧ y₁ = negY (shortWS A B) x₂ y₂
    · -- P = -Q: sum is 0
      obtain ⟨hx_eq, hy_eq⟩ := hxy
      rw [Point.add_of_Y_eq hx_eq hy_eq, veluMapPoint_zero]
      have hP_neg : (Point.some x₁ y₁ h₁ : Point (shortWS A B)) =
          -(Point.some x₂ y₂ h₂) := by
        rw [Point.neg_some]; subst hx_eq; subst hy_eq; rfl
      rw [hP_neg, veluMapPoint_neg, neg_add_cancel]
    · -- P + Q ≠ 0
      rw [Point.add_some hxy]
      by_cases hx₁r : x₁ = r
      · -- x₁ = r: P₁ is the torsion point (r, 0)
        have hy₁ : y₁ = 0 := torsion_y_zero htors h₁.left hx₁r
        have hx₂r : x₂ ≠ r := by
          intro heq; apply hxy
          exact ⟨hx₁r ▸ heq ▸ rfl,
            by simp [negY, shortWS, hy₁, torsion_y_zero htors h₂.left heq]⟩
        have hφ₁ : veluMapPoint htors (Point.some x₁ y₁ h₁) =
            (0 : Point (veluQuotCurve A B r)) := by
          unfold veluMapPoint; exact dif_pos hx₁r
        rw [hφ₁, zero_add]
        simp only [hx₁r, hy₁]
        set ℓ := slope (shortWS A B) r x₂ 0 y₂
        set x₃ := addX (shortWS A B) r x₂ ℓ with x₃_def
        have hℓ : ℓ = (0 - y₂) / (r - x₂) :=
          WeierstrassCurve.Affine.slope_of_X_ne (Ne.symm hx₂r)
        have hx₃_eq : x₃ = ℓ ^ 2 - r - x₂ := by
          simp [x₃_def, addX, shortWS]
        have hcoset : (x₃ - r) * (x₂ - r) = veluT A r := by
          rw [hx₃_eq, hℓ]
          exact coset_x_identity htors (shortWS_equation.mp h₂.left) hx₂r
        have hx₃r : x₃ ≠ r := by
          intro heq
          exact veluT_ne_zero htors (by rw [← hcoset, heq, sub_self, zero_mul])
        unfold veluMapPoint
        dsimp only []
        rw [dif_neg hx₃r, dif_neg hx₂r]
        apply point_some_congr
        · -- X: x₃ + t/(x₃-r) = x₂ + t/(x₂-r)
          have h1 : veluT A r / (x₃ - r) = x₂ - r := by
            rw [div_eq_iff (sub_ne_zero.mpr hx₃r)]
            linarith [mul_comm (x₃ - r) (x₂ - r), hcoset]
          have h2 : veluT A r / (x₂ - r) = x₃ - r := by
            rw [div_eq_iff (sub_ne_zero.mpr hx₂r)]
            linarith [hcoset]
          linarith [h1, h2]
        · -- Y-coordinate
          rw [div_eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hx₃r))
            (pow_ne_zero 2 (sub_ne_zero.mpr hx₂r))]
          have haddY : addY (shortWS A B) r x₂ 0 ℓ = -(ℓ * (x₃ - r)) := by
            simp only [addY, negY, shortWS,
              WeierstrassCurve.Affine.negAddY, addX]
            linear_combination ℓ * hx₃_eq
          rw [haddY]
          have hℓ_mul : ℓ * (r - x₂) = -y₂ := by
            rw [hℓ, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hx₂r))]
            ring
          linear_combination
            -(ℓ * (x₃ - r) * (x₂ - r) ^ 2 + y₂ * (x₃ - r) ^ 2) * hcoset
            - (x₃ - r) ^ 2 * (x₂ - r) * (x₂ - x₃) * hℓ_mul
      · by_cases hx₂r : x₂ = r
        · -- x₂ = r: symmetric torsion case (direct proof)
          have hy₂ : y₂ = 0 := torsion_y_zero htors h₂.left hx₂r
          have hφ₂ : veluMapPoint htors (Point.some x₂ y₂ h₂) =
              (0 : Point (veluQuotCurve A B r)) := by
            unfold veluMapPoint; exact dif_pos hx₂r
          rw [hφ₂, add_zero]
          simp only [hx₂r, hy₂]
          set ℓ := slope (shortWS A B) x₁ r y₁ 0
          set x₃ := addX (shortWS A B) x₁ r ℓ with x₃_def
          have hℓ : ℓ = (y₁ - 0) / (x₁ - r) :=
            WeierstrassCurve.Affine.slope_of_X_ne hx₁r
          have hx₃_eq : x₃ = ℓ ^ 2 - x₁ - r := by
            simp [x₃_def, addX, shortWS]
          have hcoset : (x₃ - r) * (x₁ - r) = veluT A r := by
            have h := coset_x_identity htors (shortWS_equation.mp h₁.left) hx₁r
            simp only at h
            rw [hx₃_eq]
            have hsq : ((0 - y₁) / (r - x₁)) ^ 2 = ℓ ^ 2 := by
              rw [hℓ, sub_zero, zero_sub, div_pow, div_pow, neg_sq,
                show (r - x₁ : ℚ) ^ 2 = (x₁ - r) ^ 2 from by ring]
            rw [hsq, show ℓ ^ 2 - r - x₁ = ℓ ^ 2 - x₁ - r from by ring] at h
            exact h
          have hx₃r : x₃ ≠ r := by
            intro heq
            exact veluT_ne_zero htors (by rw [← hcoset, heq, sub_self, zero_mul])
          unfold veluMapPoint
          dsimp only []
          rw [dif_neg hx₃r, dif_neg hx₁r]
          apply point_some_congr
          · have h1 : veluT A r / (x₃ - r) = x₁ - r := by
              rw [div_eq_iff (sub_ne_zero.mpr hx₃r)]
              linarith [mul_comm (x₃ - r) (x₁ - r), hcoset]
            have h2 : veluT A r / (x₁ - r) = x₃ - r := by
              rw [div_eq_iff (sub_ne_zero.mpr hx₁r)]
              linarith [hcoset]
            linarith [h1, h2]
          · rw [div_eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hx₃r))
              (pow_ne_zero 2 (sub_ne_zero.mpr hx₁r))]
            have haddY : addY (shortWS A B) x₁ r y₁ ℓ = -(ℓ * (x₃ - x₁) + y₁) := by
              simp only [addY, negY, shortWS,
                WeierstrassCurve.Affine.negAddY, addX]
              linear_combination ℓ * hx₃_eq
            rw [haddY]
            have hℓ_mul : ℓ * (x₁ - r) = y₁ := by
              rw [hℓ, sub_zero, div_mul_cancel₀ _ (sub_ne_zero.mpr hx₁r)]
            linear_combination
              -ℓ * (x₃ - r) * (x₁ - r) * ((x₃ - r) + (x₁ - r)) * hcoset
              + (2 * (x₃ - r) ^ 2 * (x₁ - r) ^ 2
                 - veluT A r * ((x₃ - r) ^ 2 + (x₁ - r) ^ 2)) * hℓ_mul
        · -- Generic: x₁ ≠ r, x₂ ≠ r
          have hcurve₁ := shortWS_equation.mp h₁.left
          have hcurve₂ := shortWS_equation.mp h₂.left
          have ha₁ : x₁ - r ≠ 0 := sub_ne_zero.mpr hx₁r
          have ha₂ : x₂ - r ≠ 0 := sub_ne_zero.mpr hx₂r
          by_cases hx₁x₂ : x₁ = x₂
          · -- Doubling case: x₁ = x₂
            have h_y_sq : y₁ ^ 2 = y₂ ^ 2 := by
              have h := hcurve₂; rw [← hx₁x₂] at h; linarith
            have h_y_eq : y₁ = y₂ := by
              have h_factor : (y₁ - y₂) * (y₁ + y₂) = 0 := by nlinarith
              rcases mul_eq_zero.mp h_factor with h_diff | h_sum
              · linarith
              · exfalso; apply hxy
                exact ⟨hx₁x₂, by
                  simp only [negY, shortWS, mul_zero, zero_mul, sub_zero]; linarith⟩
            have h_y_ne : y₁ ≠ 0 := by
              intro h; apply hxy
              exact ⟨hx₁x₂, by
                simp only [negY, shortWS, mul_zero, zero_mul, sub_zero]
                linarith [h_y_eq]⟩
            have hy_ne_neg : y₁ ≠ negY (shortWS A B) x₁ y₁ := by
              simp only [negY, shortWS, mul_zero, zero_mul, sub_zero]
              intro h; exact h_y_ne (by linarith)
            unfold veluMapPoint; dsimp only []
            rw [dif_neg hx₁r, dif_neg hx₂r]
            simp only [show x₂ = x₁ from hx₁x₂.symm, show y₂ = y₁ from h_y_eq.symm]
            set ℓ := slope (shortWS A B) x₁ x₁ y₁ y₁
            have hℓ : ℓ = (3 * x₁ ^ 2 + A) / (2 * y₁) := by
              show WeierstrassCurve.Affine.slope (shortWS A B) x₁ x₁ y₁ y₁ =
                (3 * x₁ ^ 2 + A) / (2 * y₁)
              rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_neg]
              simp only [shortWS, negY, mul_zero, zero_mul, sub_zero, add_zero]
              ring
            have hx₃_eq : addX (shortWS A B) x₁ x₁ ℓ = ℓ ^ 2 - 2 * x₁ := by
              simp only [addX, shortWS]; ring
            by_cases hx₃r : addX (shortWS A B) x₁ x₁ ℓ = r
            · -- [2]P₁ in kernel: both sides are 0
              rw [dif_pos hx₃r]
              have hℓsq : ℓ ^ 2 = 2 * x₁ + r := by linarith [hx₃_eq, hx₃r]
              have hat : (x₁ - r) ^ 2 = veluT A r := by
                unfold veluT
                have h_ring : (3 * x₁ ^ 2 + A) ^ 2 - (8 * x₁ + 4 * r) *
                    (x₁ ^ 3 + A * x₁ + B) =
                    ((x₁ - r) ^ 2 - (3 * r ^ 2 + A)) ^ 2 +
                    (-4 * r - 8 * x₁) * (r ^ 3 + A * r + B) := by ring
                rw [htors, mul_zero, add_zero] at h_ring
                have h_sq : (3 * x₁ ^ 2 + A) ^ 2 = 4 * y₁ ^ 2 * ℓ ^ 2 := by
                  rw [hℓ]; field_simp; ring
                have h_sq_zero : ((x₁ - r) ^ 2 - (3 * r ^ 2 + A)) ^ 2 = 0 := by
                  nlinarith [hcurve₁, hℓsq]
                linarith [sq_eq_zero_iff.mp h_sq_zero]
              have hY₁_zero : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 = 0 := by
                rw [hat, sub_self, mul_zero, zero_div]
              have hY_eq : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 =
                  negY (veluQuotCurve A B r) (x₁ + veluT A r / (x₁ - r))
                    (y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2) := by
                simp only [negY, veluQuotCurve, mul_zero, zero_mul, sub_zero]
                rw [hY₁_zero]; ring
              exact (Point.add_of_Y_eq rfl hY_eq).symm
            · -- [2]P₁ not in kernel: apply certs
              rw [dif_neg hx₃r]
              have hat_ne : (x₁ - r) ^ 2 ≠ veluT A r := by
                intro hat; apply hx₃r; rw [hx₃_eq]
                unfold veluT at hat
                have h_ring : (3 * x₁ ^ 2 + A) ^ 2 - (8 * x₁ + 4 * r) *
                    (x₁ ^ 3 + A * x₁ + B) =
                    ((x₁ - r) ^ 2 - (3 * r ^ 2 + A)) ^ 2 +
                    (-4 * r - 8 * x₁) * (r ^ 3 + A * r + B) := by ring
                rw [htors, mul_zero, add_zero, hat, sub_self, zero_pow two_ne_zero] at h_ring
                have h_sq : (3 * x₁ ^ 2 + A) ^ 2 = 4 * y₁ ^ 2 * ℓ ^ 2 := by
                  rw [hℓ]; field_simp; ring
                have h_prod : y₁ ^ 2 * (4 * ℓ ^ 2 - (8 * x₁ + 4 * r)) = 0 := by
                  linear_combination -h_sq + h_ring - (8 * x₁ + 4 * r) * hcurve₁
                rcases mul_eq_zero.mp h_prod with h | h
                · exact absurd (sq_eq_zero_iff.mp h) h_y_ne
                · linarith
              have hY₁_ne : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 ≠ 0 :=
                div_ne_zero (mul_ne_zero h_y_ne (sub_ne_zero.mpr hat_ne))
                  (pow_ne_zero 2 (sub_ne_zero.mpr hx₁r))
              have hy'_ne_neg : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 ≠
                  negY (veluQuotCurve A B r) (x₁ + veluT A r / (x₁ - r))
                    (y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2) := by
                simp only [negY, veluQuotCurve, mul_zero, zero_mul, sub_zero]
                intro h; exact hY₁_ne (by linarith)
              have hxy' : ¬(x₁ + veluT A r / (x₁ - r) = x₁ + veluT A r / (x₁ - r) ∧
                  y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 =
                    negY (veluQuotCurve A B r) (x₁ + veluT A r / (x₁ - r))
                      (y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2)) :=
                fun ⟨_, h⟩ => hy'_ne_neg h
              rw [Point.add_some hxy']
              apply point_some_congr
              · -- X-coordinate identity
                rw [hx₃_eq, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy'_ne_neg]
                simp only [hℓ, addX, negY, shortWS, veluQuotCurve,
                  mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                unfold veluT at hat_ne ⊢
                have ha₃ : ((3 * x₁ ^ 2 + A) / (2 * y₁)) ^ 2 - 2 * x₁ - r ≠ 0 := by
                  have : ℓ ^ 2 - 2 * x₁ - r ≠ 0 := by
                    rw [← hx₃_eq]; exact sub_ne_zero.mpr hx₃r
                  rwa [hℓ] at this
                have hcurve₁' : y₁ ^ 2 - x₁ ^ 3 - A * x₁ + r ^ 3 + A * r = 0 := by
                  linarith [hcurve₁, htors]
                sorry
              · -- Y-coordinate identity
                rw [hx₃_eq, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy'_ne_neg]
                simp only [hℓ, addY, WeierstrassCurve.Affine.negAddY,
                  negY, addX, shortWS, veluQuotCurve,
                  mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                unfold veluT at hat_ne ⊢
                have ha₃ : ((3 * x₁ ^ 2 + A) / (2 * y₁)) ^ 2 - 2 * x₁ - r ≠ 0 := by
                  have : ℓ ^ 2 - 2 * x₁ - r ≠ 0 := by
                    rw [← hx₃_eq]; exact sub_ne_zero.mpr hx₃r
                  rwa [hℓ] at this
                have hcurve₁' : y₁ ^ 2 - x₁ ^ 3 - A * x₁ + r ^ 3 + A * r = 0 := by
                  linarith [hcurve₁, htors]
                sorry
          · -- Addition case: x₁ ≠ x₂
            have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx₁x₂
            unfold veluMapPoint
            dsimp only []
            rw [dif_neg hx₁r, dif_neg hx₂r]
            set ℓ := slope (shortWS A B) x₁ x₂ y₁ y₂
            have hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂) :=
              WeierstrassCurve.Affine.slope_of_X_ne hx₁x₂
            have hx₃_eq : addX (shortWS A B) x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
              simp [addX, shortWS]
            by_cases hx₃r : addX (shortWS A B) x₁ x₂ ℓ = r
            · -- P₁+P₂ in kernel: φ(P₁+P₂) = 0, need φ(P₁)+φ(P₂) = 0
              rw [dif_pos hx₃r]
              -- ℓ² = x₁ + x₂ + r
              have hℓsq : ℓ ^ 2 = x₁ + x₂ + r := by linarith [hx₃_eq, hx₃r]
              -- Sum point P₁+P₂ is on the curve with x = r, so y = 0
              have h_sum_eq := shortWS_equation.mp
                (WeierstrassCurve.Affine.equation_add h₁.left h₂.left hxy)
              rw [hx₃r] at h_sum_eq
              have haddY_zero : addY (shortWS A B) x₁ x₂ y₁ ℓ = 0 := by
                have : (addY (shortWS A B) x₁ x₂ y₁ ℓ) ^ 2 = 0 := by linarith [h_sum_eq, htors]
                exact sq_eq_zero_iff.mp this
              -- addY = -(y₁ + ℓ(r - x₁)), so y₁ = ℓ(x₁ - r)
              have h_y1 : y₁ = ℓ * (x₁ - r) := by
                have : addY (shortWS A B) x₁ x₂ y₁ ℓ = -(y₁ + ℓ * (r - x₁)) := by
                  simp only [addY, negY, shortWS,
                    WeierstrassCurve.Affine.negAddY, addX]
                  linear_combination -ℓ * hℓsq
                linarith [this, haddY_zero]
              have hℓd : ℓ * (x₁ - x₂) = y₁ - y₂ := by rw [hℓ]; field_simp
              have h_y2 : y₂ = ℓ * (x₂ - r) := by linear_combination h_y1 + hℓd
              -- (x₁ - r)(x₂ - r) = veluT A r
              have hat : (x₁ - r) * (x₂ - r) = veluT A r := by
                unfold veluT
                have h_y1_sq : y₁ ^ 2 = ℓ ^ 2 * (x₁ - r) ^ 2 := by rw [h_y1]; ring
                have h_key : (x₁ + x₂ + r) * (x₁ - r) ^ 2 = x₁ ^ 3 + A * x₁ + B := by
                  rw [hℓsq.symm, ← h_y1_sq]; exact hcurve₁
                have h_poly : (x₁ - r) * ((x₁ - r) * (x₂ - r) - (3 * r ^ 2 + A)) = 0 := by
                  linear_combination h_key + htors
                rcases mul_eq_zero.mp h_poly with h | h
                · exact absurd h ha₁
                · linarith
              -- X₁' = X₂'
              have hX_eq : x₁ + veluT A r / (x₁ - r) =
                  x₂ + veluT A r / (x₂ - r) := by
                have h1 : veluT A r / (x₁ - r) = x₂ - r := by
                  rw [div_eq_iff ha₁]; linarith [hat]
                have h2 : veluT A r / (x₂ - r) = x₁ - r := by
                  rw [div_eq_iff ha₂]; linarith [mul_comm (x₁ - r) (x₂ - r), hat]
                linarith [h1, h2]
              -- Y₁' = negY(E', X₂', Y₂')
              have hY_negY : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 =
                  negY (veluQuotCurve A B r) (x₂ + veluT A r / (x₂ - r))
                    (y₂ * ((x₂ - r) ^ 2 - veluT A r) / (x₂ - r) ^ 2) := by
                simp only [negY, veluQuotCurve, mul_zero, sub_zero, zero_mul]
                rw [h_y1, h_y2]
                have hf1 : (x₁ - r) ^ 2 - veluT A r = (x₁ - r) * (x₁ - x₂) := by
                  linear_combination hat
                have hf2 : (x₂ - r) ^ 2 - veluT A r = (x₂ - r) * (x₂ - x₁) := by
                  linear_combination hat
                rw [hf1, hf2]
                field_simp
                ring
              exact (Point.add_of_Y_eq hX_eq hY_negY).symm
            · -- P₁+P₂ not in kernel
              rw [dif_neg hx₃r]
              -- Split on the coset condition a₁a₂ = t
              by_cases hat : (x₁ - r) * (x₂ - r) = veluT A r
              · -- a₁a₂ = t: X₁' = X₂', E' addition is doubling (x₃ ≠ r here)
                -- X₁' = X₂' (from hat, same as kernel case)
                have hX_eq : x₁ + veluT A r / (x₁ - r) =
                    x₂ + veluT A r / (x₂ - r) := by
                  have h1 : veluT A r / (x₁ - r) = x₂ - r := by
                    rw [div_eq_iff ha₁]; linarith [hat]
                  have h2 : veluT A r / (x₂ - r) = x₁ - r := by
                    rw [div_eq_iff ha₂]
                    linarith [mul_comm (x₁ - r) (x₂ - r), hat]
                  linarith [h1, h2]
                -- Y₁' ≠ negY(Y₂'): if equal, forces x₃ = r, contradicting hx₃r
                have hy'_ne_neg : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 ≠
                    negY (veluQuotCurve A B r) (x₂ + veluT A r / (x₂ - r))
                      (y₂ * ((x₂ - r) ^ 2 - veluT A r) / (x₂ - r) ^ 2) := by
                  simp only [negY, veluQuotCurve, mul_zero, sub_zero, zero_mul]
                  intro h_eq
                  apply hx₃r; rw [hx₃_eq, hℓ]
                  have hf1 : (x₁ - r) ^ 2 - veluT A r = (x₁ - r) * (x₁ - x₂) := by
                    linear_combination hat
                  have hf2 : (x₂ - r) ^ 2 - veluT A r = (x₂ - r) * (x₂ - x₁) := by
                    linear_combination hat
                  have h1_ne : (x₁ - r : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 ha₁
                  have h2_ne : (x₂ - r : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 ha₂
                  have h_eq_add : y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 +
                      y₂ * ((x₂ - r) ^ 2 - veluT A r) / (x₂ - r) ^ 2 = 0 := by
                    linarith
                  rw [hf1, hf2, div_add_div _ _ h1_ne h2_ne] at h_eq_add
                  replace h_eq_add :=
                    (div_eq_zero_iff.mp h_eq_add).resolve_right (mul_ne_zero h1_ne h2_ne)
                  have h_factor : (x₁ - r) * (x₂ - r) * (x₁ - x₂) *
                      (y₁ * (x₂ - r) - y₂ * (x₁ - r)) = 0 := by
                    linear_combination h_eq_add
                  rcases mul_eq_zero.mp h_factor with h | h
                  · rcases mul_eq_zero.mp h with h' | h'
                    · rcases mul_eq_zero.mp h' with h'' | h''
                      · exact absurd h'' ha₁
                      · exact absurd h'' ha₂
                    · exact absurd h' hd
                  · have hslope : (y₁ - y₂) * (x₂ - r) = y₂ * (x₁ - x₂) := by
                      linarith
                    have hslope_sq : (y₁ - y₂) ^ 2 * (x₂ - r) ^ 2 =
                        y₂ ^ 2 * (x₁ - x₂) ^ 2 := by
                      linear_combination
                        ((y₁ - y₂) * (x₂ - r) + y₂ * (x₁ - x₂)) * hslope
                    have hat' := hat; unfold veluT at hat'
                    have hnum : (x₁ + x₂ + r) * (x₂ - r) ^ 2 =
                        x₂ ^ 3 + A * x₂ + B := by
                      linear_combination (x₂ - r) * hat' - htors
                    have hgoal : (y₁ - y₂) ^ 2 =
                        (x₁ + x₂ + r) * (x₁ - x₂) ^ 2 := by
                      have h_key : ((y₁ - y₂) ^ 2 -
                          (x₁ + x₂ + r) * (x₁ - x₂) ^ 2) *
                          (x₂ - r) ^ 2 = 0 := by
                        linear_combination hslope_sq -
                          (x₁ - x₂) ^ 2 * hnum +
                          (x₁ - x₂) ^ 2 * hcurve₂
                      rcases mul_eq_zero.mp h_key with hk | hk
                      · linarith
                      · exact absurd hk h2_ne
                    rw [div_pow, hgoal,
                      mul_div_cancel_right₀ _ (pow_ne_zero 2 hd)]
                    ring
                have hxy' : ¬(x₁ + veluT A r / (x₁ - r) =
                      x₂ + veluT A r / (x₂ - r) ∧
                    y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 =
                      negY (veluQuotCurve A B r) (x₂ + veluT A r / (x₂ - r))
                        (y₂ * ((x₂ - r) ^ 2 - veluT A r) / (x₂ - r) ^ 2)) :=
                  fun ⟨_, h⟩ => hy'_ne_neg h
                rw [Point.add_some hxy']
                apply point_some_congr
                · -- X-coordinate identity (E-side addition ↔ E'-side doubling)
                  -- h_ya ≠ 0 from hy'_ne_neg via hat
                  have h_ya_ne : y₁ * (x₂ - r) - y₂ * (x₁ - r) ≠ 0 := by
                    intro h
                    apply hy'_ne_neg
                    simp only [negY, veluQuotCurve, mul_zero, sub_zero, zero_mul]
                    have hf1 : (x₁ - r) ^ 2 - veluT A r = (x₁ - r) * (x₁ - x₂) := by
                      linear_combination hat
                    have hf2 : (x₂ - r) ^ 2 - veluT A r = (x₂ - r) * (x₂ - x₁) := by
                      linear_combination hat
                    rw [hf1, hf2]
                    field_simp
                    linear_combination (x₁ - x₂) * h
                  have hy₁ : y₁ ≠ 0 := by
                    intro hy₁_eq
                    apply h_ya_ne
                    have h_c1_zero : x₁ ^ 3 + A * x₁ + B = 0 := by
                      nlinarith [hcurve₁, hy₁_eq]
                    have h_prod : (x₁ - r) * (x₁ ^ 2 + x₁ * r + r ^ 2 + A) = 0 := by
                      linear_combination h_c1_zero - htors
                    have h_quad : x₁ ^ 2 + x₁ * r + r ^ 2 + A = 0 :=
                      (mul_eq_zero.mp h_prod).resolve_left ha₁
                    have hat' := hat; unfold veluT at hat'
                    have hx₂_prod : (x₁ - r) * (x₂ + x₁ + r) = 0 := by
                      linear_combination hat' + h_quad
                    have hx₂ : x₂ + x₁ + r = 0 :=
                      (mul_eq_zero.mp hx₂_prod).resolve_left ha₁
                    have hy₂sq : y₂ ^ 2 = 0 := by
                      linear_combination hcurve₂ +
                        (A + r ^ 2 + 2 * r * x₁ - r * x₂ + x₁ ^ 2 -
                          x₁ * x₂ + x₂ ^ 2) * hx₂ +
                        (-2 * r - x₁) * h_quad + htors
                    have hy₂ : y₂ = 0 := sq_eq_zero_iff.mp hy₂sq
                    rw [hy₁_eq, hy₂]; ring
                  refine mul_left_cancel₀ h_ya_ne ?_
                  rw [hx₃_eq]
                  rw [WeierstrassCurve.Affine.slope_of_Y_ne hX_eq hy'_ne_neg]
                  simp only [hℓ, addX, negY, shortWS, veluQuotCurve,
                    mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                  unfold veluT
                  unfold veluT at hat
                  have hx₃r_poly : (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
                      x₂ * (x₁ - x₂) ^ 2 - (x₁ - x₂) ^ 2 * r ≠ 0 := by
                    intro h; apply hx₃r; rw [hx₃_eq]
                    have : ℓ ^ 2 = x₁ + x₂ + r := by
                      rw [hℓ, div_pow]; field_simp; nlinarith
                    linarith
                  have hy₁_fac_ne : y₁ * ((x₁ - r) ^ 2 - (3 * r ^ 2 + A)) ≠ 0 := by
                    have hf : (x₁ - r) ^ 2 - (3 * r ^ 2 + A) =
                        (x₁ - r) * (x₁ - x₂) := by
                      linear_combination hat
                    rw [hf]; exact mul_ne_zero hy₁ (mul_ne_zero ha₁ hd)
                  have h_ya_neg : y₁ * (x₂ - r) + y₂ * (x₁ - r) = 0 := by
                    have h_prod : (y₁ * (x₂ - r) - y₂ * (x₁ - r)) *
                        (y₁ * (x₂ - r) + y₂ * (x₁ - r)) = 0 := by
                      linear_combination
                          (x₂ - r) ^ 2 * hcurve₁ -
                          (x₁ - r) ^ 2 * hcurve₂ +
                          (x₁ - r) * (x₂ - r) * (x₁ - x₂) * hat -
                          (x₁ - x₂) * (x₁ + x₂ - 2 * r) * htors
                    exact (mul_eq_zero.mp h_prod).resolve_left h_ya_ne
                  have hy₂_eq : y₂ = -(y₁ * (x₂ - r) / (x₁ - r)) := by
                    have h := h_ya_neg; field_simp at h ⊢; linarith
                  have hE : y₁ ^ 2 - (x₁ - r) ^ 2 * (x₁ + x₂ + r) = 0 := by
                    linear_combination hcurve₁ + (r - x₁) * hat + htors
                  have h_sub_ne : (x₁ - r) ^ 2 - (3 * r ^ 2 + A) ≠ 0 := by
                    have hf : (x₁ - r) ^ 2 - (3 * r ^ 2 + A) =
                        (x₁ - r) * (x₁ - x₂) := by linear_combination hat
                    rw [hf]; exact mul_ne_zero ha₁ hd
                  rw [hy₂_eq] at hx₃r_poly
                  field_simp at hx₃r_poly
                  rw [hy₂_eq]
                  sorry
                · -- Y-coordinate identity
                  have h_ya_ne : y₁ * (x₂ - r) - y₂ * (x₁ - r) ≠ 0 := by
                    intro h
                    apply hy'_ne_neg
                    simp only [negY, veluQuotCurve, mul_zero, sub_zero, zero_mul]
                    have hf1 : (x₁ - r) ^ 2 - veluT A r = (x₁ - r) * (x₁ - x₂) := by
                      linear_combination hat
                    have hf2 : (x₂ - r) ^ 2 - veluT A r = (x₂ - r) * (x₂ - x₁) := by
                      linear_combination hat
                    rw [hf1, hf2]
                    field_simp
                    linear_combination (x₁ - x₂) * h
                  have hy₁ : y₁ ≠ 0 := by
                    intro hy₁_eq
                    apply h_ya_ne
                    have h_c1_zero : x₁ ^ 3 + A * x₁ + B = 0 := by
                      nlinarith [hcurve₁, hy₁_eq]
                    have h_prod : (x₁ - r) * (x₁ ^ 2 + x₁ * r + r ^ 2 + A) = 0 := by
                      linear_combination h_c1_zero - htors
                    have h_quad : x₁ ^ 2 + x₁ * r + r ^ 2 + A = 0 :=
                      (mul_eq_zero.mp h_prod).resolve_left ha₁
                    have hat' := hat; unfold veluT at hat'
                    have hx₂_prod : (x₁ - r) * (x₂ + x₁ + r) = 0 := by
                      linear_combination hat' + h_quad
                    have hx₂ : x₂ + x₁ + r = 0 :=
                      (mul_eq_zero.mp hx₂_prod).resolve_left ha₁
                    have hy₂sq : y₂ ^ 2 = 0 := by
                      linear_combination hcurve₂ +
                        (A + r ^ 2 + 2 * r * x₁ - r * x₂ + x₁ ^ 2 -
                          x₁ * x₂ + x₂ ^ 2) * hx₂ +
                        (-2 * r - x₁) * h_quad + htors
                    have hy₂ : y₂ = 0 := sq_eq_zero_iff.mp hy₂sq
                    rw [hy₁_eq, hy₂]; ring
                  refine mul_left_cancel₀ h_ya_ne ?_
                  rw [hx₃_eq]
                  rw [WeierstrassCurve.Affine.slope_of_Y_ne hX_eq hy'_ne_neg]
                  simp only [hℓ, addY, WeierstrassCurve.Affine.negAddY, negY, addX,
                    shortWS, veluQuotCurve,
                    mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                  unfold veluT
                  unfold veluT at hat
                  have hx₃r_poly : (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
                      x₂ * (x₁ - x₂) ^ 2 - (x₁ - x₂) ^ 2 * r ≠ 0 := by
                    intro h; apply hx₃r; rw [hx₃_eq]
                    have : ℓ ^ 2 = x₁ + x₂ + r := by
                      rw [hℓ, div_pow]; field_simp; nlinarith
                    linarith
                  have hy₁_fac_ne : y₁ * ((x₁ - r) ^ 2 - (3 * r ^ 2 + A)) ≠ 0 := by
                    have hf : (x₁ - r) ^ 2 - (3 * r ^ 2 + A) =
                        (x₁ - r) * (x₁ - x₂) := by
                      linear_combination hat
                    rw [hf]; exact mul_ne_zero hy₁ (mul_ne_zero ha₁ hd)
                  have h_ya_neg : y₁ * (x₂ - r) + y₂ * (x₁ - r) = 0 := by
                    have h_prod : (y₁ * (x₂ - r) - y₂ * (x₁ - r)) *
                        (y₁ * (x₂ - r) + y₂ * (x₁ - r)) = 0 := by
                      linear_combination
                          (x₂ - r) ^ 2 * hcurve₁ -
                          (x₁ - r) ^ 2 * hcurve₂ +
                          (x₁ - r) * (x₂ - r) * (x₁ - x₂) * hat -
                          (x₁ - x₂) * (x₁ + x₂ - 2 * r) * htors
                    exact (mul_eq_zero.mp h_prod).resolve_left h_ya_ne
                  have hy₂_eq : y₂ = -(y₁ * (x₂ - r) / (x₁ - r)) := by
                    have h := h_ya_neg; field_simp at h ⊢; linarith
                  have h_sub_ne : (x₁ - r) ^ 2 - (r ^ 2 * 3 + A) ≠ 0 := by
                    have hf : (x₁ - r) ^ 2 - (r ^ 2 * 3 + A) =
                        (x₁ - r) * (x₁ - x₂) := by linear_combination hat
                    rw [hf]; exact mul_ne_zero ha₁ hd
                  rw [hy₂_eq] at hx₃r_poly
                  field_simp at hx₃r_poly
                  rw [hy₂_eq, WeierstrassCurve.Affine.slope_of_X_ne hx₁x₂]
                  field_simp [hx₃r_poly, h_sub_ne]
                  sorry
              · -- a₁a₂ ≠ t: X₁' ≠ X₂', fully generic addition on E'
                have hX_ne : x₁ + veluT A r / (x₁ - r) ≠
                    x₂ + veluT A r / (x₂ - r) := by
                  intro heq; apply hat
                  have h1 : (x₁ - x₂) * ((x₁ - r) * (x₂ - r) - veluT A r) = 0 := by
                    have := heq; unfold veluT at this ⊢
                    field_simp at this ⊢; linarith
                  rcases mul_eq_zero.mp h1 with h | h
                  · exact absurd (sub_eq_zero.mp h) hx₁x₂
                  · linarith
                have hxy' : ¬(x₁ + veluT A r / (x₁ - r) =
                      x₂ + veluT A r / (x₂ - r) ∧
                    y₁ * ((x₁ - r) ^ 2 - veluT A r) / (x₁ - r) ^ 2 =
                      negY (veluQuotCurve A B r) (x₂ + veluT A r / (x₂ - r))
                        (y₂ * ((x₂ - r) ^ 2 - veluT A r) / (x₂ - r) ^ 2)) :=
                  fun ⟨h, _⟩ => hX_ne h
                rw [Point.add_some hxy']
                apply point_some_congr
                · -- X-coordinate identity
                  simp only [hx₃_eq, addX, shortWS, veluQuotCurve,
                    WeierstrassCurve.Affine.slope_of_X_ne hX_ne,
                    mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                  rw [WeierstrassCurve.Affine.slope_of_X_ne hx₁x₂]
                  unfold veluT
                  -- field_simp needs nonzero proofs matching the exact denominator form
                  have hx₃r_poly : (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
                      x₂ * (x₁ - x₂) ^ 2 - (x₁ - x₂) ^ 2 * r ≠ 0 := by
                    intro h; apply hx₃r; rw [hx₃_eq]
                    have : ℓ ^ 2 = x₁ + x₂ + r := by
                      rw [hℓ, div_pow]; field_simp; nlinarith
                    linarith
                  have hX_den :
                      (x₂ - r) * (x₁ * (x₁ - r) + (3 * r ^ 2 + A)) -
                      (x₁ - r) * (x₂ * (x₂ - r) + (3 * r ^ 2 + A)) ≠ 0 := by
                    intro h
                    have : (x₁ - x₂) * ((x₁ - r) * (x₂ - r) -
                        (3 * r ^ 2 + A)) = 0 := by
                      linear_combination h
                    rcases mul_eq_zero.mp this with h1 | h1
                    · exact absurd h1 hd
                    · exact absurd (by linarith :
                        (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A) hat
                  have hcurve₁' : y₁ ^ 2 - x₁ ^ 3 - A * x₁ + r ^ 3 + A * r = 0 := by
                    linarith [hcurve₁, htors]
                  have hcurve₂' : y₂ ^ 2 - x₂ ^ 3 - A * x₂ + r ^ 3 + A * r = 0 := by
                    linarith [hcurve₂, htors]
                  field_simp [ha₁, ha₂, hd, hx₃r_poly, hX_den]
                  set_option maxHeartbeats 0 in
                  linear_combination
                      (2*A ^ 3*r ^ 4*x₁ ^ 3 - 6*A ^ 3*r ^ 4*x₁ ^ 2*x₂ + 6*A ^ 3*r ^ 4*x₁*x₂ ^ 2 - 2*A ^ 3*r ^ 4*x₂ ^ 3 - 5*A ^ 3*r ^ 3*x₁ ^ 4 + 12*A ^ 3*r ^ 3*x₁ ^ 3*x₂ - 6*A ^ 3*r ^ 3*x₁ ^ 2*x₂ ^ 2 - 4*A ^ 3*r ^ 3*x₁*x₂ ^ 3 + 3*A ^ 3*r ^ 3*x₂ ^ 4 + 4*A ^ 3*r ^ 2*x₁ ^ 5 - 5*A ^ 3*r ^ 2*x₁ ^ 4*x₂ - 8*A ^ 3*r ^ 2*x₁ ^ 3*x₂ ^ 2 + 14*A ^ 3*r ^ 2*x₁ ^ 2*x₂ ^ 3 - 4*A ^ 3*r ^ 2*x₁*x₂ ^ 4 - A ^ 3*r ^ 2*x₂ ^ 5 - A ^ 3*r*x₁ ^ 6 - 2*A ^ 3*r*x₁ ^ 5*x₂ + 10*A ^ 3*r*x₁ ^ 4*x₂ ^ 2 - 8*A ^ 3*r*x₁ ^ 3*x₂ ^ 3 - A ^ 3*r*x₁ ^ 2*x₂ ^ 4 + 2*A ^ 3*r*x₁*x₂ ^ 5 + A ^ 3*x₁ ^ 6*x₂ - 2*A ^ 3*x₁ ^ 5*x₂ ^ 2 + 2*A ^ 3*x₁ ^ 3*x₂ ^ 4 - A ^ 3*x₁ ^ 2*x₂ ^ 5 + 12*A ^ 2*r ^ 6*x₁ ^ 3 - 36*A ^ 2*r ^ 6*x₁ ^ 2*x₂ + 36*A ^ 2*r ^ 6*x₁*x₂ ^ 2 - 12*A ^ 2*r ^ 6*x₂ ^ 3 - 27*A ^ 2*r ^ 5*x₁ ^ 4 + 66*A ^ 2*r ^ 5*x₁ ^ 3*x₂ - 36*A ^ 2*r ^ 5*x₁ ^ 2*x₂ ^ 2 - 18*A ^ 2*r ^ 5*x₁*x₂ ^ 3 + 15*A ^ 2*r ^ 5*x₂ ^ 4 + 19*A ^ 2*r ^ 4*x₁ ^ 5 - 35*A ^ 2*r ^ 4*x₁ ^ 4*x₂ - 2*A ^ 2*r ^ 4*x₁ ^ 3*x₂ ^ 2 + 26*A ^ 2*r ^ 4*x₁ ^ 2*x₂ ^ 3 - A ^ 2*r ^ 4*x₁*x₂ ^ 4 - 7*A ^ 2*r ^ 4*x₂ ^ 5 - 10*A ^ 2*r ^ 3*x₁ ^ 5*x₂ + 35*A ^ 2*r ^ 3*x₁ ^ 4*x₂ ^ 2 - 52*A ^ 2*r ^ 3*x₁ ^ 3*x₂ ^ 3 - 2*A ^ 2*r ^ 3*x₁ ^ 3*y₁ ^ 2 + 4*A ^ 2*r ^ 3*x₁ ^ 3*y₁*y₂ + 46*A ^ 2*r ^ 3*x₁ ^ 2*x₂ ^ 4 + 6*A ^ 2*r ^ 3*x₁ ^ 2*x₂*y₁ ^ 2 - 12*A ^ 2*r ^ 3*x₁ ^ 2*x₂*y₁*y₂ - 26*A ^ 2*r ^ 3*x₁*x₂ ^ 5 - 6*A ^ 2*r ^ 3*x₁*x₂ ^ 2*y₁ ^ 2 + 12*A ^ 2*r ^ 3*x₁*x₂ ^ 2*y₁*y₂ + 7*A ^ 2*r ^ 3*x₂ ^ 6 + 2*A ^ 2*r ^ 3*x₂ ^ 3*y₁ ^ 2 - 4*A ^ 2*r ^ 3*x₂ ^ 3*y₁*y₂ - 2*A ^ 2*r ^ 2*x₁ ^ 7 - 4*A ^ 2*r ^ 2*x₁ ^ 6*x₂ + 18*A ^ 2*r ^ 2*x₁ ^ 5*x₂ ^ 2 - 5*A ^ 2*r ^ 2*x₁ ^ 4*x₂ ^ 3 + A ^ 2*r ^ 2*x₁ ^ 4*y₁ ^ 2 - 2*A ^ 2*r ^ 2*x₁ ^ 4*y₁*y₂ - 4*A ^ 2*r ^ 2*x₁ ^ 4*y₂ ^ 2 - 22*A ^ 2*r ^ 2*x₁ ^ 3*x₂ ^ 4 + 2*A ^ 2*r ^ 2*x₁ ^ 3*x₂*y₁ ^ 2 - 4*A ^ 2*r ^ 2*x₁ ^ 3*x₂*y₁*y₂ + 16*A ^ 2*r ^ 2*x₁ ^ 3*x₂*y₂ ^ 2 + 18*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 5 - 12*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 2*y₁ ^ 2 + 24*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 24*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 - 2*A ^ 2*r ^ 2*x₁*x₂ ^ 6 + 14*A ^ 2*r ^ 2*x₁*x₂ ^ 3*y₁ ^ 2 - 28*A ^ 2*r ^ 2*x₁*x₂ ^ 3*y₁*y₂ + 16*A ^ 2*r ^ 2*x₁*x₂ ^ 3*y₂ ^ 2 - A ^ 2*r ^ 2*x₂ ^ 7 - 5*A ^ 2*r ^ 2*x₂ ^ 4*y₁ ^ 2 + 10*A ^ 2*r ^ 2*x₂ ^ 4*y₁*y₂ - 4*A ^ 2*r ^ 2*x₂ ^ 4*y₂ ^ 2 + 4*A ^ 2*r*x₁ ^ 7*x₂ - A ^ 2*r*x₁ ^ 6*x₂ ^ 2 - 28*A ^ 2*r*x₁ ^ 5*x₂ ^ 3 + 4*A ^ 2*r*x₁ ^ 5*y₂ ^ 2 + 45*A ^ 2*r*x₁ ^ 4*x₂ ^ 4 - 2*A ^ 2*r*x₁ ^ 4*x₂*y₁ ^ 2 + 4*A ^ 2*r*x₁ ^ 4*x₂*y₁*y₂ - 12*A ^ 2*r*x₁ ^ 4*x₂*y₂ ^ 2 - 14*A ^ 2*r*x₁ ^ 3*x₂ ^ 5 + 2*A ^ 2*r*x₁ ^ 3*x₂ ^ 2*y₁ ^ 2 - 4*A ^ 2*r*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 8*A ^ 2*r*x₁ ^ 3*x₂ ^ 2*y₂ ^ 2 - 17*A ^ 2*r*x₁ ^ 2*x₂ ^ 6 + 6*A ^ 2*r*x₁ ^ 2*x₂ ^ 3*y₁ ^ 2 - 12*A ^ 2*r*x₁ ^ 2*x₂ ^ 3*y₁*y₂ + 8*A ^ 2*r*x₁ ^ 2*x₂ ^ 3*y₂ ^ 2 + 14*A ^ 2*r*x₁*x₂ ^ 7 - 10*A ^ 2*r*x₁*x₂ ^ 4*y₁ ^ 2 + 20*A ^ 2*r*x₁*x₂ ^ 4*y₁*y₂ - 12*A ^ 2*r*x₁*x₂ ^ 4*y₂ ^ 2 - 3*A ^ 2*r*x₂ ^ 8 + 4*A ^ 2*r*x₂ ^ 5*y₁ ^ 2 - 8*A ^ 2*r*x₂ ^ 5*y₁*y₂ + 4*A ^ 2*r*x₂ ^ 5*y₂ ^ 2 - 2*A ^ 2*x₁ ^ 7*x₂ ^ 2 + 5*A ^ 2*x₁ ^ 6*x₂ ^ 3 - A ^ 2*x₁ ^ 6*y₂ ^ 2 + A ^ 2*x₁ ^ 5*x₂ ^ 4 + 2*A ^ 2*x₁ ^ 5*x₂*y₂ ^ 2 - 13*A ^ 2*x₁ ^ 4*x₂ ^ 5 + A ^ 2*x₁ ^ 4*x₂ ^ 2*y₁ ^ 2 - 2*A ^ 2*x₁ ^ 4*x₂ ^ 2*y₁*y₂ + A ^ 2*x₁ ^ 4*x₂ ^ 2*y₂ ^ 2 + 12*A ^ 2*x₁ ^ 3*x₂ ^ 6 - 2*A ^ 2*x₁ ^ 3*x₂ ^ 3*y₁ ^ 2 + 4*A ^ 2*x₁ ^ 3*x₂ ^ 3*y₁*y₂ - 4*A ^ 2*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 - A ^ 2*x₁ ^ 2*x₂ ^ 7 + A ^ 2*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 - 3*A ^ 2*x₁*x₂ ^ 8 + 2*A ^ 2*x₁*x₂ ^ 5*y₁ ^ 2 - 4*A ^ 2*x₁*x₂ ^ 5*y₁*y₂ + 2*A ^ 2*x₁*x₂ ^ 5*y₂ ^ 2 + A ^ 2*x₂ ^ 9 - A ^ 2*x₂ ^ 6*y₁ ^ 2 + 2*A ^ 2*x₂ ^ 6*y₁*y₂ - A ^ 2*x₂ ^ 6*y₂ ^ 2 + 22*A*r ^ 8*x₁ ^ 3 - 66*A*r ^ 8*x₁ ^ 2*x₂ + 66*A*r ^ 8*x₁*x₂ ^ 2 - 22*A*r ^ 8*x₂ ^ 3 - 43*A*r ^ 7*x₁ ^ 4 + 110*A*r ^ 7*x₁ ^ 3*x₂ - 72*A*r ^ 7*x₁ ^ 2*x₂ ^ 2 - 14*A*r ^ 7*x₁*x₂ ^ 3 + 19*A*r ^ 7*x₂ ^ 4 + 27*A*r ^ 6*x₁ ^ 5 - 92*A*r ^ 6*x₁ ^ 4*x₂ + 132*A*r ^ 6*x₁ ^ 3*x₂ ^ 2 - 114*A*r ^ 6*x₁ ^ 2*x₂ ^ 3 + 65*A*r ^ 6*x₁*x₂ ^ 4 - 18*A*r ^ 6*x₂ ^ 5 + 16*A*r ^ 5*x₁ ^ 6 - 36*A*r ^ 5*x₁ ^ 5*x₂ + 63*A*r ^ 5*x₁ ^ 4*x₂ ^ 2 - 166*A*r ^ 5*x₁ ^ 3*x₂ ^ 3 - 10*A*r ^ 5*x₁ ^ 3*y₁ ^ 2 + 20*A*r ^ 5*x₁ ^ 3*y₁*y₂ + 240*A*r ^ 5*x₁ ^ 2*x₂ ^ 4 + 30*A*r ^ 5*x₁ ^ 2*x₂*y₁ ^ 2 - 60*A*r ^ 5*x₁ ^ 2*x₂*y₁*y₂ - 150*A*r ^ 5*x₁*x₂ ^ 5 - 30*A*r ^ 5*x₁*x₂ ^ 2*y₁ ^ 2 + 60*A*r ^ 5*x₁*x₂ ^ 2*y₁*y₂ + 33*A*r ^ 5*x₂ ^ 6 + 10*A*r ^ 5*x₂ ^ 3*y₁ ^ 2 - 20*A*r ^ 5*x₂ ^ 3*y₁*y₂ - 9*A*r ^ 4*x₁ ^ 7 - 29*A*r ^ 4*x₁ ^ 6*x₂ + 132*A*r ^ 4*x₁ ^ 5*x₂ ^ 2 - 115*A*r ^ 4*x₁ ^ 4*x₂ ^ 3 + 2*A*r ^ 4*x₁ ^ 4*y₁ ^ 2 - 6*A*r ^ 4*x₁ ^ 4*y₁*y₂ - 18*A*r ^ 4*x₁ ^ 4*y₂ ^ 2 - 21*A*r ^ 4*x₁ ^ 3*x₂ ^ 4 + 18*A*r ^ 4*x₁ ^ 3*x₂*y₁ ^ 2 - 28*A*r ^ 4*x₁ ^ 3*x₂*y₁*y₂ + 72*A*r ^ 4*x₁ ^ 3*x₂*y₂ ^ 2 + 57*A*r ^ 4*x₁ ^ 2*x₂ ^ 5 - 66*A*r ^ 4*x₁ ^ 2*x₂ ^ 2*y₁ ^ 2 + 120*A*r ^ 4*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 108*A*r ^ 4*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 - 14*A*r ^ 4*x₁*x₂ ^ 6 + 70*A*r ^ 4*x₁*x₂ ^ 3*y₁ ^ 2 - 132*A*r ^ 4*x₁*x₂ ^ 3*y₁*y₂ + 72*A*r ^ 4*x₁*x₂ ^ 3*y₂ ^ 2 - A*r ^ 4*x₂ ^ 7 - 24*A*r ^ 4*x₂ ^ 4*y₁ ^ 2 + 46*A*r ^ 4*x₂ ^ 4*y₁*y₂ - 18*A*r ^ 4*x₂ ^ 4*y₂ ^ 2 - A*r ^ 3*x₁ ^ 8 + 20*A*r ^ 3*x₁ ^ 7*x₂ - 12*A*r ^ 3*x₁ ^ 6*x₂ ^ 2 - 112*A*r ^ 3*x₁ ^ 5*x₂ ^ 3 + 2*A*r ^ 3*x₁ ^ 5*y₁ ^ 2 + 12*A*r ^ 3*x₁ ^ 5*y₂ ^ 2 + 210*A*r ^ 3*x₁ ^ 4*x₂ ^ 4 - 6*A*r ^ 3*x₁ ^ 4*x₂*y₁ ^ 2 - 36*A*r ^ 3*x₁ ^ 4*x₂*y₂ ^ 2 - 102*A*r ^ 3*x₁ ^ 3*x₂ ^ 5 - 12*A*r ^ 3*x₁ ^ 3*x₂ ^ 2*y₁ ^ 2 + 32*A*r ^ 3*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 24*A*r ^ 3*x₁ ^ 3*x₂ ^ 2*y₂ ^ 2 - 46*A*r ^ 3*x₁ ^ 2*x₂ ^ 6 + 52*A*r ^ 3*x₁ ^ 2*x₂ ^ 3*y₁ ^ 2 - 96*A*r ^ 3*x₁ ^ 2*x₂ ^ 3*y₁*y₂ + 24*A*r ^ 3*x₁ ^ 2*x₂ ^ 3*y₂ ^ 2 + 58*A*r ^ 3*x₁*x₂ ^ 7 - 54*A*r ^ 3*x₁*x₂ ^ 4*y₁ ^ 2 + 96*A*r ^ 3*x₁*x₂ ^ 4*y₁*y₂ - 36*A*r ^ 3*x₁*x₂ ^ 4*y₂ ^ 2 - 15*A*r ^ 3*x₂ ^ 8 + 18*A*r ^ 3*x₂ ^ 5*y₁ ^ 2 - 32*A*r ^ 3*x₂ ^ 5*y₁*y₂ + 12*A*r ^ 3*x₂ ^ 5*y₂ ^ 2 + 3*A*r ^ 2*x₁ ^ 8*x₂ - 18*A*r ^ 2*x₁ ^ 7*x₂ ^ 2 + 26*A*r ^ 2*x₁ ^ 6*x₂ ^ 3 - 2*A*r ^ 2*x₁ ^ 6*y₁*y₂ + 3*A*r ^ 2*x₁ ^ 5*x₂ ^ 4 - 6*A*r ^ 2*x₁ ^ 5*x₂*y₁ ^ 2 + 12*A*r ^ 2*x₁ ^ 5*x₂*y₁*y₂ + 12*A*r ^ 2*x₁ ^ 5*x₂*y₂ ^ 2 - 27*A*r ^ 2*x₁ ^ 4*x₂ ^ 5 + 12*A*r ^ 2*x₁ ^ 4*x₂ ^ 2*y₁ ^ 2 - 6*A*r ^ 2*x₁ ^ 4*x₂ ^ 2*y₁*y₂ - 48*A*r ^ 2*x₁ ^ 4*x₂ ^ 2*y₂ ^ 2 + 6*A*r ^ 2*x₁ ^ 3*x₂ ^ 6 + 4*A*r ^ 2*x₁ ^ 3*x₂ ^ 3*y₁ ^ 2 - 40*A*r ^ 2*x₁ ^ 3*x₂ ^ 3*y₁*y₂ + 72*A*r ^ 2*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 + 18*A*r ^ 2*x₁ ^ 2*x₂ ^ 7 - 24*A*r ^ 2*x₁ ^ 2*x₂ ^ 4*y₁ ^ 2 + 66*A*r ^ 2*x₁ ^ 2*x₂ ^ 4*y₁*y₂ - 48*A*r ^ 2*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 - 15*A*r ^ 2*x₁*x₂ ^ 8 + 18*A*r ^ 2*x₁*x₂ ^ 5*y₁ ^ 2 - 36*A*r ^ 2*x₁*x₂ ^ 5*y₁*y₂ + 12*A*r ^ 2*x₁*x₂ ^ 5*y₂ ^ 2 + 4*A*r ^ 2*x₂ ^ 9 - 4*A*r ^ 2*x₂ ^ 6*y₁ ^ 2 + 6*A*r ^ 2*x₂ ^ 6*y₁*y₂ - 3*A*r*x₁ ^ 8*x₂ ^ 2 + 12*A*r*x₁ ^ 7*x₂ ^ 3 - 7*A*r*x₁ ^ 6*x₂ ^ 4 + 4*A*r*x₁ ^ 6*x₂*y₁*y₂ - 12*A*r*x₁ ^ 6*x₂*y₂ ^ 2 - 18*A*r*x₁ ^ 5*x₂ ^ 5 + 6*A*r*x₁ ^ 5*x₂ ^ 2*y₁ ^ 2 - 24*A*r*x₁ ^ 5*x₂ ^ 2*y₁*y₂ + 36*A*r*x₁ ^ 5*x₂ ^ 2*y₂ ^ 2 + 17*A*r*x₁ ^ 4*x₂ ^ 6 - 14*A*r*x₁ ^ 4*x₂ ^ 3*y₁ ^ 2 + 36*A*r*x₁ ^ 4*x₂ ^ 3*y₁*y₂ - 24*A*r*x₁ ^ 4*x₂ ^ 3*y₂ ^ 2 + 10*A*r*x₁ ^ 3*x₂ ^ 7 + 6*A*r*x₁ ^ 3*x₂ ^ 4*y₁ ^ 2 - 4*A*r*x₁ ^ 3*x₂ ^ 4*y₁*y₂ - 24*A*r*x₁ ^ 3*x₂ ^ 4*y₂ ^ 2 - 15*A*r*x₁ ^ 2*x₂ ^ 8 + 6*A*r*x₁ ^ 2*x₂ ^ 5*y₁ ^ 2 - 24*A*r*x₁ ^ 2*x₂ ^ 5*y₁*y₂ + 36*A*r*x₁ ^ 2*x₂ ^ 5*y₂ ^ 2 + 4*A*r*x₁*x₂ ^ 9 - 4*A*r*x₁*x₂ ^ 6*y₁ ^ 2 + 12*A*r*x₁*x₂ ^ 6*y₁*y₂ - 12*A*r*x₁*x₂ ^ 6*y₂ ^ 2 + A*x₁ ^ 8*x₂ ^ 3 - 5*A*x₁ ^ 7*x₂ ^ 4 + 6*A*x₁ ^ 6*x₂ ^ 5 - 2*A*x₁ ^ 6*x₂ ^ 2*y₁*y₂ + 6*A*x₁ ^ 6*x₂ ^ 2*y₂ ^ 2 + 4*A*x₁ ^ 5*x₂ ^ 6 - 2*A*x₁ ^ 5*x₂ ^ 3*y₁ ^ 2 + 12*A*x₁ ^ 5*x₂ ^ 3*y₁*y₂ - 24*A*x₁ ^ 5*x₂ ^ 3*y₂ ^ 2 - 13*A*x₁ ^ 4*x₂ ^ 7 + 6*A*x₁ ^ 4*x₂ ^ 4*y₁ ^ 2 - 24*A*x₁ ^ 4*x₂ ^ 4*y₁*y₂ + 36*A*x₁ ^ 4*x₂ ^ 4*y₂ ^ 2 + 9*A*x₁ ^ 3*x₂ ^ 8 - 6*A*x₁ ^ 3*x₂ ^ 5*y₁ ^ 2 + 20*A*x₁ ^ 3*x₂ ^ 5*y₁*y₂ - 24*A*x₁ ^ 3*x₂ ^ 5*y₂ ^ 2 - 2*A*x₁ ^ 2*x₂ ^ 9 + 2*A*x₁ ^ 2*x₂ ^ 6*y₁ ^ 2 - 6*A*x₁ ^ 2*x₂ ^ 6*y₁*y₂ + 6*A*x₁ ^ 2*x₂ ^ 6*y₂ ^ 2 + 12*r ^ 10*x₁ ^ 3 - 36*r ^ 10*x₁ ^ 2*x₂ + 36*r ^ 10*x₁*x₂ ^ 2 - 12*r ^ 10*x₂ ^ 3 - 21*r ^ 9*x₁ ^ 4 + 60*r ^ 9*x₁ ^ 3*x₂ - 54*r ^ 9*x₁ ^ 2*x₂ ^ 2 + 12*r ^ 9*x₁*x₂ ^ 3 + 3*r ^ 9*x₂ ^ 4 + 18*r ^ 8*x₁ ^ 5 - 96*r ^ 8*x₁ ^ 4*x₂ + 198*r ^ 8*x₁ ^ 3*x₂ ^ 2 - 198*r ^ 8*x₁ ^ 2*x₂ ^ 3 + 96*r ^ 8*x₁*x₂ ^ 4 - 18*r ^ 8*x₂ ^ 5 + 21*r ^ 7*x₁ ^ 6 - 72*r ^ 7*x₁ ^ 5*x₂ + 144*r ^ 7*x₁ ^ 4*x₂ ^ 2 - 246*r ^ 7*x₁ ^ 3*x₂ ^ 3 - 12*r ^ 7*x₁ ^ 3*y₁ ^ 2 + 24*r ^ 7*x₁ ^ 3*y₁*y₂ + 279*r ^ 7*x₁ ^ 2*x₂ ^ 4 + 36*r ^ 7*x₁ ^ 2*x₂*y₁ ^ 2 - 72*r ^ 7*x₁ ^ 2*x₂*y₁*y₂ - 162*r ^ 7*x₁*x₂ ^ 5 - 36*r ^ 7*x₁*x₂ ^ 2*y₁ ^ 2 + 72*r ^ 7*x₁*x₂ ^ 2*y₁*y₂ + 36*r ^ 7*x₂ ^ 6 + 12*r ^ 7*x₂ ^ 3*y₁ ^ 2 - 24*r ^ 7*x₂ ^ 3*y₁*y₂ - 9*r ^ 6*x₁ ^ 7 - 24*r ^ 6*x₁ ^ 6*x₂ + 180*r ^ 6*x₁ ^ 5*x₂ ^ 2 - 300*r ^ 6*x₁ ^ 4*x₂ ^ 3 - 3*r ^ 6*x₁ ^ 4*y₁ ^ 2 - 18*r ^ 6*x₁ ^ 4*y₂ ^ 2 + 189*r ^ 6*x₁ ^ 3*x₂ ^ 4 + 36*r ^ 6*x₁ ^ 3*x₂*y₁ ^ 2 - 48*r ^ 6*x₁ ^ 3*x₂*y₁*y₂ + 72*r ^ 6*x₁ ^ 3*x₂*y₂ ^ 2 - 18*r ^ 6*x₁ ^ 2*x₂ ^ 5 - 90*r ^ 6*x₁ ^ 2*x₂ ^ 2*y₁ ^ 2 + 144*r ^ 6*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 108*r ^ 6*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 - 24*r ^ 6*x₁*x₂ ^ 6 + 84*r ^ 6*x₁*x₂ ^ 3*y₁ ^ 2 - 144*r ^ 6*x₁*x₂ ^ 3*y₁*y₂ + 72*r ^ 6*x₁*x₂ ^ 3*y₂ ^ 2 + 6*r ^ 6*x₂ ^ 7 - 27*r ^ 6*x₂ ^ 4*y₁ ^ 2 + 48*r ^ 6*x₂ ^ 4*y₁*y₂ - 18*r ^ 6*x₂ ^ 4*y₂ ^ 2 - 3*r ^ 5*x₁ ^ 8 + 24*r ^ 5*x₁ ^ 7*x₂ - 27*r ^ 5*x₁ ^ 6*x₂ ^ 2 - 84*r ^ 5*x₁ ^ 5*x₂ ^ 3 + 6*r ^ 5*x₁ ^ 5*y₁ ^ 2 + 225*r ^ 5*x₁ ^ 4*x₂ ^ 4 - 36*r ^ 5*x₁ ^ 4*x₂*y₁*y₂ - 180*r ^ 5*x₁ ^ 3*x₂ ^ 5 - 54*r ^ 5*x₁ ^ 3*x₂ ^ 2*y₁ ^ 2 + 132*r ^ 5*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 15*r ^ 5*x₁ ^ 2*x₂ ^ 6 + 102*r ^ 5*x₁ ^ 2*x₂ ^ 3*y₁ ^ 2 - 180*r ^ 5*x₁ ^ 2*x₂ ^ 3*y₁*y₂ + 48*r ^ 5*x₁*x₂ ^ 7 - 72*r ^ 5*x₁*x₂ ^ 4*y₁ ^ 2 + 108*r ^ 5*x₁*x₂ ^ 4*y₁*y₂ - 18*r ^ 5*x₂ ^ 8 + 18*r ^ 5*x₂ ^ 5*y₁ ^ 2 - 24*r ^ 5*x₂ ^ 5*y₁*y₂ + 9*r ^ 4*x₁ ^ 8*x₂ - 36*r ^ 4*x₁ ^ 7*x₂ ^ 2 + 33*r ^ 4*x₁ ^ 6*x₂ ^ 3 - 6*r ^ 4*x₁ ^ 6*y₁*y₂ + 9*r ^ 4*x₁ ^ 6*y₂ ^ 2 - 18*r ^ 4*x₁ ^ 5*x₂*y₁ ^ 2 + 36*r ^ 4*x₁ ^ 5*x₂*y₁*y₂ + 18*r ^ 4*x₁ ^ 5*x₂*y₂ ^ 2 + 36*r ^ 4*x₁ ^ 4*x₂ ^ 5 + 27*r ^ 4*x₁ ^ 4*x₂ ^ 2*y₁ ^ 2 - 153*r ^ 4*x₁ ^ 4*x₂ ^ 2*y₂ ^ 2 - 90*r ^ 4*x₁ ^ 3*x₂ ^ 6 + 30*r ^ 4*x₁ ^ 3*x₂ ^ 3*y₁ ^ 2 - 156*r ^ 4*x₁ ^ 3*x₂ ^ 3*y₁*y₂ + 252*r ^ 4*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 + 63*r ^ 4*x₁ ^ 2*x₂ ^ 7 - 72*r ^ 4*x₁ ^ 2*x₂ ^ 4*y₁ ^ 2 + 198*r ^ 4*x₁ ^ 2*x₂ ^ 4*y₁*y₂ - 153*r ^ 4*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 - 18*r ^ 4*x₁*x₂ ^ 8 + 36*r ^ 4*x₁*x₂ ^ 5*y₁ ^ 2 - 72*r ^ 4*x₁*x₂ ^ 5*y₁*y₂ + 18*r ^ 4*x₁*x₂ ^ 5*y₂ ^ 2 + 3*r ^ 4*x₂ ^ 9 - 3*r ^ 4*x₂ ^ 6*y₁ ^ 2 + 9*r ^ 4*x₂ ^ 6*y₂ ^ 2 - 9*r ^ 3*x₁ ^ 8*x₂ ^ 2 + 36*r ^ 3*x₁ ^ 7*x₂ ^ 3 - 21*r ^ 3*x₁ ^ 6*x₂ ^ 4 + 12*r ^ 3*x₁ ^ 6*x₂*y₁*y₂ - 36*r ^ 3*x₁ ^ 6*x₂*y₂ ^ 2 - 54*r ^ 3*x₁ ^ 5*x₂ ^ 5 + 18*r ^ 3*x₁ ^ 5*x₂ ^ 2*y₁ ^ 2 - 72*r ^ 3*x₁ ^ 5*x₂ ^ 2*y₁*y₂ + 108*r ^ 3*x₁ ^ 5*x₂ ^ 2*y₂ ^ 2 + 51*r ^ 3*x₁ ^ 4*x₂ ^ 6 - 42*r ^ 3*x₁ ^ 4*x₂ ^ 3*y₁ ^ 2 + 108*r ^ 3*x₁ ^ 4*x₂ ^ 3*y₁*y₂ - 72*r ^ 3*x₁ ^ 4*x₂ ^ 3*y₂ ^ 2 + 30*r ^ 3*x₁ ^ 3*x₂ ^ 7 + 18*r ^ 3*x₁ ^ 3*x₂ ^ 4*y₁ ^ 2 - 12*r ^ 3*x₁ ^ 3*x₂ ^ 4*y₁*y₂ - 72*r ^ 3*x₁ ^ 3*x₂ ^ 4*y₂ ^ 2 - 45*r ^ 3*x₁ ^ 2*x₂ ^ 8 + 18*r ^ 3*x₁ ^ 2*x₂ ^ 5*y₁ ^ 2 - 72*r ^ 3*x₁ ^ 2*x₂ ^ 5*y₁*y₂ + 108*r ^ 3*x₁ ^ 2*x₂ ^ 5*y₂ ^ 2 + 12*r ^ 3*x₁*x₂ ^ 9 - 12*r ^ 3*x₁*x₂ ^ 6*y₁ ^ 2 + 36*r ^ 3*x₁*x₂ ^ 6*y₁*y₂ - 36*r ^ 3*x₁*x₂ ^ 6*y₂ ^ 2 + 3*r ^ 2*x₁ ^ 8*x₂ ^ 3 - 15*r ^ 2*x₁ ^ 7*x₂ ^ 4 + 18*r ^ 2*x₁ ^ 6*x₂ ^ 5 - 6*r ^ 2*x₁ ^ 6*x₂ ^ 2*y₁*y₂ + 18*r ^ 2*x₁ ^ 6*x₂ ^ 2*y₂ ^ 2 + 12*r ^ 2*x₁ ^ 5*x₂ ^ 6 - 6*r ^ 2*x₁ ^ 5*x₂ ^ 3*y₁ ^ 2 + 36*r ^ 2*x₁ ^ 5*x₂ ^ 3*y₁*y₂ - 72*r ^ 2*x₁ ^ 5*x₂ ^ 3*y₂ ^ 2 - 39*r ^ 2*x₁ ^ 4*x₂ ^ 7 + 18*r ^ 2*x₁ ^ 4*x₂ ^ 4*y₁ ^ 2 - 72*r ^ 2*x₁ ^ 4*x₂ ^ 4*y₁*y₂ + 108*r ^ 2*x₁ ^ 4*x₂ ^ 4*y₂ ^ 2 + 27*r ^ 2*x₁ ^ 3*x₂ ^ 8 - 18*r ^ 2*x₁ ^ 3*x₂ ^ 5*y₁ ^ 2 + 60*r ^ 2*x₁ ^ 3*x₂ ^ 5*y₁*y₂ - 72*r ^ 2*x₁ ^ 3*x₂ ^ 5*y₂ ^ 2 - 6*r ^ 2*x₁ ^ 2*x₂ ^ 9 + 6*r ^ 2*x₁ ^ 2*x₂ ^ 6*y₁ ^ 2 - 18*r ^ 2*x₁ ^ 2*x₂ ^ 6*y₁*y₂ + 18*r ^ 2*x₁ ^ 2*x₂ ^ 6*y₂ ^ 2)
                      * hcurve₁' +
                      (-2*A ^ 3*r ^ 4*x₁ ^ 3 + 6*A ^ 3*r ^ 4*x₁ ^ 2*x₂ - 6*A ^ 3*r ^ 4*x₁*x₂ ^ 2 + 2*A ^ 3*r ^ 4*x₂ ^ 3 + 7*A ^ 3*r ^ 3*x₁ ^ 4 - 20*A ^ 3*r ^ 3*x₁ ^ 3*x₂ + 18*A ^ 3*r ^ 3*x₁ ^ 2*x₂ ^ 2 - 4*A ^ 3*r ^ 3*x₁*x₂ ^ 3 - A ^ 3*r ^ 3*x₂ ^ 4 - 9*A ^ 3*r ^ 2*x₁ ^ 5 + 24*A ^ 3*r ^ 2*x₁ ^ 4*x₂ - 18*A ^ 3*r ^ 2*x₁ ^ 3*x₂ ^ 2 + 3*A ^ 3*r ^ 2*x₁*x₂ ^ 4 + 5*A ^ 3*r*x₁ ^ 6 - 12*A ^ 3*r*x₁ ^ 5*x₂ + 6*A ^ 3*r*x₁ ^ 4*x₂ ^ 2 + 4*A ^ 3*r*x₁ ^ 3*x₂ ^ 3 - 3*A ^ 3*r*x₁ ^ 2*x₂ ^ 4 - A ^ 3*x₁ ^ 7 + 2*A ^ 3*x₁ ^ 6*x₂ - 2*A ^ 3*x₁ ^ 4*x₂ ^ 3 + A ^ 3*x₁ ^ 3*x₂ ^ 4 - 12*A ^ 2*r ^ 6*x₁ ^ 3 + 36*A ^ 2*r ^ 6*x₁ ^ 2*x₂ - 36*A ^ 2*r ^ 6*x₁*x₂ ^ 2 + 12*A ^ 2*r ^ 6*x₂ ^ 3 + 37*A ^ 2*r ^ 5*x₁ ^ 4 - 106*A ^ 2*r ^ 5*x₁ ^ 3*x₂ + 96*A ^ 2*r ^ 5*x₁ ^ 2*x₂ ^ 2 - 22*A ^ 2*r ^ 5*x₁*x₂ ^ 3 - 5*A ^ 2*r ^ 5*x₂ ^ 4 - 41*A ^ 2*r ^ 4*x₁ ^ 5 + 119*A ^ 2*r ^ 4*x₁ ^ 4*x₂ - 114*A ^ 2*r ^ 4*x₁ ^ 3*x₂ ^ 2 + 38*A ^ 2*r ^ 4*x₁ ^ 2*x₂ ^ 3 - 5*A ^ 2*r ^ 4*x₁*x₂ ^ 4 + 3*A ^ 2*r ^ 4*x₂ ^ 5 + 20*A ^ 2*r ^ 3*x₁ ^ 6 - 76*A ^ 2*r ^ 3*x₁ ^ 5*x₂ + 117*A ^ 2*r ^ 3*x₁ ^ 4*x₂ ^ 2 - 96*A ^ 2*r ^ 3*x₁ ^ 3*x₂ ^ 3 - 4*A ^ 2*r ^ 3*x₁ ^ 3*y₁*y₂ + 2*A ^ 2*r ^ 3*x₁ ^ 3*y₂ ^ 2 + 46*A ^ 2*r ^ 3*x₁ ^ 2*x₂ ^ 4 + 12*A ^ 2*r ^ 3*x₁ ^ 2*x₂*y₁*y₂ - 6*A ^ 2*r ^ 3*x₁ ^ 2*x₂*y₂ ^ 2 - 12*A ^ 2*r ^ 3*x₁*x₂ ^ 5 - 12*A ^ 2*r ^ 3*x₁*x₂ ^ 2*y₁*y₂ + 6*A ^ 2*r ^ 3*x₁*x₂ ^ 2*y₂ ^ 2 + A ^ 2*r ^ 3*x₂ ^ 6 + 4*A ^ 2*r ^ 3*x₂ ^ 3*y₁*y₂ - 2*A ^ 2*r ^ 3*x₂ ^ 3*y₂ ^ 2 - 5*A ^ 2*r ^ 2*x₁ ^ 7 + 38*A ^ 2*r ^ 2*x₁ ^ 6*x₂ - 90*A ^ 2*r ^ 2*x₁ ^ 5*x₂ ^ 2 + 90*A ^ 2*r ^ 2*x₁ ^ 4*x₂ ^ 3 + 10*A ^ 2*r ^ 2*x₁ ^ 4*y₁*y₂ - 5*A ^ 2*r ^ 2*x₁ ^ 4*y₂ ^ 2 - 33*A ^ 2*r ^ 2*x₁ ^ 3*x₂ ^ 4 - 28*A ^ 2*r ^ 2*x₁ ^ 3*x₂*y₁*y₂ + 14*A ^ 2*r ^ 2*x₁ ^ 3*x₂*y₂ ^ 2 - 6*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 5 + 24*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 12*A ^ 2*r ^ 2*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 + 8*A ^ 2*r ^ 2*x₁*x₂ ^ 6 - 4*A ^ 2*r ^ 2*x₁*x₂ ^ 3*y₁*y₂ + 2*A ^ 2*r ^ 2*x₁*x₂ ^ 3*y₂ ^ 2 - 2*A ^ 2*r ^ 2*x₂ ^ 7 - 2*A ^ 2*r ^ 2*x₂ ^ 4*y₁*y₂ + A ^ 2*r ^ 2*x₂ ^ 4*y₂ ^ 2 + A ^ 2*r*x₁ ^ 8 - 10*A ^ 2*r*x₁ ^ 7*x₂ + 21*A ^ 2*r*x₁ ^ 6*x₂ ^ 2 - 6*A ^ 2*r*x₁ ^ 5*x₂ ^ 3 - 8*A ^ 2*r*x₁ ^ 5*y₁*y₂ + 4*A ^ 2*r*x₁ ^ 5*y₂ ^ 2 - 27*A ^ 2*r*x₁ ^ 4*x₂ ^ 4 + 20*A ^ 2*r*x₁ ^ 4*x₂*y₁*y₂ - 10*A ^ 2*r*x₁ ^ 4*x₂*y₂ ^ 2 + 36*A ^ 2*r*x₁ ^ 3*x₂ ^ 5 - 12*A ^ 2*r*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 6*A ^ 2*r*x₁ ^ 3*x₂ ^ 2*y₂ ^ 2 - 19*A ^ 2*r*x₁ ^ 2*x₂ ^ 6 - 4*A ^ 2*r*x₁ ^ 2*x₂ ^ 3*y₁*y₂ + 2*A ^ 2*r*x₁ ^ 2*x₂ ^ 3*y₂ ^ 2 + 4*A ^ 2*r*x₁*x₂ ^ 7 + 4*A ^ 2*r*x₁*x₂ ^ 4*y₁*y₂ - 2*A ^ 2*r*x₁*x₂ ^ 4*y₂ ^ 2 - A ^ 2*x₁ ^ 8*x₂ + 6*A ^ 2*x₁ ^ 7*x₂ ^ 2 - 16*A ^ 2*x₁ ^ 6*x₂ ^ 3 + 2*A ^ 2*x₁ ^ 6*y₁*y₂ - A ^ 2*x₁ ^ 6*y₂ ^ 2 + 24*A ^ 2*x₁ ^ 5*x₂ ^ 4 - 4*A ^ 2*x₁ ^ 5*x₂*y₁*y₂ + 2*A ^ 2*x₁ ^ 5*x₂*y₂ ^ 2 - 21*A ^ 2*x₁ ^ 4*x₂ ^ 5 + 10*A ^ 2*x₁ ^ 3*x₂ ^ 6 + 4*A ^ 2*x₁ ^ 3*x₂ ^ 3*y₁*y₂ - 2*A ^ 2*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 - 2*A ^ 2*x₁ ^ 2*x₂ ^ 7 - 2*A ^ 2*x₁ ^ 2*x₂ ^ 4*y₁*y₂ + A ^ 2*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 - 22*A*r ^ 8*x₁ ^ 3 + 66*A*r ^ 8*x₁ ^ 2*x₂ - 66*A*r ^ 8*x₁*x₂ ^ 2 + 22*A*r ^ 8*x₂ ^ 3 + 55*A*r ^ 7*x₁ ^ 4 - 158*A*r ^ 7*x₁ ^ 3*x₂ + 144*A*r ^ 7*x₁ ^ 2*x₂ ^ 2 - 34*A*r ^ 7*x₁*x₂ ^ 3 - 7*A*r ^ 7*x₂ ^ 4 - 48*A*r ^ 6*x₁ ^ 5 + 173*A*r ^ 6*x₁ ^ 4*x₂ - 246*A*r ^ 6*x₁ ^ 3*x₂ ^ 2 + 180*A*r ^ 6*x₁ ^ 2*x₂ ^ 3 - 74*A*r ^ 6*x₁*x₂ ^ 4 + 15*A*r ^ 6*x₂ ^ 5 + 24*A*r ^ 5*x₁ ^ 6 - 180*A*r ^ 5*x₁ ^ 5*x₂ + 441*A*r ^ 5*x₁ ^ 4*x₂ ^ 2 - 490*A*r ^ 5*x₁ ^ 3*x₂ ^ 3 - 20*A*r ^ 5*x₁ ^ 3*y₁*y₂ + 10*A*r ^ 5*x₁ ^ 3*y₂ ^ 2 + 264*A*r ^ 5*x₁ ^ 2*x₂ ^ 4 + 60*A*r ^ 5*x₁ ^ 2*x₂*y₁*y₂ - 30*A*r ^ 5*x₁ ^ 2*x₂*y₂ ^ 2 - 66*A*r ^ 5*x₁*x₂ ^ 5 - 60*A*r ^ 5*x₁*x₂ ^ 2*y₁*y₂ + 30*A*r ^ 5*x₁*x₂ ^ 2*y₂ ^ 2 + 7*A*r ^ 5*x₂ ^ 6 + 20*A*r ^ 5*x₂ ^ 3*y₁*y₂ - 10*A*r ^ 5*x₂ ^ 3*y₂ ^ 2 - 10*A*r ^ 4*x₁ ^ 7 + 124*A*r ^ 4*x₁ ^ 6*x₂ - 348*A*r ^ 4*x₁ ^ 5*x₂ ^ 2 + 399*A*r ^ 4*x₁ ^ 4*x₂ ^ 3 + 46*A*r ^ 4*x₁ ^ 4*y₁*y₂ - 24*A*r ^ 4*x₁ ^ 4*y₂ ^ 2 - 190*A*r ^ 4*x₁ ^ 3*x₂ ^ 4 - 132*A*r ^ 4*x₁ ^ 3*x₂*y₁*y₂ + 70*A*r ^ 4*x₁ ^ 3*x₂*y₂ ^ 2 + 6*A*r ^ 4*x₁ ^ 2*x₂ ^ 5 + 120*A*r ^ 4*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 66*A*r ^ 4*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 + 28*A*r ^ 4*x₁*x₂ ^ 6 - 28*A*r ^ 4*x₁*x₂ ^ 3*y₁*y₂ + 18*A*r ^ 4*x₁*x₂ ^ 3*y₂ ^ 2 - 9*A*r ^ 4*x₂ ^ 7 - 6*A*r ^ 4*x₂ ^ 4*y₁*y₂ + 2*A*r ^ 4*x₂ ^ 4*y₂ ^ 2 - 3*A*r ^ 3*x₁ ^ 8 - 14*A*r ^ 3*x₁ ^ 7*x₂ + 62*A*r ^ 3*x₁ ^ 6*x₂ ^ 2 - 54*A*r ^ 3*x₁ ^ 5*x₂ ^ 3 - 32*A*r ^ 3*x₁ ^ 5*y₁*y₂ + 18*A*r ^ 3*x₁ ^ 5*y₂ ^ 2 - 42*A*r ^ 3*x₁ ^ 4*x₂ ^ 4 + 96*A*r ^ 3*x₁ ^ 4*x₂*y₁*y₂ - 54*A*r ^ 3*x₁ ^ 4*x₂*y₂ ^ 2 + 104*A*r ^ 3*x₁ ^ 3*x₂ ^ 5 - 96*A*r ^ 3*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 52*A*r ^ 3*x₁ ^ 3*x₂ ^ 2*y₂ ^ 2 - 72*A*r ^ 3*x₁ ^ 2*x₂ ^ 6 + 32*A*r ^ 3*x₁ ^ 2*x₂ ^ 3*y₁*y₂ - 12*A*r ^ 3*x₁ ^ 2*x₂ ^ 3*y₂ ^ 2 + 20*A*r ^ 3*x₁*x₂ ^ 7 - 6*A*r ^ 3*x₁*x₂ ^ 4*y₂ ^ 2 - A*r ^ 3*x₂ ^ 8 + 2*A*r ^ 3*x₂ ^ 5*y₂ ^ 2 + 4*A*r ^ 2*x₁ ^ 9 - 3*A*r ^ 2*x₁ ^ 8*x₂ - 12*A*r ^ 2*x₁ ^ 7*x₂ ^ 2 + 6*A*r ^ 2*x₁ ^ 6*x₂ ^ 3 + 6*A*r ^ 2*x₁ ^ 6*y₁*y₂ - 4*A*r ^ 2*x₁ ^ 6*y₂ ^ 2 + 33*A*r ^ 2*x₁ ^ 5*x₂ ^ 4 - 36*A*r ^ 2*x₁ ^ 5*x₂*y₁*y₂ + 18*A*r ^ 2*x₁ ^ 5*x₂*y₂ ^ 2 - 57*A*r ^ 2*x₁ ^ 4*x₂ ^ 5 + 66*A*r ^ 2*x₁ ^ 4*x₂ ^ 2*y₁*y₂ - 24*A*r ^ 2*x₁ ^ 4*x₂ ^ 2*y₂ ^ 2 + 44*A*r ^ 2*x₁ ^ 3*x₂ ^ 6 - 40*A*r ^ 2*x₁ ^ 3*x₂ ^ 3*y₁*y₂ + 4*A*r ^ 2*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 - 18*A*r ^ 2*x₁ ^ 2*x₂ ^ 7 - 6*A*r ^ 2*x₁ ^ 2*x₂ ^ 4*y₁*y₂ + 12*A*r ^ 2*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 + 3*A*r ^ 2*x₁*x₂ ^ 8 + 12*A*r ^ 2*x₁*x₂ ^ 5*y₁*y₂ - 6*A*r ^ 2*x₁*x₂ ^ 5*y₂ ^ 2 - 2*A*r ^ 2*x₂ ^ 6*y₁*y₂ - 8*A*r*x₁ ^ 9*x₂ + 21*A*r*x₁ ^ 8*x₂ ^ 2 - 14*A*r*x₁ ^ 7*x₂ ^ 3 - 7*A*r*x₁ ^ 6*x₂ ^ 4 + 12*A*r*x₁ ^ 6*x₂*y₁*y₂ - 4*A*r*x₁ ^ 6*x₂*y₂ ^ 2 + 18*A*r*x₁ ^ 5*x₂ ^ 5 - 24*A*r*x₁ ^ 5*x₂ ^ 2*y₁*y₂ + 6*A*r*x₁ ^ 5*x₂ ^ 2*y₂ ^ 2 - 19*A*r*x₁ ^ 4*x₂ ^ 6 - 4*A*r*x₁ ^ 4*x₂ ^ 3*y₁*y₂ + 6*A*r*x₁ ^ 4*x₂ ^ 3*y₂ ^ 2 + 12*A*r*x₁ ^ 3*x₂ ^ 7 + 36*A*r*x₁ ^ 3*x₂ ^ 4*y₁*y₂ - 14*A*r*x₁ ^ 3*x₂ ^ 4*y₂ ^ 2 - 3*A*r*x₁ ^ 2*x₂ ^ 8 - 24*A*r*x₁ ^ 2*x₂ ^ 5*y₁*y₂ + 6*A*r*x₁ ^ 2*x₂ ^ 5*y₂ ^ 2 + 4*A*r*x₁*x₂ ^ 6*y₁*y₂ + 4*A*x₁ ^ 9*x₂ ^ 2 - 15*A*x₁ ^ 8*x₂ ^ 3 + 23*A*x₁ ^ 7*x₂ ^ 4 - 20*A*x₁ ^ 6*x₂ ^ 5 - 6*A*x₁ ^ 6*x₂ ^ 2*y₁*y₂ + 2*A*x₁ ^ 6*x₂ ^ 2*y₂ ^ 2 + 12*A*x₁ ^ 5*x₂ ^ 6 + 20*A*x₁ ^ 5*x₂ ^ 3*y₁*y₂ - 6*A*x₁ ^ 5*x₂ ^ 3*y₂ ^ 2 - 5*A*x₁ ^ 4*x₂ ^ 7 - 24*A*x₁ ^ 4*x₂ ^ 4*y₁*y₂ + 6*A*x₁ ^ 4*x₂ ^ 4*y₂ ^ 2 + A*x₁ ^ 3*x₂ ^ 8 + 12*A*x₁ ^ 3*x₂ ^ 5*y₁*y₂ - 2*A*x₁ ^ 3*x₂ ^ 5*y₂ ^ 2 - 2*A*x₁ ^ 2*x₂ ^ 6*y₁*y₂ - 12*r ^ 10*x₁ ^ 3 + 36*r ^ 10*x₁ ^ 2*x₂ - 36*r ^ 10*x₁*x₂ ^ 2 + 12*r ^ 10*x₂ ^ 3 + 21*r ^ 9*x₁ ^ 4 - 60*r ^ 9*x₁ ^ 3*x₂ + 54*r ^ 9*x₁ ^ 2*x₂ ^ 2 - 12*r ^ 9*x₁*x₂ ^ 3 - 3*r ^ 9*x₂ ^ 4 - 18*r ^ 8*x₁ ^ 5 + 96*r ^ 8*x₁ ^ 4*x₂ - 198*r ^ 8*x₁ ^ 3*x₂ ^ 2 + 198*r ^ 8*x₁ ^ 2*x₂ ^ 3 - 96*r ^ 8*x₁*x₂ ^ 4 + 18*r ^ 8*x₂ ^ 5 + 27*r ^ 7*x₁ ^ 6 - 180*r ^ 7*x₁ ^ 5*x₂ + 432*r ^ 7*x₁ ^ 4*x₂ ^ 2 - 498*r ^ 7*x₁ ^ 3*x₂ ^ 3 - 24*r ^ 7*x₁ ^ 3*y₁*y₂ + 12*r ^ 7*x₁ ^ 3*y₂ ^ 2 + 297*r ^ 7*x₁ ^ 2*x₂ ^ 4 + 72*r ^ 7*x₁ ^ 2*x₂*y₁*y₂ - 36*r ^ 7*x₁ ^ 2*x₂*y₂ ^ 2 - 90*r ^ 7*x₁*x₂ ^ 5 - 72*r ^ 7*x₁*x₂ ^ 2*y₁*y₂ + 36*r ^ 7*x₁*x₂ ^ 2*y₂ ^ 2 + 12*r ^ 7*x₂ ^ 6 + 24*r ^ 7*x₂ ^ 3*y₁*y₂ - 12*r ^ 7*x₂ ^ 3*y₂ ^ 2 - 12*r ^ 6*x₁ ^ 7 + 84*r ^ 6*x₁ ^ 6*x₂ - 234*r ^ 6*x₁ ^ 5*x₂ ^ 2 + 333*r ^ 6*x₁ ^ 4*x₂ ^ 3 + 48*r ^ 6*x₁ ^ 4*y₁*y₂ - 27*r ^ 6*x₁ ^ 4*y₂ ^ 2 - 246*r ^ 6*x₁ ^ 3*x₂ ^ 4 - 144*r ^ 6*x₁ ^ 3*x₂*y₁*y₂ + 84*r ^ 6*x₁ ^ 3*x₂*y₂ ^ 2 + 72*r ^ 6*x₁ ^ 2*x₂ ^ 5 + 144*r ^ 6*x₁ ^ 2*x₂ ^ 2*y₁*y₂ - 90*r ^ 6*x₁ ^ 2*x₂ ^ 2*y₂ ^ 2 + 12*r ^ 6*x₁*x₂ ^ 6 - 48*r ^ 6*x₁*x₂ ^ 3*y₁*y₂ + 36*r ^ 6*x₁*x₂ ^ 3*y₂ ^ 2 - 9*r ^ 6*x₂ ^ 7 - 3*r ^ 6*x₂ ^ 4*y₂ ^ 2 - 18*r ^ 5*x₁ ^ 8 + 48*r ^ 5*x₁ ^ 7*x₂ - 3*r ^ 5*x₁ ^ 6*x₂ ^ 2 - 108*r ^ 5*x₁ ^ 5*x₂ ^ 3 - 24*r ^ 5*x₁ ^ 5*y₁*y₂ + 18*r ^ 5*x₁ ^ 5*y₂ ^ 2 + 117*r ^ 5*x₁ ^ 4*x₂ ^ 4 + 108*r ^ 5*x₁ ^ 4*x₂*y₁*y₂ - 72*r ^ 5*x₁ ^ 4*x₂*y₂ ^ 2 - 12*r ^ 5*x₁ ^ 3*x₂ ^ 5 - 180*r ^ 5*x₁ ^ 3*x₂ ^ 2*y₁*y₂ + 102*r ^ 5*x₁ ^ 3*x₂ ^ 2*y₂ ^ 2 - 45*r ^ 5*x₁ ^ 2*x₂ ^ 6 + 132*r ^ 5*x₁ ^ 2*x₂ ^ 3*y₁*y₂ - 54*r ^ 5*x₁ ^ 2*x₂ ^ 3*y₂ ^ 2 + 24*r ^ 5*x₁*x₂ ^ 7 - 36*r ^ 5*x₁*x₂ ^ 4*y₁*y₂ - 3*r ^ 5*x₂ ^ 8 + 6*r ^ 5*x₂ ^ 5*y₂ ^ 2 + 12*r ^ 4*x₁ ^ 9 - 90*r ^ 4*x₁ ^ 7*x₂ ^ 2 + 162*r ^ 4*x₁ ^ 6*x₂ ^ 3 - 3*r ^ 4*x₁ ^ 6*y₂ ^ 2 - 117*r ^ 4*x₁ ^ 5*x₂ ^ 4 - 72*r ^ 4*x₁ ^ 5*x₂*y₁*y₂ + 36*r ^ 4*x₁ ^ 5*x₂*y₂ ^ 2 + 18*r ^ 4*x₁ ^ 4*x₂ ^ 5 + 198*r ^ 4*x₁ ^ 4*x₂ ^ 2*y₁*y₂ - 72*r ^ 4*x₁ ^ 4*x₂ ^ 2*y₂ ^ 2 + 42*r ^ 4*x₁ ^ 3*x₂ ^ 6 - 156*r ^ 4*x₁ ^ 3*x₂ ^ 3*y₁*y₂ + 30*r ^ 4*x₁ ^ 3*x₂ ^ 3*y₂ ^ 2 - 36*r ^ 4*x₁ ^ 2*x₂ ^ 7 + 27*r ^ 4*x₁ ^ 2*x₂ ^ 4*y₂ ^ 2 + 9*r ^ 4*x₁*x₂ ^ 8 + 36*r ^ 4*x₁*x₂ ^ 5*y₁*y₂ - 18*r ^ 4*x₁*x₂ ^ 5*y₂ ^ 2 - 6*r ^ 4*x₂ ^ 6*y₁*y₂ - 24*r ^ 3*x₁ ^ 9*x₂ + 63*r ^ 3*x₁ ^ 8*x₂ ^ 2 - 42*r ^ 3*x₁ ^ 7*x₂ ^ 3 - 21*r ^ 3*x₁ ^ 6*x₂ ^ 4 + 36*r ^ 3*x₁ ^ 6*x₂*y₁*y₂ - 12*r ^ 3*x₁ ^ 6*x₂*y₂ ^ 2 + 54*r ^ 3*x₁ ^ 5*x₂ ^ 5 - 72*r ^ 3*x₁ ^ 5*x₂ ^ 2*y₁*y₂ + 18*r ^ 3*x₁ ^ 5*x₂ ^ 2*y₂ ^ 2 - 57*r ^ 3*x₁ ^ 4*x₂ ^ 6 - 12*r ^ 3*x₁ ^ 4*x₂ ^ 3*y₁*y₂ + 18*r ^ 3*x₁ ^ 4*x₂ ^ 3*y₂ ^ 2 + 36*r ^ 3*x₁ ^ 3*x₂ ^ 7 + 108*r ^ 3*x₁ ^ 3*x₂ ^ 4*y₁*y₂ - 42*r ^ 3*x₁ ^ 3*x₂ ^ 4*y₂ ^ 2 - 9*r ^ 3*x₁ ^ 2*x₂ ^ 8 - 72*r ^ 3*x₁ ^ 2*x₂ ^ 5*y₁*y₂ + 18*r ^ 3*x₁ ^ 2*x₂ ^ 5*y₂ ^ 2 + 12*r ^ 3*x₁*x₂ ^ 6*y₁*y₂ + 12*r ^ 2*x₁ ^ 9*x₂ ^ 2 - 45*r ^ 2*x₁ ^ 8*x₂ ^ 3 + 69*r ^ 2*x₁ ^ 7*x₂ ^ 4 - 60*r ^ 2*x₁ ^ 6*x₂ ^ 5 - 18*r ^ 2*x₁ ^ 6*x₂ ^ 2*y₁*y₂ + 6*r ^ 2*x₁ ^ 6*x₂ ^ 2*y₂ ^ 2 + 36*r ^ 2*x₁ ^ 5*x₂ ^ 6 + 60*r ^ 2*x₁ ^ 5*x₂ ^ 3*y₁*y₂ - 18*r ^ 2*x₁ ^ 5*x₂ ^ 3*y₂ ^ 2 - 15*r ^ 2*x₁ ^ 4*x₂ ^ 7 - 72*r ^ 2*x₁ ^ 4*x₂ ^ 4*y₁*y₂ + 18*r ^ 2*x₁ ^ 4*x₂ ^ 4*y₂ ^ 2 + 3*r ^ 2*x₁ ^ 3*x₂ ^ 8 + 36*r ^ 2*x₁ ^ 3*x₂ ^ 5*y₁*y₂ - 6*r ^ 2*x₁ ^ 3*x₂ ^ 5*y₂ ^ 2 - 6*r ^ 2*x₁ ^ 2*x₂ ^ 6*y₁*y₂)
                      * hcurve₂'
                · -- Y-coordinate identity
                  simp only [hx₃_eq, addY, WeierstrassCurve.Affine.negAddY, negY, addX, shortWS,
                    veluQuotCurve, WeierstrassCurve.Affine.slope_of_X_ne hX_ne,
                    mul_zero, zero_mul, sub_zero, add_zero, zero_add]
                  rw [WeierstrassCurve.Affine.slope_of_X_ne hx₁x₂]
                  unfold veluT
                  have hx₃r_poly : (y₁ - y₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
                      x₂ * (x₁ - x₂) ^ 2 - (x₁ - x₂) ^ 2 * r ≠ 0 := by
                    intro h; apply hx₃r; rw [hx₃_eq]
                    have : ℓ ^ 2 = x₁ + x₂ + r := by
                      rw [hℓ, div_pow]; field_simp; nlinarith
                    linarith
                  have hX_den : (x₂ - r) * (x₁ * (x₁ - r) + (3 * r ^ 2 + A)) -
                      (x₁ - r) * (x₂ * (x₂ - r) + (3 * r ^ 2 + A)) ≠ 0 := by
                    intro h
                    have : (x₁ - x₂) * ((x₁ - r) * (x₂ - r) -
                        (3 * r ^ 2 + A)) = 0 := by linear_combination h
                    rcases mul_eq_zero.mp this with h1 | h1
                    · exact absurd h1 hd
                    · exact absurd (by linarith :
                        (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A) hat
                  have hcurve₁' : y₁ ^ 2 - x₁ ^ 3 - A * x₁ + r ^ 3 + A * r = 0 := by
                    linarith [hcurve₁, htors]
                  have hcurve₂' : y₂ ^ 2 - x₂ ^ 3 - A * x₂ + r ^ 3 + A * r = 0 := by
                    linarith [hcurve₂, htors]
                  sorry

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
