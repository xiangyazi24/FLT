import Mathlib

/-!
# Real topology route, S3: the algebraic component character

This file starts the purely algebraic part of the real-topology route.  For a
short real Weierstrass model `y^2 = x^3 + A*x^2 + B*x`, and a chosen branch
point `e`, the component character is represented additively as a map to
`ZMod 2`: an affine point contributes `1` exactly when `x < e`, while the point
at infinity and the branch point itself contribute `0`.

The multiplicative `{±1}` character can later be recovered by `b ↦ (-1)^b`.
Using `ZMod 2` is the convenient form for a homomorphism out of the additive
point group.
-/

open scoped WeierstrassCurve.Affine
open Polynomial

namespace MazurProof.RealTopology

/-- Short real Weierstrass model `y^2 = x^3 + A*x^2 + B*x`. -/
def shortW (A B : ℝ) : WeierstrassCurve ℝ :=
  { a₁ := 0
    a₂ := A
    a₃ := 0
    a₄ := B
    a₆ := 0 }

/-- The cubic on the right-hand side of `shortW`. -/
def shortCubic (A B x : ℝ) : ℝ :=
  x ^ 3 + A * x ^ 2 + B * x

/-- Formal derivative of `shortCubic A B`. -/
def shortCubicDeriv (A B x : ℝ) : ℝ :=
  3 * x ^ 2 + 2 * A * x + B

@[simp] theorem shortW_equation_iff {A B x y : ℝ} :
    WeierstrassCurve.Affine.Equation (shortW A B) x y ↔
      y ^ 2 = shortCubic A B x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortW, shortCubic]

@[simp] theorem shortW_negY (A B x y : ℝ) :
    WeierstrassCurve.Affine.negY (shortW A B) x y = -y := by
  simp [shortW, WeierstrassCurve.Affine.negY]

@[simp] theorem shortW_addX (A B x₁ x₂ ell : ℝ) :
    WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂ ell =
      ell ^ 2 - A - x₁ - x₂ := by
  simp [shortW, WeierstrassCurve.Affine.addX]

/-- Additive `ZMod 2` side bit: `1` means strictly left of `e`. -/
noncomputable def sideBit (e x : ℝ) : ZMod 2 :=
  if x < e then 1 else 0

@[simp] theorem sideBit_of_lt {e x : ℝ} (h : x < e) : sideBit e x = 1 := by
  simp [sideBit, h]

@[simp] theorem sideBit_of_not_lt {e x : ℝ} (h : ¬ x < e) : sideBit e x = 0 := by
  simp [sideBit, h]

theorem sideBit_eq_of_sub_eq_pos_div
    {e x x' d : ℝ} (hd : 0 < d) (hx : x ≠ e)
    (hsub : x' - e = d / (x - e)) :
    sideBit e x' = sideBit e x := by
  by_cases hlt : x < e
  · have hden_neg : x - e < 0 := sub_neg.mpr hlt
    have hdiv_neg : d / (x - e) < 0 := div_neg_of_pos_of_neg hd hden_neg
    have hx'lt : x' < e := by linarith
    simp [sideBit, hlt, hx'lt]
  · have hxgt : e < x := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hx)
    have hden_pos : 0 < x - e := sub_pos.mpr hxgt
    have hdiv_pos : 0 < d / (x - e) := div_pos hd hden_pos
    have hx'nlt : ¬ x' < e := by linarith
    simp [sideBit, hlt, hx'nlt]

set_option linter.flexible false in
theorem sideBit_add_eq_zero_of_mul_pos
    {e x₁ x₂ : ℝ} (hprod : 0 < (x₁ - e) * (x₂ - e)) :
    sideBit e x₁ + sideBit e x₂ = 0 := by
  by_cases h₁ : x₁ < e
  · by_cases h₂ : x₂ < e
    · simp [sideBit, h₁, h₂]
      decide
    · have hx₁neg : x₁ - e < 0 := sub_neg.mpr h₁
      have hx₂nonneg : 0 ≤ x₂ - e := sub_nonneg.mpr (not_lt.mp h₂)
      have hnonpos : (x₁ - e) * (x₂ - e) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx₁neg) hx₂nonneg
      linarith
  · by_cases h₂ : x₂ < e
    · have hx₁nonneg : 0 ≤ x₁ - e := sub_nonneg.mpr (not_lt.mp h₁)
      have hx₂neg : x₂ - e < 0 := sub_neg.mpr h₂
      have hnonpos : (x₁ - e) * (x₂ - e) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hx₁nonneg (le_of_lt hx₂neg)
      linarith
    · simp [sideBit, h₁, h₂]

/-- The point-level S3 character in additive `ZMod 2` form. -/
noncomputable def componentBit {A B : ℝ} (e : ℝ) :
    WeierstrassCurve.Affine.Point (shortW A B) → ZMod 2
  | 0 => 0
  | WeierstrassCurve.Affine.Point.some x _ _ => sideBit e x

@[simp] theorem componentBit_zero {A B e : ℝ} :
    componentBit (A := A) (B := B) e 0 = 0 :=
  rfl

@[simp] theorem componentBit_some {A B e x y : ℝ}
    (h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y) :
    componentBit e (WeierstrassCurve.Affine.Point.some x y h) = sideBit e x :=
  rfl

@[simp] theorem componentBit_neg {A B e : ℝ}
    (P : WeierstrassCurve.Affine.Point (shortW A B)) :
    componentBit e (-P) = componentBit e P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp [componentBit, WeierstrassCurve.Affine.Point.neg_some]

private lemma pos_of_not_neg_of_ne {a : ℝ} (ha_nonneg : ¬ a < 0) (ha_ne : a ≠ 0) :
    0 < a := by
  exact lt_of_le_of_ne (not_lt.mp ha_nonneg) (Ne.symm ha_ne)

set_option linter.flexible false in
/--
If three nonzero real factors have nonnegative product, then the number of
negative factors is even.  This is the algebraic parity extraction behind S3.
-/
theorem sideBit_zero_add_zero_add_zero_of_mul_nonneg
    {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hprod : 0 ≤ a * b * c) :
    ((if a < 0 then 1 else 0) +
      (if b < 0 then 1 else 0) +
      (if c < 0 then 1 else 0) : ZMod 2) = 0 := by
  by_cases ha_neg : a < 0
  · by_cases hb_neg : b < 0
    · by_cases hc_neg : c < 0
      · simp [ha_neg, hb_neg, hc_neg]
        have hab_pos : 0 < a * b := mul_pos_of_neg_of_neg ha_neg hb_neg
        have habc_neg : a * b * c < 0 := mul_neg_of_pos_of_neg hab_pos hc_neg
        linarith
      · simp [ha_neg, hb_neg, hc_neg]
        decide
    · by_cases hc_neg : c < 0
      · simp [ha_neg, hb_neg, hc_neg]
        decide
      · simp [ha_neg, hb_neg, hc_neg]
        have hb_pos : 0 < b := pos_of_not_neg_of_ne hb_neg hb
        have hc_pos : 0 < c := pos_of_not_neg_of_ne hc_neg hc
        have hab_neg : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
        have habc_neg : a * b * c < 0 := mul_neg_of_neg_of_pos hab_neg hc_pos
        linarith
  · by_cases hb_neg : b < 0
    · by_cases hc_neg : c < 0
      · simp [ha_neg, hb_neg, hc_neg]
        decide
      · simp [ha_neg, hb_neg, hc_neg]
        have ha_pos : 0 < a := pos_of_not_neg_of_ne ha_neg ha
        have hc_pos : 0 < c := pos_of_not_neg_of_ne hc_neg hc
        have hab_neg : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
        have habc_neg : a * b * c < 0 := mul_neg_of_neg_of_pos hab_neg hc_pos
        linarith
    · by_cases hc_neg : c < 0
      · simp [ha_neg, hb_neg, hc_neg]
        have ha_pos : 0 < a := pos_of_not_neg_of_ne ha_neg ha
        have hb_pos : 0 < b := pos_of_not_neg_of_ne hb_neg hb
        have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
        have habc_neg : a * b * c < 0 := mul_neg_of_pos_of_neg hab_pos hc_neg
        linarith
      · simp [ha_neg, hb_neg, hc_neg]

theorem sideBit_add_add_eq_zero_of_product_square
    {e x₁ x₂ x₃ s : ℝ}
    (h₁ : x₁ ≠ e) (h₂ : x₂ ≠ e) (h₃ : x₃ ≠ e)
    (hprod : (x₁ - e) * (x₂ - e) * (x₃ - e) = s ^ 2) :
    sideBit e x₁ + sideBit e x₂ + sideBit e x₃ = 0 := by
  have hnonneg : 0 ≤ (x₁ - e) * (x₂ - e) * (x₃ - e) := by
    rw [hprod]
    exact sq_nonneg s
  have hpar := sideBit_zero_add_zero_add_zero_of_mul_nonneg
    (a := x₁ - e) (b := x₂ - e) (c := x₃ - e)
    (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂) (sub_ne_zero.mpr h₃) hnonneg
  simpa [sideBit, sub_lt_zero] using hpar

set_option linter.flexible false in
/--
Key S3 algebra identity for a non-vertical secant/tangent.  Here
`x₃ = x(P + Q)` and `ell*e + nu` is the line value at the branch point `e`.
-/
theorem shortW_line_product_identity
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂)) :
    let ell := WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂
    let x₃ := WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂ ell
    let nu := y₁ - ell * x₁
    (x₁ - e) * (x₂ - e) * (x₃ - e) = (ell * e + nu) ^ 2 := by
  classical
  let ell := WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂
  let x₃ := WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂ ell
  let nu := y₁ - ell * x₁
  have hpoly := WeierstrassCurve.Affine.addPolynomial_slope
    (W := shortW A B) h₁.1 h₂.1 hxy
  have heval := congrArg (fun p : ℝ[X] => p.eval e) hpoly
  simp [shortW, WeierstrassCurve.Affine.addPolynomial,
    WeierstrassCurve.Affine.linePolynomial, WeierstrassCurve.Affine.polynomial] at heval
  have hroot' : e ^ 3 + A * e ^ 2 + B * e = 0 := by
    simpa [shortCubic] using hroot
  rw [hroot'] at heval
  simp [shortW] at heval ⊢
  ring_nf at heval ⊢
  exact heval.symm

set_option linter.flexible false in
/--
If `T=(e,0)` is a branch point and `Q=(x,y)` with `x≠e`, then the
`x`-coordinate of `T+Q` satisfies
`x(T+Q)-e = f'(e)/(x-e)`.
-/
theorem shortW_branch_addX_sub_eq_deriv_div
    {A B e x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hcurve : y ^ 2 = shortCubic A B x)
    (hx : x ≠ e) :
    let ell := WeierstrassCurve.Affine.slope (shortW A B) e x 0 y
    let x₃ := WeierstrassCurve.Affine.addX (shortW A B) e x ell
    x₃ - e = shortCubicDeriv A B e / (x - e) := by
  classical
  rw [WeierstrassCurve.Affine.slope_of_X_ne (W := shortW A B)
    (x₁ := e) (x₂ := x) (y₁ := 0) (y₂ := y) (by exact fun h => hx h.symm)]
  simp [shortW, WeierstrassCurve.Affine.addX, shortCubic, shortCubicDeriv] at hroot hcurve ⊢
  field_simp [sub_ne_zero.mpr hx]
  rw [hcurve]
  ring_nf at hroot ⊢
  have hroot_factor : e * (A * e + B + e ^ 2) = 0 := by nlinarith [hroot]
  have hroot_factor_x : e * (x - e) * (A * e + B + e ^ 2) = 0 := by
    calc
      e * (x - e) * (A * e + B + e ^ 2) =
          (x - e) * (e * (A * e + B + e ^ 2)) := by ring
      _ = 0 := by rw [hroot_factor, mul_zero]
  nlinarith [hroot_factor_x]

theorem branch_y_eq_zero
    {A B e x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hx : x = e)
    (h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y) :
    y = 0 := by
  subst x
  have hcurve : y ^ 2 = shortCubic A B e := by
    simpa using (shortW_equation_iff.mp h.1)
  rw [hroot] at hcurve
  exact sq_eq_zero_iff.mp hcurve

/-- Branch case `x(P)=e`: adding the branch point preserves the side bit. -/
theorem componentBit_add_of_left_branch
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂))
    (hx₁ : x₁ = e) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  subst x₁
  have hy₁ : y₁ = 0 := branch_y_eq_zero hroot rfl h₁
  have hx₂ : x₂ ≠ e := by
    intro hx₂e
    have hy₂ : y₂ = 0 := branch_y_eq_zero hroot hx₂e h₂
    apply hxy
    constructor
    · exact hx₂e.symm
    · simp [hy₁, hy₂, hx₂e, shortW, WeierstrassCurve.Affine.negY]
  let ell := WeierstrassCurve.Affine.slope (shortW A B) e x₂ 0 y₂
  let x₃ := WeierstrassCurve.Affine.addX (shortW A B) e x₂ ell
  have hcurve₂ : y₂ ^ 2 = shortCubic A B x₂ := by
    simpa using (shortW_equation_iff.mp h₂.1)
  have hsub : x₃ - e = shortCubicDeriv A B e / (x₂ - e) := by
    simpa [ell, x₃] using
      shortW_branch_addX_sub_eq_deriv_div
        (A := A) (B := B) (e := e) (x := x₂) (y := y₂)
        hroot hcurve₂ hx₂
  have hside : sideBit e x₃ = sideBit e x₂ :=
    sideBit_eq_of_sub_eq_pos_div hderiv hx₂ hsub
  have hadd := WeierstrassCurve.Affine.Point.add_some
    (W := shortW A B) (h₁ := h₁) (h₂ := h₂) hxy
  rw [hadd]
  simpa [componentBit, hy₁, ell, x₃, sideBit] using hside

/-- Branch case `x(Q)=e`, reduced to the left-branch case by commutativity. -/
theorem componentBit_add_of_right_branch
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂))
    (hx₂ : x₂ = e) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  have hxy_swap :
      ¬(x₂ = x₁ ∧ y₂ = WeierstrassCurve.Affine.negY (shortW A B) x₁ y₁) := by
    intro h
    apply hxy
    constructor
    · exact h.1.symm
    · have hy₂ : y₂ = -y₁ := by
        simpa [shortW, WeierstrassCurve.Affine.negY] using h.2
      have hy₁ : y₁ = -y₂ := by linarith
      simpa [shortW, WeierstrassCurve.Affine.negY, h.1] using hy₁
  have hleft := componentBit_add_of_left_branch
    (A := A) (B := B) (e := e) (x₁ := x₂) (x₂ := x₁)
    (y₁ := y₂) (y₂ := y₁) (h₁ := h₂) (h₂ := h₁)
    hroot hderiv hxy_swap hx₂
  calc
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
        = componentBit e
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ +
              WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := by
            rw [add_comm]
    _ = componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) +
          componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := hleft
    _ = componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
          componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
            rw [add_comm]

set_option linter.flexible false in
/--
If the sum has branch `x`-coordinate `e`, then the two input offsets have
product `f'(e)`.
-/
theorem shortW_sum_branch_product_eq_deriv
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂))
    (hx₃ :
      WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
        (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e) :
    (x₁ - e) * (x₂ - e) = shortCubicDeriv A B e := by
  classical
  let ell := WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂
  let x₃ := WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂ ell
  let nu := y₁ - ell * x₁
  have hprod :
      (x₁ - e) * (x₂ - e) * (x₃ - e) = (ell * e + nu) ^ 2 := by
    simpa [ell, x₃, nu] using
      shortW_line_product_identity (A := A) (B := B) (e := e)
        (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
        (h₁ := h₁) (h₂ := h₂) hroot hxy
  have hx₃' : x₃ = e := by
    simpa [x₃, ell] using hx₃
  have hline_sq : (ell * e + nu) ^ 2 = 0 := by
    simpa [hx₃'] using hprod.symm
  have hline0 : ell * e + nu = 0 := sq_eq_zero_iff.mp hline_sq
  have hroots :
      (derivative (WeierstrassCurve.Affine.addPolynomial (shortW A B) x₁ y₁ ell)).eval e =
        -((e - x₁) * (e - x₂)) := by
    have hderiv := WeierstrassCurve.Affine.derivative_addPolynomial_slope
      (W := shortW A B) h₁.1 h₂.1 hxy
    have heval := congrArg (fun p : ℝ[X] => p.eval e) hderiv
    rw [hx₃] at heval
    simpa [ell] using heval
  have hdirect :
      (derivative (WeierstrassCurve.Affine.addPolynomial (shortW A B) x₁ y₁ ell)).eval e =
        2 * ell * (ell * e + nu) - shortCubicDeriv A B e := by
    simp [shortW, WeierstrassCurve.Affine.addPolynomial,
      WeierstrassCurve.Affine.linePolynomial, WeierstrassCurve.Affine.polynomial,
      shortCubicDeriv, nu]
    simp only [derivative_C, derivative_X, derivative_add, derivative_sub, derivative_mul,
      derivative_sq, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_zero, eval_one]
    ring_nf
  have hdirect0 :
      (derivative (WeierstrassCurve.Affine.addPolynomial (shortW A B) x₁ y₁ ell)).eval e =
        -shortCubicDeriv A B e := by
    simpa [hline0] using hdirect
  nlinarith

/-- Branch case `x(P+Q)=e`: the two inputs have the same side bit. -/
theorem componentBit_add_of_sum_branch
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂))
    (hx₃ :
      WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
        (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  have hprod_eq := shortW_sum_branch_product_eq_deriv
    (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
    (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
    hroot hxy hx₃
  have hprod_pos : 0 < (x₁ - e) * (x₂ - e) := by
    rw [hprod_eq]
    exact hderiv
  have hbits : sideBit e x₁ + sideBit e x₂ = 0 :=
    sideBit_add_eq_zero_of_mul_pos hprod_pos
  have hadd := WeierstrassCurve.Affine.Point.add_some
    (W := shortW A B) (h₁ := h₁) (h₂ := h₂) hxy
  rw [hadd]
  change sideBit e
      (WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
        (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂)) =
    sideBit e x₁ + sideBit e x₂
  rw [hx₃]
  simpa [sideBit] using hbits.symm

/-- Generic non-vertical, non-branch case of additivity for the S3 bit. -/
theorem componentBit_add_of_nonvertical_nonbranch
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂))
    (hx₁ : x₁ ≠ e) (hx₂ : x₂ ≠ e)
    (hx₃ :
      WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
        (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) ≠ e) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  classical
  let ell := WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂
  let x₃ := WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂ ell
  let nu := y₁ - ell * x₁
  have hprod :
      (x₁ - e) * (x₂ - e) * (x₃ - e) = (ell * e + nu) ^ 2 := by
    simpa [ell, x₃, nu] using
      shortW_line_product_identity (A := A) (B := B) (e := e)
        (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
        (h₁ := h₁) (h₂ := h₂) hroot hxy
  have hbit : sideBit e x₁ + sideBit e x₂ + sideBit e x₃ = 0 :=
    sideBit_add_add_eq_zero_of_product_square
      (e := e) (x₁ := x₁) (x₂ := x₂) (x₃ := x₃)
      (s := ell * e + nu) hx₁ hx₂ (by simpa [x₃, ell] using hx₃) hprod
  have hadd := WeierstrassCurve.Affine.Point.add_some
    (W := shortW A B) (h₁ := h₁) (h₂ := h₂) hxy
  have hx₃_bit : sideBit e x₃ = sideBit e x₁ + sideBit e x₂ := by
    have hsum : sideBit e x₃ + (sideBit e x₁ + sideBit e x₂) = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hbit
    have hneg : sideBit e x₃ = -(sideBit e x₁ + sideBit e x₂) :=
      eq_neg_of_add_eq_zero_left hsum
    simpa [CharTwo.neg_eq] using hneg
  rw [hadd]
  simpa [componentBit, x₃, ell] using hx₃_bit

/-- Vertical affine case: inverse pairs both have the same side bit. -/
theorem componentBit_add_of_vertical
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hx : x₁ = x₂)
    (hy : y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := shortW A B) hx hy]
  simp [componentBit, hx, CharTwo.add_self_eq_zero]

/-- Full affine additivity of the S3 bit under the positive-derivative branch hypothesis. -/
theorem componentBit_add_of_affine
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  by_cases hvertical :
      x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂
  · exact componentBit_add_of_vertical (e := e) hvertical.1 hvertical.2
  · by_cases hx₁ : x₁ = e
    · exact componentBit_add_of_left_branch
        (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
        (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
        hroot hderiv hvertical hx₁
    · by_cases hx₂ : x₂ = e
      · exact componentBit_add_of_right_branch
          (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
          (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
          hroot hderiv hvertical hx₂
      · by_cases hx₃ :
          WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
            (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e
        · exact componentBit_add_of_sum_branch
            (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
            (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
            hroot hderiv hvertical hx₃
        · exact componentBit_add_of_nonvertical_nonbranch
            (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
            (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
            hroot hvertical hx₁ hx₂ hx₃

/-- Point-level additivity of the S3 bit. -/
theorem componentBit_map_add
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    ∀ P Q : WeierstrassCurve.Affine.Point (shortW A B),
      componentBit e (P + Q) = componentBit e P + componentBit e Q := by
  intro P Q
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y h =>
          simp [componentBit, WeierstrassCurve.Affine.Point.add_def,
            WeierstrassCurve.Affine.Point.add]
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          simp [componentBit, WeierstrassCurve.Affine.Point.add_def,
            WeierstrassCurve.Affine.Point.add]
      | some x₂ y₂ h₂ =>
          exact componentBit_add_of_affine
            (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
            (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
            hroot hderiv

/-- The S3 component character in additive `ZMod 2` form. -/
noncomputable def componentBitHom
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    WeierstrassCurve.Affine.Point (shortW A B) →+ ZMod 2 where
  toFun := componentBit e
  map_zero' := rfl
  map_add' := componentBit_map_add hroot hderiv

/--
Affine additivity reduced to the remaining branch cases.  The non-branch
case is the product-square identity above; the vertical case is immediate.
-/
theorem componentBit_add_of_affine_of_branch_cases
    {A B e x₁ x₂ y₁ y₂ : ℝ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂}
    (hroot : shortCubic A B e = 0)
    (hbranch :
      ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂) →
        (x₁ = e ∨ x₂ = e ∨
          WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
            (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e) →
        componentBit e
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
              WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
          componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
            componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    componentBit e
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
  by_cases hvertical :
      x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂
  · exact componentBit_add_of_vertical (e := e) hvertical.1 hvertical.2
  · by_cases hx₁ : x₁ = e
    · exact hbranch hvertical (Or.inl hx₁)
    · by_cases hx₂ : x₂ = e
      · exact hbranch hvertical (Or.inr <| Or.inl hx₂)
      · by_cases hx₃ :
          WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
            (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e
        · exact hbranch hvertical (Or.inr <| Or.inr hx₃)
        · exact componentBit_add_of_nonvertical_nonbranch
            (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
            (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
            hroot hvertical hx₁ hx₂ hx₃

/--
Point-level additivity reduced to affine branch cases.  This is the S3
assembly target before the three `x=e` branch lemmas are discharged.
-/
theorem componentBit_map_add_of_branch_cases
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hbranch :
      ∀ {x₁ x₂ y₁ y₂ : ℝ}
        {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
        {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂},
        ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂) →
          (x₁ = e ∨ x₂ = e ∨
            WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
              (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e) →
          componentBit e
              (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
            componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
              componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    ∀ P Q : WeierstrassCurve.Affine.Point (shortW A B),
      componentBit e (P + Q) = componentBit e P + componentBit e Q := by
  intro P Q
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y h =>
          simp [componentBit, WeierstrassCurve.Affine.Point.add_def,
            WeierstrassCurve.Affine.Point.add]
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          simp [componentBit, WeierstrassCurve.Affine.Point.add_def,
            WeierstrassCurve.Affine.Point.add]
      | some x₂ y₂ h₂ =>
          exact componentBit_add_of_affine_of_branch_cases
            (A := A) (B := B) (e := e) (x₁ := x₁) (x₂ := x₂)
            (y₁ := y₁) (y₂ := y₂) (h₁ := h₁) (h₂ := h₂)
            hroot (hbranch (h₁ := h₁) (h₂ := h₂))

/-- Conditional additive homomorphism form of the S3 component bit. -/
noncomputable def componentBitHomOfBranchCases
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hbranch :
      ∀ {x₁ x₂ y₁ y₂ : ℝ}
        {h₁ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₁ y₁}
        {h₂ : WeierstrassCurve.Affine.Nonsingular (shortW A B) x₂ y₂},
        ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY (shortW A B) x₂ y₂) →
          (x₁ = e ∨ x₂ = e ∨
            WeierstrassCurve.Affine.addX (shortW A B) x₁ x₂
              (WeierstrassCurve.Affine.slope (shortW A B) x₁ x₂ y₁ y₂) = e) →
          componentBit e
              (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
            componentBit e (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
              componentBit e (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    WeierstrassCurve.Affine.Point (shortW A B) →+ ZMod 2 where
  toFun := componentBit e
  map_zero' := rfl
  map_add' := componentBit_map_add_of_branch_cases hroot hbranch

end MazurProof.RealTopology
