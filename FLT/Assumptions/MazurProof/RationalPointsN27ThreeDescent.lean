import FLT.Assumptions.MazurProof.RationalPointsN18
import FLT.Assumptions.MazurProof.TateOrder18
import FLT.Assumptions.MazurProof.TateOriginDivision
import FLT.Assumptions.MazurProof.RationalPointsN27CM

/-!
# A special three-descent for the order-nine Kubert family

The rational 3-torsion point `T = 3Q` is moved to `(0,0)` with horizontal
tangent.  On the resulting model

`Y^2 + aXY + bY = X^3`,

the `Y`-coordinate is the standard 3-descent function.  The elementary
addition identity proved below shows directly, without divisor theory, that
the `Y`-coordinate of a rational triple is a rational cube.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsN27ThreeDescent

open RationalPointsN18
open TateOriginDivision
open Scratch.TateZ2xZ10Reduction

noncomputable section

private noncomputable def pointCurveEqAddEquiv
    {W₁ W₂ : WeierstrassCurve ℚ} (h : W₁ = W₂) :
    WeierstrassCurve.Affine.Point W₁ ≃+ WeierstrassCurve.Affine.Point W₂ := by
  subst h
  exact AddEquiv.refl _

private theorem pointCurveEqAddEquiv_some
    {W₁ W₂ : WeierstrassCurve ℚ} (h : W₁ = W₂) {x y : ℚ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular W₁ x y}
    {h₂ : WeierstrassCurve.Affine.Nonsingular W₂ x y} :
    pointCurveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y h₁) =
      WeierstrassCurve.Affine.Point.some x y h₂ := by
  subst h
  change WeierstrassCurve.Affine.Point.some x y h₁ =
    WeierstrassCurve.Affine.Point.some x y h₂
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-! ## The elementary addition identity on a curve with rational 3-torsion -/

/-- A Weierstrass model with the rational flex `(0,0)`. -/
def flexCurve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := a
  a₂ := 0
  a₃ := b
  a₄ := 0
  a₆ := 0

@[simp] theorem flexCurve_equation_iff (a b x y : ℚ) :
    WeierstrassCurve.Affine.Equation (flexCurve a b) x y ↔
      y ^ 2 + a * x * y + b * y = x ^ 3 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [flexCurve]

/-- Both affine points above `X=0` on the flex model are killed by three. -/
theorem three_nsmul_flex_x_zero
    (a b y : ℚ) [WeierstrassCurve.IsElliptic (flexCurve a b)]
    (h : WeierstrassCurve.Affine.Nonsingular (flexCurve a b) 0 y) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 y h :
          WeierstrassCurve.Affine.Point (flexCurve a b)) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval (flexCurve a b) h).mpr
  rw [(flexCurve a b).ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, flexCurve]

/-! ## The third multiple of the Tate origin -/

private theorem tate_double_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) b (b * c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]
  ring

private theorem tate_triple_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) c (b - c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]
  ring

def tateDoublePoint
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some b (b * c) (tate_double_nonsingular b c)

def tateTriplePoint
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some c (b - c) (tate_triple_nonsingular b c)

theorem two_nsmul_tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (W b c)] (hb : b ≠ 0) :
    (2 : ℕ) • tateOrigin b c = tateDoublePoint b c := by
  rw [two_nsmul]
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY (W b c) 0 0 := by
    simpa [W, tateNormalFormCurve] using hb.symm
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ +
      WeierstrassCurve.Affine.Point.some 0 0 _ = tateDoublePoint b c
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  unfold tateDoublePoint
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    ring

theorem three_nsmul_tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (W b c)] (hb : b ≠ 0) :
    (3 : ℕ) • tateOrigin b c = tateTriplePoint b c := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
    two_nsmul_tateOrigin b c hb]
  change
    WeierstrassCurve.Affine.Point.some b (b * c) _ +
      WeierstrassCurve.Affine.Point.some 0 0 _ =
        WeierstrassCurve.Affine.Point.some c (b - c) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    field_simp [hb]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    field_simp [hb]
    ring

/-! ## Translating the order-three point in the Kubert family -/

abbrev kubertCurve (t : ℚ) : WeierstrassCurve ℚ :=
  W (kubertB9 t) (kubertC9 t)

def kubertFlexA (t : ℚ) : ℚ := -t ^ 3 + 3 * t ^ 2 - 1

def kubertFlexB (t : ℚ) : ℚ := -t ^ 3 * (t - 1) ^ 3

def kubertFlexChange (t : ℚ) : WeierstrassCurve.VariableChange ℚ :=
  translateToOriginTangent (kubertCurve t) (kubertC9 t)
    (kubertB9 t - kubertC9 t)

theorem kubert_flex_tangent_denominator (t : ℚ) :
    2 * (kubertB9 t - kubertC9 t) +
        (kubertCurve t).a₁ * kubertC9 t + (kubertCurve t).a₃ =
      kubertFlexB t := by
  simp [kubertCurve, W, tateNormalFormCurve, kubertB9, kubertC9,
    kubertFlexB]
  ring

theorem kubert_flex_tangent_slope
    {t : ℚ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    tangentSlope (kubertCurve t) (kubertC9 t)
        (kubertB9 t - kubertC9 t) = t ^ 2 - 1 := by
  have htm : t - 1 ≠ 0 := sub_ne_zero.mpr ht₁
  have hB : kubertFlexB t ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 ht₀)) (pow_ne_zero 3 htm)
  unfold tangentSlope
  rw [kubert_flex_tangent_denominator]
  apply (div_eq_iff hB).2
  simp [kubertCurve, W, tateNormalFormCurve, kubertB9, kubertC9,
    kubertFlexB]
  ring

theorem kubertFlexChange_curve
    {t : ℚ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    kubertFlexChange t • kubertCurve t =
      flexCurve (kubertFlexA t) (kubertFlexB t) := by
  have htm : t - 1 ≠ 0 := sub_ne_zero.mpr ht₁
  have hB : kubertFlexB t ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 ht₀)) (pow_ne_zero 3 htm)
  have hden :
      2 * (kubertB9 t - kubertC9 t) +
          (kubertCurve t).a₁ * kubertC9 t + (kubertCurve t).a₃ ≠ 0 := by
    rw [kubert_flex_tangent_denominator]
    exact hB
  have hpoint : WeierstrassCurve.Affine.Equation (kubertCurve t)
      (kubertC9 t) (kubertB9 t - kubertC9 t) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [kubertCurve, W, tateNormalFormCurve, kubertB9, kubertC9]
    ring
  have hs := kubert_flex_tangent_slope ht₀ ht₁
  ext
  · simp only [kubertFlexChange, translateToOriginTangent_a₁]
    rw [hs]
    simp [kubertCurve, W, tateNormalFormCurve, kubertC9, kubertFlexA,
      flexCurve]
    ring
  · simp only [kubertFlexChange, translateToOriginTangent_a₂]
    rw [hs]
    simp [kubertCurve, W, tateNormalFormCurve, kubertB9, kubertC9,
      flexCurve]
    ring
  · simp only [kubertFlexChange, translateToOriginTangent_a₃]
    simp [kubertCurve, W, tateNormalFormCurve, kubertB9, kubertC9,
      kubertFlexB, flexCurve]
    ring
  · change
      ((translateToOriginTangent (kubertCurve t) (kubertC9 t)
        (kubertB9 t - kubertC9 t)) • kubertCurve t).a₄ = 0
    exact translateToOriginTangent_a₄_eq_zero (kubertCurve t) hden
  · change
      ((translateToOriginTangent (kubertCurve t) (kubertC9 t)
        (kubertB9 t - kubertC9 t)) • kubertCurve t).a₆ = 0
    exact translateToOriginTangent_a₆_eq_zero (kubertCurve t) hpoint
/-- The intercept at `X = 0` of the line used in the affine addition law. -/
def lineIntercept (x y ℓ : ℚ) : ℚ := y - ℓ * x

private theorem second_point_on_addition_line
    {a b x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧
      y₁ = WeierstrassCurve.Affine.negY (flexCurve a b) x₂ y₂)) :
    let ℓ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₂ y₁ y₂
    y₂ = ℓ * (x₂ - x₁) + y₁ := by
  dsimp only
  by_cases hx : x₁ = x₂
  · have hyneg : y₁ ≠ WeierstrassCurve.Affine.negY (flexCurve a b) x₂ y₂ :=
      fun hy ↦ hxy ⟨hx, hy⟩
    have hy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hyneg
    rw [hx, sub_self, mul_zero, zero_add]
    exact hy.symm
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

/-- Cross-multiplied form of the 3-descent addition law.

If `P₃ = P₁ + P₂`, `k` is the intercept of the line through `P₁,P₂`,
then `y₃ k³ = -y₁ y₂ x₃³`. -/
theorem addY_mul_intercept_cube
    {a b x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧
      y₁ = WeierstrassCurve.Affine.negY (flexCurve a b) x₂ y₂)) :
    let ℓ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₂ y₁ y₂
    let x₃ := WeierstrassCurve.Affine.addX (flexCurve a b) x₁ x₂ ℓ
    let y₃ := WeierstrassCurve.Affine.addY (flexCurve a b) x₁ x₂ y₁ ℓ
    let k := lineIntercept x₁ y₁ ℓ
    y₃ * k ^ 3 = -(y₁ * y₂ * x₃ ^ 3) := by
  dsimp only
  let W := flexCurve a b
  let ℓ := WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂
  let x₃ := WeierstrassCurve.Affine.addX W x₁ x₂ ℓ
  let y₃ := WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ
  let k := lineIntercept x₁ y₁ ℓ
  change y₃ * k ^ 3 = -(y₁ * y₂ * x₃ ^ 3)
  have hline : y₂ = ℓ * (x₂ - x₁) + y₁ := by
    exact second_point_on_addition_line h₁ h₂ hxy
  have hpoly := WeierstrassCurve.Affine.addPolynomial_slope h₁ h₂ hxy
  change W.toAffine.addPolynomial x₁ y₁ ℓ =
      -((Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂) *
        (Polynomial.X - Polynomial.C x₃)) at hpoly
  have hyprod : y₁ * y₂ * (ℓ * x₃ + k) = k ^ 3 := by
    by_cases hl : ℓ = 0
    · have hk : k = y₁ := by simp [k, lineIntercept, hl]
      have hy₂ : y₂ = y₁ := by simpa [hl] using hline
      rw [hk, hy₂, hl]
      ring
    · have heval := congrArg (fun p : Polynomial ℚ ↦ p.eval (-k / ℓ)) hpoly
      simp only [Polynomial.eval_neg, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
      have haddEval : (W.toAffine.addPolynomial x₁ y₁ ℓ).eval (-k / ℓ) =
          k ^ 3 / ℓ ^ 3 := by
        simp [WeierstrassCurve.Affine.addPolynomial,
          WeierstrassCurve.Affine.polynomial,
          WeierstrassCurve.Affine.linePolynomial, W, flexCurve, k, lineIntercept]
        field_simp [hl]
        ring
      rw [haddEval] at heval
      field_simp [hl] at heval
      have hfac₁ : -k - ℓ * x₁ = -y₁ := by
        simp [k, lineIntercept]
      have hfac₂ : -k - ℓ * x₂ = -y₂ := by
        rw [hline]
        simp [k, lineIntercept]
        ring
      rw [hfac₁, hfac₂] at heval
      linear_combination -heval
  have hy₃ : y₃ = -(ℓ * x₃ + k) - a * x₃ - b := by
    change
      -(ℓ * (x₃ - x₁) + y₁) - a * x₃ - b =
        -(ℓ * x₃ + k) - a * x₃ - b
    simp [k, lineIntercept]
    ring
  have hcurve₃ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₃ y₃ := by
    exact WeierstrassCurve.Affine.equation_add h₁ h₂ hxy
  rw [flexCurve_equation_iff] at hcurve₃
  have hyline : y₃ * (ℓ * x₃ + k) = -x₃ ^ 3 := by
    linear_combination y₃ * hy₃ - hcurve₃
  linear_combination y₁ * y₂ * hyline - y₃ * hyprod

/-- Applying the addition identity to `P+P` and then `(2P)+P` shows that
the `Y`-coordinate of `3P` is a cube, provided the three coordinates that
occur in the explicit cube root are nonzero. -/
theorem triple_addY_is_cube
    {a b x₁ y₁ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation (flexCurve a b) x₁ y₁)
    (hdouble : y₁ ≠ WeierstrassCurve.Affine.negY (flexCurve a b) x₁ y₁)
    (hadd :
      let ℓ₁ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₁ y₁ y₁
      let x₂ := WeierstrassCurve.Affine.addX (flexCurve a b) x₁ x₁ ℓ₁
      let y₂ := WeierstrassCurve.Affine.addY (flexCurve a b) x₁ x₁ y₁ ℓ₁
      ¬(x₂ = x₁ ∧
        y₂ = WeierstrassCurve.Affine.negY (flexCurve a b) x₁ y₁))
    (hy₁ : y₁ ≠ 0)
    (hx₂ :
      let ℓ₁ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₁ y₁ y₁
      WeierstrassCurve.Affine.addX (flexCurve a b) x₁ x₁ ℓ₁ ≠ 0)
    (hx₃ :
      let ℓ₁ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₁ y₁ y₁
      let x₂ := WeierstrassCurve.Affine.addX (flexCurve a b) x₁ x₁ ℓ₁
      let y₂ := WeierstrassCurve.Affine.addY (flexCurve a b) x₁ x₁ y₁ ℓ₁
      let ℓ₂ := WeierstrassCurve.Affine.slope (flexCurve a b) x₂ x₁ y₂ y₁
      WeierstrassCurve.Affine.addX (flexCurve a b) x₂ x₁ ℓ₂ ≠ 0) :
    let ℓ₁ := WeierstrassCurve.Affine.slope (flexCurve a b) x₁ x₁ y₁ y₁
    let x₂ := WeierstrassCurve.Affine.addX (flexCurve a b) x₁ x₁ ℓ₁
    let y₂ := WeierstrassCurve.Affine.addY (flexCurve a b) x₁ x₁ y₁ ℓ₁
    let ℓ₂ := WeierstrassCurve.Affine.slope (flexCurve a b) x₂ x₁ y₂ y₁
    let y₃ := WeierstrassCurve.Affine.addY (flexCurve a b) x₂ x₁ y₂ ℓ₂
    ∃ u : ℚ, u ^ 3 = y₃ := by
  dsimp only at hadd hx₂ hx₃ ⊢
  let W := flexCurve a b
  let ℓ₁ := WeierstrassCurve.Affine.slope W x₁ x₁ y₁ y₁
  let x₂ := WeierstrassCurve.Affine.addX W x₁ x₁ ℓ₁
  let y₂ := WeierstrassCurve.Affine.addY W x₁ x₁ y₁ ℓ₁
  let k₁ := lineIntercept x₁ y₁ ℓ₁
  let ℓ₂ := WeierstrassCurve.Affine.slope W x₂ x₁ y₂ y₁
  let x₃ := WeierstrassCurve.Affine.addX W x₂ x₁ ℓ₂
  let y₃ := WeierstrassCurve.Affine.addY W x₂ x₁ y₂ ℓ₂
  let k₂ := lineIntercept x₂ y₂ ℓ₂
  change ∃ u : ℚ, u ^ 3 = y₃
  have hnonvert₁ : ¬(x₁ = x₁ ∧
      y₁ = WeierstrassCurve.Affine.negY W x₁ y₁) := by
    exact fun h ↦ hdouble h.2
  have h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂ := by
    exact WeierstrassCurve.Affine.equation_add h₁ h₁ hnonvert₁
  have hA : y₂ * k₁ ^ 3 = -(y₁ * y₁ * x₂ ^ 3) := by
    exact addY_mul_intercept_cube h₁ h₁ hnonvert₁
  have hB : y₃ * k₂ ^ 3 = -(y₂ * y₁ * x₃ ^ 3) := by
    exact addY_mul_intercept_cube h₂ h₁ hadd
  have hy₂ : y₂ ≠ 0 := by
    intro hy₂
    rw [hy₂, zero_mul] at hA
    have : y₁ * y₁ * x₂ ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hy₁ hy₁) (pow_ne_zero 3 hx₂)
    exact this (neg_eq_zero.mp hA.symm)
  have hcombined :
      y₃ * (k₁ * k₂) ^ 3 = (y₁ * x₂ * x₃) ^ 3 := by
    calc
      y₃ * (k₁ * k₂) ^ 3
          = (y₃ * k₂ ^ 3) * k₁ ^ 3 := by ring
      _ = (-(y₂ * y₁ * x₃ ^ 3)) * k₁ ^ 3 := by rw [hB]
      _ = -(y₁ * x₃ ^ 3) * (y₂ * k₁ ^ 3) := by ring
      _ = -(y₁ * x₃ ^ 3) * (-(y₁ * y₁ * x₂ ^ 3)) := by rw [hA]
      _ = (y₁ * x₂ * x₃) ^ 3 := by ring
  have hnum : y₁ * x₂ * x₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hy₁ hx₂) hx₃
  have hden : k₁ * k₂ ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] at hcombined
    exact (pow_ne_zero 3 hnum) hcombined.symm
  refine ⟨(y₁ * x₂ * x₃) / (k₁ * k₂), ?_⟩
  rw [div_pow]
  exact (div_eq_iff (pow_ne_zero 3 hden)).2 hcombined.symm

/-! ## The Kubert order-nine three-descent -/

/-- If the marked order-nine point in Kubert's family is divisible by three,
then `t(t-1)` is a rational cube.  Both noncuspidality conditions are retained
in the conclusion for direct use by the level-27 quotient map. -/
theorem kubert_three_divisibility_cube
    {t : ℚ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1)
    [WeierstrassCurve.IsElliptic (kubertCurve t)]
    (R : WeierstrassCurve.Affine.Point (kubertCurve t))
    (hR : (3 : ℕ) • R = tateOrigin (kubertB9 t) (kubertC9 t)) :
    ∃ x : ℚ, x ^ 3 = t * (t - 1) := by
  let z : ℚ := t * (t - 1)
  let c : ℚ := kubertC9 t
  let A : ℚ := kubertFlexA t
  let B : ℚ := kubertFlexB t
  let C := kubertFlexChange t
  let E₃raw : WeierstrassCurve ℚ := C • kubertCurve t
  have hcurve : E₃raw = flexCurve A B := by
    exact kubertFlexChange_curve ht₀ ht₁
  haveI : WeierstrassCurve.IsElliptic E₃raw := by
    dsimp [E₃raw]
    infer_instance
  haveI : WeierstrassCurve.IsElliptic (flexCurve A B) := by
    rw [← hcurve]
    infer_instance
  let φraw : WeierstrassCurve.Affine.Point (kubertCurve t) ≃+
      WeierstrassCurve.Affine.Point E₃raw := by
    dsimp [E₃raw, C]
    exact variableChangePointAddEquiv (kubertCurve t) (kubertFlexChange t)
  let φ : WeierstrassCurve.Affine.Point (kubertCurve t) ≃+
      WeierstrassCurve.Affine.Point (flexCurve A B) :=
    φraw.trans (pointCurveEqAddEquiv hcurve)
  have hz : z ≠ 0 := mul_ne_zero ht₀ (sub_ne_zero.mpr ht₁)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (pow_ne_zero 2 ht₀) (sub_ne_zero.mpr ht₁)
  have hQeq : WeierstrassCurve.Affine.Equation (flexCurve A B) (-c) (z ^ 2) := by
    rw [flexCurve_equation_iff]
    dsimp [A, B, c, z, kubertFlexA, kubertFlexB, kubertC9]
    ring
  have hQns : WeierstrassCurve.Affine.Nonsingular (flexCurve A B) (-c) (z ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hQeq
  let Q₃ : WeierstrassCurve.Affine.Point (flexCurve A B) :=
    WeierstrassCurve.Affine.Point.some (-c) (z ^ 2) hQns
  have hrawQns : WeierstrassCurve.Affine.Nonsingular E₃raw (-c) (z ^ 2) := by
    rw [hcurve]
    exact hQns
  have hφrawQ :
      φraw (tateOrigin (kubertB9 t) (kubertC9 t)) =
        WeierstrassCurve.Affine.Point.some (-c) (z ^ 2) hrawQns := by
    change variableChangePointMap (kubertCurve t) (kubertFlexChange t)
        (tateOrigin (kubertB9 t) (kubertC9 t)) =
      WeierstrassCurve.Affine.Point.some (-c) (z ^ 2) hrawQns
    dsimp [variableChangePointMap, tateOrigin]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · simp [c, kubertFlexChange, variableChangePointX, translateToOriginTangent]
    · simp only [kubertFlexChange, variableChangePointY, translateToOriginTangent]
      rw [kubert_flex_tangent_slope ht₀ ht₁]
      dsimp [z]
      simp [kubertB9, kubertC9]
      ring
  have hφQ : φ (tateOrigin (kubertB9 t) (kubertC9 t)) = Q₃ := by
    change (pointCurveEqAddEquiv hcurve)
        (φraw (tateOrigin (kubertB9 t) (kubertC9 t))) = Q₃
    rw [hφrawQ]
    exact pointCurveEqAddEquiv_some hcurve
  let R₃ : WeierstrassCurve.Affine.Point (flexCurve A B) := φ R
  have h₃R₃ : (3 : ℕ) • R₃ = Q₃ := by
    calc
      (3 : ℕ) • R₃ = φ ((3 : ℕ) • R) := by
        rw [map_nsmul]
      _ = φ (tateOrigin (kubertB9 t) (kubertC9 t)) := by rw [hR]
      _ = Q₃ := hφQ
  have hQ₃_ne : Q₃ ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hb9 : kubertB9 t ≠ 0 := kubertB9_ne_zero ht₀ ht₁
  have h₂Q : (2 : ℕ) • tateOrigin (kubertB9 t) (kubertC9 t) ≠ 0 := by
    rw [two_nsmul_tateOrigin (kubertB9 t) (kubertC9 t) hb9]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have h₂Q₃ : (2 : ℕ) • Q₃ ≠ 0 := by
    intro hzero
    apply h₂Q
    apply φ.injective
    rw [map_nsmul, hφQ, hzero, map_zero]
  cases hR₃ : R₃ with
  | zero =>
      have : (3 : ℕ) • R₃ = 0 := by
        rw [hR₃]
        exact nsmul_zero 3
      exact (hQ₃_ne (h₃R₃.symm.trans this)).elim
  | some x₁ y₁ h₁ =>
      let P : WeierstrassCurve.Affine.Point (flexCurve A B) :=
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁
      have h₃P : (3 : ℕ) • P = Q₃ := by simpa [P, hR₃] using h₃R₃
      have hdouble : y₁ ≠ WeierstrassCurve.Affine.negY (flexCurve A B) x₁ y₁ := by
        intro hy
        have h₂P : (2 : ℕ) • P = 0 := by
          simpa [P, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁ := h₁) hy)
        have h₃Peq : (3 : ℕ) • P = P := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul, h₂P,
            zero_add]
        have hPQ : P = Q₃ := h₃Peq.symm.trans h₃P
        apply h₂Q₃
        rw [← hPQ, h₂P]
      let ℓ₁ := WeierstrassCurve.Affine.slope (flexCurve A B) x₁ x₁ y₁ y₁
      let x₂ := WeierstrassCurve.Affine.addX (flexCurve A B) x₁ x₁ ℓ₁
      let y₂ := WeierstrassCurve.Affine.addY (flexCurve A B) x₁ x₁ y₁ ℓ₁
      have hnonvert₁ : ¬(x₁ = x₁ ∧
          y₁ = WeierstrassCurve.Affine.negY (flexCurve A B) x₁ y₁) :=
        fun h ↦ hdouble h.2
      have h₂ns : WeierstrassCurve.Affine.Nonsingular (flexCurve A B) x₂ y₂ :=
        WeierstrassCurve.Affine.nonsingular_add h₁ h₁ hnonvert₁
      let P₂ : WeierstrassCurve.Affine.Point (flexCurve A B) :=
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ns
      have h₂P : (2 : ℕ) • P = P₂ := by
        rw [two_nsmul]
        simpa [P, P₂, ℓ₁, x₂, y₂] using
          (WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h₁) hdouble)
      have hadd : ¬(x₂ = x₁ ∧
          y₂ = WeierstrassCurve.Affine.negY (flexCurve A B) x₁ y₁) := by
        rintro ⟨hx, hy⟩
        have hsum : P₂ + P = 0 := by
          exact WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := h₂ns) (h₂ := h₁) hx hy
        have h₃zero : (3 : ℕ) • P = 0 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul, h₂P]
          exact hsum
        exact hQ₃_ne (h₃P.symm.trans h₃zero)
      have hy₁ : y₁ ≠ 0 := by
        intro hy
        have hx : x₁ = 0 := by
          have heq := (flexCurve_equation_iff A B x₁ y₁).mp h₁.1
          have hxpow : x₁ ^ 3 = 0 := by simpa [hy] using heq.symm
          exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hxpow
        subst x₁
        have h₃zero := three_nsmul_flex_x_zero A B y₁ h₁
        exact hQ₃_ne (h₃P.symm.trans h₃zero)
      have hx₂ : x₂ ≠ 0 := by
        intro hx
        have h₂ns₀ : WeierstrassCurve.Affine.Nonsingular (flexCurve A B) 0 y₂ := by
          simpa [hx] using h₂ns
        have h₃P₂ : (3 : ℕ) • P₂ = 0 := by
          simpa [P₂, hx] using three_nsmul_flex_x_zero A B y₂ h₂ns₀
        apply h₂Q₃
        calc
          (2 : ℕ) • Q₃ = (2 : ℕ) • ((3 : ℕ) • P) := by rw [h₃P]
          _ = (3 : ℕ) • ((2 : ℕ) • P) := by
            simp only [← mul_nsmul]
          _ = (3 : ℕ) • P₂ := by rw [h₂P]
          _ = 0 := h₃P₂
      let ℓ₂ := WeierstrassCurve.Affine.slope (flexCurve A B) x₂ x₁ y₂ y₁
      let x₃ := WeierstrassCurve.Affine.addX (flexCurve A B) x₂ x₁ ℓ₂
      let y₃ := WeierstrassCurve.Affine.addY (flexCurve A B) x₂ x₁ y₂ ℓ₂
      have h₃ns : WeierstrassCurve.Affine.Nonsingular (flexCurve A B) x₃ y₃ :=
        WeierstrassCurve.Affine.nonsingular_add h₂ns h₁ hadd
      let P₃ : WeierstrassCurve.Affine.Point (flexCurve A B) :=
        WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ns
      have h₃Pcoords : (3 : ℕ) • P = P₃ := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul, h₂P]
        simpa [P₂, P, P₃, ℓ₂, x₃, y₃] using
          (WeierstrassCurve.Affine.Point.add_some (h₁ := h₂ns) (h₂ := h₁) hadd)
      have hP₃Q : P₃ = Q₃ := h₃Pcoords.symm.trans h₃P
      have hx₃eq : x₃ = -c := (WeierstrassCurve.Affine.Point.some.inj hP₃Q).1
      have hy₃eq : y₃ = z ^ 2 := (WeierstrassCurve.Affine.Point.some.inj hP₃Q).2
      have hx₃ : x₃ ≠ 0 := by
        intro hx
        apply hc
        apply neg_eq_zero.mp
        rw [← hx₃eq, hx]
      obtain ⟨u, hu⟩ := triple_addY_is_cube h₁.1 hdouble hadd hy₁ hx₂ hx₃
      change u ^ 3 = y₃ at hu
      rw [hy₃eq] at hu
      have hu₀ : u ≠ 0 := by
        intro hu₀
        apply hz
        have : z ^ 2 = 0 := by rw [← hu, hu₀]; norm_num
        exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp this
      refine ⟨z / u, ?_⟩
      change (z / u) ^ 3 = z
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 3 hu₀)).2
      rw [hu]
      ring

/-- The cube supplied by three-divisibility gives the explicit noncuspidal
point `(x,-t)` on the level-27 quotient `y²+y=x³`. -/
theorem kubert_three_divisibility_level27_point
    {t : ℚ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1)
    [WeierstrassCurve.IsElliptic (kubertCurve t)]
    (R : WeierstrassCurve.Affine.Point (kubertCurve t))
    (hR : (3 : ℕ) • R = tateOrigin (kubertB9 t) (kubertC9 t)) :
    ∃ x y : ℚ,
      RationalPointsN27CM.Level27Equation x y ∧
      ¬ RationalPointsN27CM.Level27Cusp x y := by
  obtain ⟨x, hx⟩ := kubert_three_divisibility_cube ht₀ ht₁ R hR
  refine ⟨x, -t, ?_, ?_⟩
  · simp only [RationalPointsN27CM.Level27Equation]
    rw [hx]
    ring
  · rintro ⟨hx₀, _⟩
    have hprod : t * (t - 1) = 0 := by rw [← hx, hx₀]; norm_num
    exact (mul_ne_zero ht₀ (sub_ne_zero.mpr ht₁)) hprod

/-- Consequently the Kubert order-nine origin is not rationally
three-divisible.  This is the special three-descent endpoint needed for the
order-27 exclusion. -/
theorem no_kubert_three_divisibility
    {t : ℚ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1)
    [WeierstrassCurve.IsElliptic (kubertCurve t)] :
    ¬ ∃ R : WeierstrassCurve.Affine.Point (kubertCurve t),
      (3 : ℕ) • R = tateOrigin (kubertB9 t) (kubertC9 t) := by
  rintro ⟨R, hR⟩
  obtain ⟨x, y, hcurve, hnoncusp⟩ :=
    kubert_three_divisibility_level27_point ht₀ ht₁ R hR
  exact hnoncusp (RationalPointsN27CM.level27_rational_points_are_cusps hcurve)

/-! ## Simultaneous Tate normalization of a point and a three-division preimage -/

/-- Normalize a marked point of order greater than three while transporting a
chosen rational three-division preimage through the same two variable changes. -/
theorem exists_tate_normalized_three_preimage_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q R : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hQ : addOrderOf Q = n) (hthree : (3 : ℕ) • R = Q) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      ∃ R' : WeierstrassCurve.Affine.Point (W b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          (3 : ℕ) • R' = tateOrigin b c := by
  cases Q with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hQ
      omega
  | some x₀ y₀ hQaff =>
      have hbase : E⁄ℚ = E := by
        ext <;> simp
      let ι : WeierstrassCurve.Affine.Point (E⁄ℚ) ≃+
          WeierstrassCurve.Affine.Point E := pointCurveEqAddEquiv hbase
      let hQaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        rw [← hbase]
        exact hQaff
      let Q₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hQaffE
      let R₀ : WeierstrassCurve.Affine.Point E := ι R
      have hιQ :
          ι (WeierstrassCurve.Affine.Point.some x₀ y₀ hQaff) = Q₀ := by
        dsimp [ι, Q₀]
        exact pointCurveEqAddEquiv_some hbase
      have hQ₀_order : addOrderOf Q₀ = n := by
        have hmaporder :
            addOrderOf
                (ι (WeierstrassCurve.Affine.Point.some x₀ y₀ hQaff)) = n := by
          calc
            addOrderOf
                (ι (WeierstrassCurve.Affine.Point.some x₀ y₀ hQaff)) =
                addOrderOf
                  (WeierstrassCurve.Affine.Point.some x₀ y₀ hQaff) :=
              addOrderOf_injective ι.toAddMonoidHom ι.injective _
            _ = n := hQ
        rwa [hιQ] at hmaporder
      have hthree₀ : (3 : ℕ) • R₀ = Q₀ := by
        calc
          (3 : ℕ) • R₀ = ι ((3 : ℕ) • R) := by
            dsimp [R₀]
            exact (map_nsmul ι 3 R).symm
          _ = ι (WeierstrassCurve.Affine.Point.some x₀ y₀ hQaff) :=
            congrArg ι hthree
          _ = Q₀ := hιQ
      let Qsmall₀ : ∀ m < n, 0 < m → (m : ℕ) • Q₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := Q₀) (by omega)).mp hQ₀_order).2
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden₀
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h₂zero : (2 : ℕ) • Q₀ = 0 := by
          simpa [Q₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hQaffE) hy)
        exact Qsmall₀ 2 (by omega) (by norm_num) h₂zero
      let C₀ := translateToOriginTangent E x₀ y₀
      let W₁ : WeierstrassCurve ℚ := C₀ • E
      haveI : W₁.IsElliptic := by
        dsimp [W₁]
        infer_instance
      let φ₀ : WeierstrassCurve.Affine.Point E ≃+
          WeierstrassCurve.Affine.Point W₁ := by
        dsimp [W₁]
        exact variableChangePointAddEquiv E C₀
      have hW₁a₆ : W₁.a₆ = 0 := by
        simpa [W₁, C₀] using
          translateToOriginTangent_a₆_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hQaffE.1
      have hW₁a₄ : W₁.a₄ = 0 := by
        simpa [W₁, C₀] using
          translateToOriginTangent_a₄_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hden
      have hW₁a₃_formula : W₁.a₃ = E.a₃ + E.a₁ * x₀ + 2 * y₀ := by
        simp [W₁, C₀]
      have hW₁a₃_ne : W₁.a₃ ≠ 0 := by
        rw [hW₁a₃_formula]
        intro h
        apply hden
        linarith
      have hW₁origin : WeierstrassCurve.Affine.Nonsingular W₁ 0 0 := by
        apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        rw [WeierstrassCurve.Affine.equation_iff]
        simp [hW₁a₆]
      have hφ₀Q_origin :
          φ₀ Q₀ = WeierstrassCurve.Affine.Point.some 0 0 hW₁origin := by
        change variableChangePointMap E C₀ Q₀ =
          WeierstrassCurve.Affine.Point.some 0 0 hW₁origin
        dsimp [variableChangePointMap, Q₀]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor <;>
          simp [C₀, variableChangePointX, variableChangePointY,
            translateToOriginTangent]
      have hW₁a₂_ne : W₁.a₂ ≠ 0 := by
        intro hW₁a₂
        have h₃zero_origin :
            (3 : ℕ) •
                (WeierstrassCurve.Affine.Point.some 0 0 hW₁origin :
                  WeierstrassCurve.Affine.Point W₁) = 0 := by
          apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval W₁ hW₁origin).mpr
          rw [W₁.ΨSq_ofNat 3]
          simp [show ¬ Even (3 : ℕ) by decide, WeierstrassCurve.preΨ'_three,
            WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
            WeierstrassCurve.b₆, WeierstrassCurve.b₈, hW₁a₂,
            hW₁a₄, hW₁a₆]
        have h₃zero_map : (3 : ℕ) • φ₀ Q₀ = 0 := by
          simpa [hφ₀Q_origin] using h₃zero_origin
        have h₃zero : (3 : ℕ) • Q₀ = 0 := by
          apply φ₀.injective
          rw [map_nsmul, h₃zero_map, map_zero]
        exact Qsmall₀ 3 hn (by norm_num) h₃zero
      let ρ : ℚ := W₁.a₃ / W₁.a₂
      have hρ : ρ ≠ 0 := div_ne_zero hW₁a₃_ne hW₁a₂_ne
      let C₁ := scaleByRho ρ hρ
      let b : ℚ := tateBFromCoefficients W₁.a₂ W₁.a₃
      let c : ℚ := tateCFromCoefficients W₁.a₁ W₁.a₂ W₁.a₃
      have hW₂eq : C₁ • W₁ = W b c := by
        ext <;> dsimp [C₁, ρ, b, c, W, tateNormalFormCurve,
          tateBFromCoefficients, tateCFromCoefficients]
        · rw [WeierstrassCurve.variableChange_a₁]
          simp [scaleByRho]
          field_simp [hW₁a₂_ne, hW₁a₃_ne]
        · rw [scaleByTateRho_a₂ W₁ hW₁a₂_ne hW₁a₃_ne]
          ring
        · rw [scaleByTateRho_a₃ W₁ hW₁a₂_ne hW₁a₃_ne]
          ring
        · simp [WeierstrassCurve.variableChange_a₄, scaleByRho, hW₁a₄]
        · simp [WeierstrassCurve.variableChange_a₆, scaleByRho, hW₁a₆]
      haveI : WeierstrassCurve.IsElliptic (W b c) := by
        rw [← hW₂eq]
        infer_instance
      let φ₁raw : WeierstrassCurve.Affine.Point W₁ ≃+
          WeierstrassCurve.Affine.Point (C₁ • W₁) :=
        variableChangePointAddEquiv W₁ C₁
      let φ₁ : WeierstrassCurve.Affine.Point W₁ ≃+
          WeierstrassCurve.Affine.Point (W b c) :=
        φ₁raw.trans (pointCurveEqAddEquiv hW₂eq)
      have hφ₁φ₀Q_origin : φ₁ (φ₀ Q₀) = tateOrigin b c := by
        rw [hφ₀Q_origin]
        have hRawOrigin :
            WeierstrassCurve.Affine.Nonsingular (C₁ • W₁) 0 0 := by
          rw [hW₂eq]
          exact tate_origin_nonsingular b c
        have hφ₁raw_origin :
            φ₁raw (WeierstrassCurve.Affine.Point.some 0 0 hW₁origin) =
              WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin := by
          change variableChangePointMap W₁ C₁
              (WeierstrassCurve.Affine.Point.some 0 0 hW₁origin) =
            WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin
          dsimp [variableChangePointMap]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor <;>
            simp [C₁, variableChangePointX, variableChangePointY, scaleByRho]
        change (pointCurveEqAddEquiv hW₂eq)
            (φ₁raw (WeierstrassCurve.Affine.Point.some 0 0 hW₁origin)) =
          tateOrigin b c
        rw [hφ₁raw_origin]
        exact pointCurveEqAddEquiv_some hW₂eq
      have hOriginOrder : addOrderOf (tateOrigin b c) = n := by
        have hmaporder : addOrderOf (φ₁ (φ₀ Q₀)) = n := by
          calc
            addOrderOf (φ₁ (φ₀ Q₀)) = addOrderOf (φ₀ Q₀) :=
              addOrderOf_injective φ₁.toAddMonoidHom φ₁.injective (φ₀ Q₀)
            _ = addOrderOf Q₀ :=
              addOrderOf_injective φ₀.toAddMonoidHom φ₀.injective Q₀
            _ = n := hQ₀_order
        rwa [hφ₁φ₀Q_origin] at hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W₁.a₂ ^ 3 / W₁.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW₁a₂_ne) (pow_ne_zero 2 hW₁a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      let R' : WeierstrassCurve.Affine.Point (W b c) := φ₁ (φ₀ R₀)
      have hR' : (3 : ℕ) • R' = tateOrigin b c := by
        calc
          (3 : ℕ) • R' = φ₁ ((3 : ℕ) • φ₀ R₀) := by rw [map_nsmul]
          _ = φ₁ (φ₀ ((3 : ℕ) • R₀)) :=
            congrArg φ₁ (map_nsmul φ₀ 3 R₀).symm
          _ = φ₁ (φ₀ Q₀) := by rw [hthree₀]
          _ = tateOrigin b c := hφ₁φ₀Q_origin
      exact ⟨b, c, inferInstance, R', hOriginOrder, hb, hR'⟩

private theorem addOrderOf_three_nsmul_of_order27
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 27) :
    addOrderOf ((3 : ℕ) • P) = 9 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

/-- End-to-end order-27 exclusion obtained from simultaneous Tate
normalization, Kubert's order-nine parametrization, and the special
three-descent above. -/
theorem no_rational_point_of_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 27 := by
  rintro ⟨P, hP⟩
  let Q : (E⁄ℚ).Point := (3 : ℕ) • P
  have hQ : addOrderOf Q = 9 := addOrderOf_three_nsmul_of_order27 hP
  obtain ⟨b, c, hEll, R, hord, hb, hthree⟩ :=
    exists_tate_normalized_three_preimage_of_addOrder_gt_three E Q P 9
      (by norm_num) hQ rfl
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have hF9 : TateNFDivision.F9 b c = 0 :=
    TateOrder18.F9_eq_zero_of_tateOrigin_order_nine b c hb hord
  obtain ⟨t, ht₀, ht₁, hbparam, hcparam⟩ := F9_parametrization hb hF9
  subst b
  subst c
  exact no_kubert_three_divisibility ht₀ ht₁ ⟨R, hthree⟩

end

end MazurProof.RationalPointsN27ThreeDescent
