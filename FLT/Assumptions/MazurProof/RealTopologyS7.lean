import FLT.Assumptions.MazurProof.RealTopologyS4

/-!
# Real topology route, S7: local chord calculus

This file isolates the algebraic differential identity used in the local
additivity proof for the S5 theta candidate.  For a fixed point `Q=(a,b)` and a
moving point `P=(x,y)` with `x ≠ a`, we use the usual chord formulas on
`shortW A B`.
-/

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology

namespace MazurProof.RealTopology

noncomputable section

/-- Slope of the chord through `(x,y)` and `(a,b)`. -/
def chordM (x y a b : ℝ) : ℝ :=
  (y - b) / (x - a)

/-- The x-coordinate of the chord sum in the short Weierstrass model. -/
def chordX (A x y a b : ℝ) : ℝ :=
  (chordM x y a b) ^ 2 - A - x - a

/-- The y-coordinate of the chord sum in the short Weierstrass model. -/
def chordY (A x y a b : ℝ) : ℝ :=
  -(y + chordM x y a b * (chordX A x y a b - x))

/-- Divided difference of `shortCubic A B` at `x` and `a`. -/
def chordDivDiff (A B x a : ℝ) : ℝ :=
  x ^ 2 + x * a + a ^ 2 + A * (x + a) + B

theorem shortCubic_sub_eq_mul_chordDivDiff (A B x a : ℝ) :
    shortCubic A B x - shortCubic A B a =
      (x - a) * chordDivDiff A B x a := by
  simp [shortCubic, chordDivDiff]
  ring

theorem shortCubicDeriv_eq_chordDivDiff_add (A B x a : ℝ) :
    shortCubicDeriv A B x =
      chordDivDiff A B x a + (x - a) * (2 * x + a + A) := by
  simp [shortCubicDeriv, chordDivDiff]
  ring

theorem chordM_mul_sub_eq
    {x y a b : ℝ} (hD : x - a ≠ 0) :
    chordM x y a b * (x - a) = y - b := by
  unfold chordM
  field_simp [hD]

theorem chordM_mul_y_add_eq_chordDivDiff
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hD : x - a ≠ 0) :
    chordM x y a b * (y + b) = chordDivDiff A B x a := by
  apply mul_left_cancel₀ hD
  calc
    (x - a) * (chordM x y a b * (y + b))
        = (chordM x y a b * (x - a)) * (y + b) := by ring
    _ = (y - b) * (y + b) := by rw [chordM_mul_sub_eq hD]
    _ = y ^ 2 - b ^ 2 := by ring
    _ = shortCubic A B x - shortCubic A B a := by rw [hy, hb]
    _ = (x - a) * chordDivDiff A B x a :=
      shortCubic_sub_eq_mul_chordDivDiff A B x a

theorem chord_deriv_key
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hD : x - a ≠ 0) :
    shortCubicDeriv A B x - 2 * y * chordM x y a b =
      (x - a) * (x - chordX A x y a b) := by
  have hder :
      shortCubicDeriv A B x =
        chordDivDiff A B x a + (x - a) * (2 * x + a + A) :=
    shortCubicDeriv_eq_chordDivDiff_add A B x a
  have hmadd :
      chordM x y a b * (y + b) = chordDivDiff A B x a :=
    chordM_mul_y_add_eq_chordDivDiff hy hb hD
  have hmD :
      chordM x y a b * (x - a) = y - b :=
    chordM_mul_sub_eq (x := x) (y := y) (a := a) (b := b) hD
  have hmyb :
      chordM x y a b * (y - b) =
        chordM x y a b * (chordM x y a b * (x - a)) := by
    rw [← hmD]
  calc
    shortCubicDeriv A B x - 2 * y * chordM x y a b
        = chordDivDiff A B x a + (x - a) * (2 * x + a + A) -
            (chordM x y a b * (y + b) +
              chordM x y a b * (y - b)) := by
          rw [hder]
          ring
    _ = chordDivDiff A B x a + (x - a) * (2 * x + a + A) -
            (chordDivDiff A B x a +
              chordM x y a b * (chordM x y a b * (x - a))) := by
          rw [hmadd, hmyb]
    _ = (x - a) * (x - chordX A x y a b) := by
          unfold chordX
          ring

theorem chord_slope_deriv_expr
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0) :
    (((shortCubicDeriv A B x) / (2 * y)) * (x - a) - (y - b)) /
        (x - a) ^ 2 =
      (x - chordX A x y a b) / (2 * y) := by
  have hkey := chord_deriv_key (A := A) (B := B) (x := x) (y := y)
    (a := a) (b := b) hy hb hD
  have hmD :
      chordM x y a b * (x - a) = y - b :=
    chordM_mul_sub_eq (x := x) (y := y) (a := a) (b := b) hD
  have hD2 : (x - a) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have h2y : 2 * y ≠ 0 := by
    exact mul_ne_zero (by norm_num) hy0
  field_simp [hD, hD2, h2y] at hkey hmD ⊢
  linear_combination (x - a) * hkey + (2 * y) * hmD

theorem chord_deriv_identity_from_slope_expr
    {A x y a b : ℝ}
    (hy0 : y ≠ 0) :
    2 * chordM x y a b * ((x - chordX A x y a b) / (2 * y)) - 1 =
      chordY A x y a b / y := by
  unfold chordY
  field_simp [hy0]
  ring

theorem chord_deriv_identity_algebra
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0) :
    let m := chordM x y a b
    let _x3 := chordX A x y a b
    let y3 := chordY A x y a b
    2 * m * (((shortCubicDeriv A B x) / (2 * y)) * (x - a) - (y - b)) /
        (x - a) ^ 2 - 1 = y3 / y := by
  dsimp only
  rw [show 2 * chordM x y a b *
        (((shortCubicDeriv A B x) / (2 * y)) * (x - a) - (y - b)) /
          (x - a) ^ 2 =
      2 * chordM x y a b *
        ((((shortCubicDeriv A B x) / (2 * y)) * (x - a) - (y - b)) /
          (x - a) ^ 2) by ring]
  rw [chord_slope_deriv_expr hy hb hy0 hD]
  exact chord_deriv_identity_from_slope_expr hy0

theorem hasDerivAt_chordX_signed
    {u : ℝ → ℝ} {A B a b x y : ℝ}
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x) :
    HasDerivAt
      (fun t : ℝ => chordX A t (u t) a b)
      (chordY A x y a b / y)
      x := by
  let m' : ℝ :=
    (((shortCubicDeriv A B x) / (2 * y)) * (x - a) - (y - b)) /
      (x - a) ^ 2
  have hnum :
      HasDerivAt (fun t : ℝ => u t - b) (shortCubicDeriv A B x / (2 * y)) x := by
    simpa using hu.sub_const b
  have hden : HasDerivAt (fun t : ℝ => t - a) 1 x := by
    simpa using (hasDerivAt_id x).sub_const a
  have hm :
      HasDerivAt (fun t : ℝ => chordM t (u t) a b) m' x := by
    unfold chordM m'
    simpa [huval] using hnum.fun_div hden hD
  have hxpow :
      HasDerivAt (fun t : ℝ => (chordM t (u t) a b) ^ 2)
        (2 * chordM x y a b * m') x := by
    simpa [huval, pow_one, mul_comm, mul_left_comm, mul_assoc] using hm.fun_pow 2
  have hcore :
      HasDerivAt
        (fun t : ℝ => (chordM t (u t) a b) ^ 2 - A - t - a)
        (2 * chordM x y a b * m' - 1) x := by
    have hA :
        HasDerivAt (fun t : ℝ => (chordM t (u t) a b) ^ 2 - A)
          (2 * chordM x y a b * m') x := by
      simpa using hxpow.sub_const A
    have hsubx := hA.sub (hasDerivAt_id x)
    simpa [Pi.sub_apply, sub_eq_add_neg, add_assoc] using hsubx.sub_const a
  have halg :
      2 * chordM x y a b * m' - 1 = chordY A x y a b / y := by
    dsimp [m']
    rw [show 2 * chordM x y a b *
          (((shortCubicDeriv A B x) / (2 * y) * (x - a) - (y - b)) /
            (x - a) ^ 2) =
        2 * chordM x y a b *
          ((shortCubicDeriv A B x) / (2 * y) * (x - a) - (y - b)) /
            (x - a) ^ 2 by ring]
    exact chord_deriv_identity_algebra (A := A) (B := B) (x := x) (y := y)
      (a := a) (b := b) hy hQ hy0 hD
  simpa [chordX] using hcore.congr_deriv halg

theorem hasDerivAt_chordX_upper_sqrt
    {A B a b x : ℝ}
    (hQ : b ^ 2 = shortCubic A B a)
    (hxpos : 0 < shortCubic A B x)
    (hD : x - a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => chordX A t (√(shortCubic A B t)) a b)
      (chordY A x (√(shortCubic A B x)) a b / √(shortCubic A B x))
      x := by
  have hy : (√(shortCubic A B x)) ^ 2 = shortCubic A B x :=
    sq_sqrt hxpos.le
  have hy0 : √(shortCubic A B x) ≠ 0 :=
    (sqrt_pos.mpr hxpos).ne'
  exact hasDerivAt_chordX_signed (A := A) (B := B) (a := a) (b := b)
    (x := x) (y := √(shortCubic A B x))
    hQ hy hy0 hD rfl (sqrt_shortCubic_hasDerivAt_of_pos hxpos)

theorem hasDerivAt_chordX_lower_sqrt
    {A B a b x : ℝ}
    (hQ : b ^ 2 = shortCubic A B a)
    (hxpos : 0 < shortCubic A B x)
    (hD : x - a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => chordX A t (-√(shortCubic A B t)) a b)
      (chordY A x (-√(shortCubic A B x)) a b / (-√(shortCubic A B x)))
      x := by
  have hy : (-√(shortCubic A B x)) ^ 2 = shortCubic A B x := by
    rw [neg_sq]
    exact sq_sqrt hxpos.le
  have hsqrt0 : √(shortCubic A B x) ≠ 0 :=
    (sqrt_pos.mpr hxpos).ne'
  have hy0 : -√(shortCubic A B x) ≠ 0 :=
    neg_ne_zero.mpr hsqrt0
  have hderiv_eq :
      -(shortCubicDeriv A B x / (2 * √(shortCubic A B x))) =
        shortCubicDeriv A B x / (2 * (-√(shortCubic A B x))) := by
    field_simp [hsqrt0]
  have hu :
      HasDerivAt (fun t : ℝ => -√(shortCubic A B t))
        (shortCubicDeriv A B x / (2 * (-√(shortCubic A B x)))) x :=
    (sqrt_shortCubic_hasDerivAt_of_pos hxpos).neg.congr_deriv hderiv_eq
  exact hasDerivAt_chordX_signed (A := A) (B := B) (a := a) (b := b)
    (x := x) (y := -√(shortCubic A B x))
    hQ hy hy0 hD rfl hu

theorem shortW_slope_eq_chordM
    {A B x y a b : ℝ}
    (hD : x - a ≠ 0) :
    WeierstrassCurve.Affine.slope (shortW A B) x a y b =
      chordM x y a b := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (W := shortW A B)
    (x₁ := x) (x₂ := a) (y₁ := y) (y₂ := b) (sub_ne_zero.mp hD)]
  rfl

theorem shortW_addX_eq_chordX
    {A B x y a b : ℝ}
    (hD : x - a ≠ 0) :
    WeierstrassCurve.Affine.addX (shortW A B) x a
        (WeierstrassCurve.Affine.slope (shortW A B) x a y b) =
      chordX A x y a b := by
  rw [shortW_slope_eq_chordM (A := A) (B := B) hD]
  simp [shortW, chordX, WeierstrassCurve.Affine.addX]

theorem shortW_addY_eq_chordY
    {A B x y a b : ℝ}
    (hD : x - a ≠ 0) :
    WeierstrassCurve.Affine.addY (shortW A B) x a y
        (WeierstrassCurve.Affine.slope (shortW A B) x a y b) =
      chordY A x y a b := by
  rw [shortW_slope_eq_chordM (A := A) (B := B) hD]
  simp [shortW, chordX, chordY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  ring

theorem chordY_sq_eq_shortCubic_chordX
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hD : x - a ≠ 0) :
    (chordY A x y a b) ^ 2 =
      shortCubic A B (chordX A x y a b) := by
  have hP : WeierstrassCurve.Affine.Equation (shortW A B) x y := by
    exact shortW_equation_iff.mpr hy
  have hQ : WeierstrassCurve.Affine.Equation (shortW A B) a b := by
    exact shortW_equation_iff.mpr hb
  have hxy :
      ¬(x = a ∧ y = WeierstrassCurve.Affine.negY (shortW A B) a b) := by
    intro h
    exact hD (sub_eq_zero.mpr h.1)
  have hadd := WeierstrassCurve.Affine.equation_add
    (W := shortW A B) hP hQ hxy
  rw [shortW_addX_eq_chordX (A := A) (B := B) (x := x) (y := y)
      (a := a) (b := b) hD,
    shortW_addY_eq_chordY (A := A) (B := B) (x := x) (y := y)
      (a := a) (b := b) hD] at hadd
  exact shortW_equation_iff.mp hadd

theorem sqrt_shortCubic_chordX_eq_chordY_of_chordY_pos
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hD : x - a ≠ 0)
    (hy3pos : 0 < chordY A x y a b) :
    √(shortCubic A B (chordX A x y a b)) =
      chordY A x y a b := by
  have hcurve := chordY_sq_eq_shortCubic_chordX
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b) hy hb hD
  rcases y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic hcurve with h | h
  · exact h.symm
  · exfalso
    have hsqrt_nonneg : 0 ≤ √(shortCubic A B (chordX A x y a b)) :=
      sqrt_nonneg _
    have hy3nonpos : chordY A x y a b ≤ 0 := by
      rw [h]
      exact neg_nonpos.mpr hsqrt_nonneg
    linarith

theorem sqrt_shortCubic_chordX_eq_neg_chordY_of_chordY_neg
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hD : x - a ≠ 0)
    (hy3neg : chordY A x y a b < 0) :
    √(shortCubic A B (chordX A x y a b)) =
      -chordY A x y a b := by
  have hcurve := chordY_sq_eq_shortCubic_chordX
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b) hy hb hD
  rcases y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic hcurve with h | h
  · have hy3nonneg : 0 ≤ chordY A x y a b := by
      rw [h]
      exact sqrt_nonneg _
    linarith
  · rw [h]
    ring

theorem rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_pos
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (hy3pos : 0 < chordY A x y a b) :
    rightIntegrand A B (chordX A x y a b) *
        (chordY A x y a b / y) =
      1 / y := by
  have hsqrt := sqrt_shortCubic_chordX_eq_chordY_of_chordY_pos
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b) hy hb hD hy3pos
  have hy30 : chordY A x y a b ≠ 0 := hy3pos.ne'
  unfold rightIntegrand
  rw [hsqrt]
  field_simp [hy0, hy30]

theorem neg_rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_neg
    {A B x y a b : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hb : b ^ 2 = shortCubic A B a)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (hy3neg : chordY A x y a b < 0) :
    -(rightIntegrand A B (chordX A x y a b)) *
        (chordY A x y a b / y) =
      1 / y := by
  have hsqrt := sqrt_shortCubic_chordX_eq_neg_chordY_of_chordY_neg
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b) hy hb hD hy3neg
  have hy30 : chordY A x y a b ≠ 0 := hy3neg.ne
  unfold rightIntegrand
  rw [hsqrt]
  field_simp [hy0, hy30]

theorem hasDerivAt_neg_sigma_comp_chordX_signed
    {u : ℝ → ℝ} {A B e a b x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b) :
    HasDerivAt
      (fun t : ℝ => -sigma A B (chordX A t (u t) a b))
      (rightIntegrand A B (chordX A x y a b) *
        (chordY A x y a b / y)) x := by
  have hx3u : e < chordX A x (u x) a b := by
    simpa [huval] using hx3
  have houter :
      HasDerivAt (fun z : ℝ => -sigma A B z)
        (rightIntegrand A B (chordX A x (u x) a b)) (chordX A x (u x) a b) :=
    neg_sigma_hasDerivAt_of_right hroot hderiv hposRight hx3u
  have hinner := hasDerivAt_chordX_signed hQ hy hy0 hD huval hu
  simpa [Function.comp_def, huval] using houter.comp x hinner

theorem hasDerivAt_sigma_comp_chordX_signed
    {u : ℝ → ℝ} {A B e a b x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b) :
    HasDerivAt
      (fun t : ℝ => sigma A B (chordX A t (u t) a b))
      (-(rightIntegrand A B (chordX A x y a b)) *
        (chordY A x y a b / y)) x := by
  have hx3u : e < chordX A x (u x) a b := by
    simpa [huval] using hx3
  have houter :
      HasDerivAt (sigma A B)
        (-(rightIntegrand A B (chordX A x (u x) a b))) (chordX A x (u x) a b) :=
    sigma_hasDerivAt_of_right hroot hderiv hposRight hx3u
  have hinner := hasDerivAt_chordX_signed hQ hy hy0 hD huval hu
  simpa [Function.comp_def, huval] using houter.comp x hinner

theorem hasDerivAt_neg_sigma_comp_chordX_signed_of_chordY_pos
    {u : ℝ → ℝ} {A B e a b x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3pos : 0 < chordY A x y a b) :
    HasDerivAt
      (fun t : ℝ => -sigma A B (chordX A t (u t) a b))
      (1 / y) x := by
  have hbase := hasDerivAt_neg_sigma_comp_chordX_signed
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hy0 hD huval hu hx3
  have hderiv_eq :=
    rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_pos
      (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
      hy hQ hy0 hD hy3pos
  exact hbase.congr_deriv hderiv_eq

theorem hasDerivAt_sigma_comp_chordX_signed_of_chordY_neg
    {u : ℝ → ℝ} {A B e a b x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hy0 : y ≠ 0)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3neg : chordY A x y a b < 0) :
    HasDerivAt
      (fun t : ℝ => sigma A B (chordX A t (u t) a b))
      (1 / y) x := by
  have hbase := hasDerivAt_sigma_comp_chordX_signed
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hy0 hD huval hu hx3
  have hderiv_eq :=
    neg_rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_neg
      (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
      hy hQ hy0 hD hy3neg
  exact hbase.congr_deriv hderiv_eq

end

end MazurProof.RealTopology
