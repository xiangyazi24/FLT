import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.TateZ2xZ10Reduction

/-!
# Tate-normal-form reduction layer for `ZMod 2 × ZMod 12`

This file mirrors `scratch.TateZ2xZ10Reduction` up through the Tate
normalization and the order-12 polynomial.  The downstream map to the `N = 12`
obstruction curve is kept in this module so `DescentBridgeN12` can import a
single proven forward direction once the algebraic branch step is closed.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ12Reduction

open Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The order-12 Tate condition. -/
def Phi12 (b c : ℚ) : ℚ :=
  3 * b ^ 4 - b ^ 3 * c ^ 2 - 9 * b ^ 3 * c + 10 * b ^ 2 * c ^ 2
    + b * c ^ 4 - 5 * b * c ^ 3 + c ^ 6 + c ^ 4

/-- The `x`-coordinate of `6 • (0,0)` on Tate normal form. -/
def tateX6 (b c : ℚ) : ℚ :=
  (b - c) * (b ^ 2 - b * c - c ^ 3) / (b - c ^ 2 - c) ^ 2

/-- The `y`-coordinate of `6 • (0,0)` on Tate normal form. -/
def tateY6 (b c : ℚ) : ℚ :=
  c * (b - c) ^ 2 * (2 * b ^ 2 - b * c ^ 2 - 3 * b * c + c ^ 2) /
    (b - c ^ 2 - c) ^ 3

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

private def tateOriginPoint (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private lemma tate_point_nonsingular_of_equation
    (b c x y : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (h :
      y ^ 2 + (1 - c) * x * y - b * y =
        x ^ 3 - b * x ^ 2) :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x y := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]
  nlinarith

private lemma tate_twoP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) :
    ∃ h2 : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) b (b * c),
      (2 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some b (b * c) h2 := by
  let W := tateNormalFormCurve b c
  have h2 : WeierstrassCurve.Affine.Nonsingular W b (b * c) := by
    apply tate_point_nonsingular_of_equation
    ring
  refine ⟨h2, ?_⟩
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    simpa [W, tateNormalFormCurve, WeierstrassCurve.Affine.negY, eq_comm] using hb
  rw [two_nsmul]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY]
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    ring

private lemma tate_threeP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) :
    ∃ h3 : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) c (b - c),
      (3 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some c (b - c) h3 := by
  let W := tateNormalFormCurve b c
  rcases tate_twoP_eq b c hb with ⟨h2, h2eq⟩
  have h3 : WeierstrassCurve.Affine.Nonsingular W c (b - c) := by
    apply tate_point_nonsingular_of_equation
    ring
  refine ⟨h3, ?_⟩
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    field_simp [hb]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    field_simp [hb]
    ring

private lemma tate_fourP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ h4 : WeierstrassCurve.Affine.Nonsingular
        (tateNormalFormCurve b c)
        (b * (b - c) / c ^ 2)
        (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3),
      (4 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3) h4 := by
  let W := tateNormalFormCurve b c
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  have h4 : WeierstrassCurve.Affine.Nonsingular W
      (b * (b - c) / c ^ 2)
      (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3) := by
    apply tate_point_nonsingular_of_equation
    field_simp [hc]
    ring
  refine ⟨h4, ?_⟩
  rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h3eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    field_simp [hc]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring

private lemma tate_fiveP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b - c ≠ 0) :
    ∃ h5 : WeierstrassCurve.Affine.Nonsingular
        (tateNormalFormCurve b c) (tateX5 b c) (tateY5 b c),
      (5 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some (tateX5 b c) (tateY5 b c) h5 := by
  let W := tateNormalFormCurve b c
  rcases tate_fourP_eq b c hb hc with ⟨h4, h4eq⟩
  have h5 : WeierstrassCurve.Affine.Nonsingular W (tateX5 b c) (tateY5 b c) := by
    apply tate_point_nonsingular_of_equation
    unfold tateX5 tateY5
    field_simp [hbc]
    ring
  refine ⟨h5, ?_⟩
  have hx4 : b * (b - c) / c ^ 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hb hbc) (pow_ne_zero 2 hc)
  rw [show (5 : ℕ) = 4 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h4eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx4]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx4]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    unfold tateX5
    field_simp [hb, hc, hbc]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx4]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    unfold tateY5
    field_simp [hb, hc, hbc]
    ring

private lemma tate_sixP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hD : b - c ^ 2 - c ≠ 0) :
    ∃ h6 : WeierstrassCurve.Affine.Nonsingular
        (tateNormalFormCurve b c) (tateX6 b c) (tateY6 b c),
      (6 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some (tateX6 b c) (tateY6 b c) h6 := by
  let W := tateNormalFormCurve b c
  rcases tate_fiveP_eq b c hb hc hbc with ⟨h5, h5eq⟩
  have h6 : WeierstrassCurve.Affine.Nonsingular W (tateX6 b c) (tateY6 b c) := by
    apply tate_point_nonsingular_of_equation
    unfold tateX6 tateY6
    field_simp [hD]
    ring
  refine ⟨h6, ?_⟩
  have hx5 : tateX5 b c ≠ 0 := by
    unfold tateX5
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hc) hD)
      (pow_ne_zero 2 hbc)
  rw [show (6 : ℕ) = 5 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h5eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx5]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx5]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    unfold tateX5 tateY5 tateX6
    field_simp [hb, hc, hbc, hD]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx5]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    unfold tateX5 tateY5 tateY6
    field_simp [hb, hc, hbc, hD]
    ring

private lemma tate_fourP_eq_zero_of_c_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc0 : c = 0) :
    (4 : ℕ) • tateOriginPoint b c = 0 := by
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h3eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hc0]
  simp [tateNormalFormCurve, WeierstrassCurve.Affine.negY, hc0]

private lemma tate_fiveP_eq_zero_of_b_eq_c
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hbc_eq : b = c) :
    (5 : ℕ) • tateOriginPoint b c = 0 := by
  rcases tate_twoP_eq b c hb with ⟨h2, h2eq⟩
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  rw [show (5 : ℕ) = 2 + 3 by norm_num, add_nsmul]
  rw [h2eq, h3eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hbc_eq]
  rw [WeierstrassCurve.Affine.negY]
  simp [tateNormalFormCurve, hbc_eq]
  ring

private lemma tate_sixP_eq_zero_of_b_sub_c_sq_sub_c_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hD0 : b - c ^ 2 - c = 0) :
    (6 : ℕ) • tateOriginPoint b c = 0 := by
  rcases tate_fiveP_eq b c hb hc hbc with ⟨h5, h5eq⟩
  have hx5 : tateX5 b c = 0 := by
    unfold tateX5
    rw [hD0]
    ring
  have hy5 : tateY5 b c = b := by
    have hbexpr : b = c ^ 2 + c := by nlinarith
    unfold tateY5
    rw [hbexpr]
    field_simp [hc]
    ring
  rw [show (6 : ℕ) = 5 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h5eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx5]
  rw [hy5]
  simp [tateNormalFormCurve, WeierstrassCurve.Affine.negY]

private lemma origin_three_nsmul_eq_zero_of_a2_eq_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {h0 : WeierstrassCurve.Affine.Nonsingular W 0 0}
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ ≠ 0)
    (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h0 :
          WeierstrassCurve.Affine.Point W) = 0 := by
  let O : WeierstrassCurve.Affine.Point W :=
    WeierstrassCurve.Affine.Point.some 0 0 h0
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    intro h
    apply ha₃
    rw [WeierstrassCurve.Affine.negY] at h
    linarith
  have h2 : WeierstrassCurve.Affine.Nonsingular W 0 (-W.a₃) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [ha₂, ha₄, ha₆]
    ring
  have h2eq :
      (2 : ℕ) • O =
        WeierstrassCurve.Affine.Point.some 0 (-W.a₃) h2 := by
    rw [two_nsmul]
    simp only [O]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

lemma Phi12_of_tate_6P_twoTorsion (b c : ℚ) (hc : c ≠ 0)
    (hD : b - c ^ 2 - c ≠ 0)
    (h6P2 : 2 * tateY6 b c + (1 - c) * tateX6 b c - b = 0) :
    Phi12 b c = 0 := by
  unfold tateX6 tateY6 at h6P2
  field_simp [hD] at h6P2
  ring_nf at h6P2
  have hprod : c * Phi12 b c = 0 := by
    unfold Phi12
    ring_nf
    linear_combination h6P2
  exact (mul_eq_zero.mp hprod).resolve_left hc

/--
Pure group-theory extraction from an injective `ZMod 2 × ZMod 12`.
-/
theorem injective_Z2xZ12_gives_order12_and_independent_2torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let P := f ((0 : ZMod 2), (1 : ZMod 12))
    let T := f ((1 : ZMod 2), (0 : ZMod 12))
    addOrderOf P = 12 ∧
      (2 : ℕ) • T = 0 ∧ T ≠ 0 ∧
      (6 : ℕ) • P = f ((0 : ZMod 2), (6 : ZMod 12)) ∧
      (6 : ℕ) • P ≠ 0 ∧
      (2 : ℕ) • ((6 : ℕ) • P) = 0 ∧
      T ≠ (6 : ℕ) • P := by
  classical
  let p0 : ZMod 2 × ZMod 12 := ((0 : ZMod 2), (1 : ZMod 12))
  let t0 : ZMod 2 × ZMod 12 := ((1 : ZMod 2), (0 : ZMod 12))
  let p6 : ZMod 2 × ZMod 12 := ((0 : ZMod 2), (6 : ZMod 12))
  have hp0_order : addOrderOf p0 = 12 := by
    simp [p0, Prod.addOrderOf_mk]
  have hP_order : addOrderOf (f p0) = 12 := by
    rw [addOrderOf_injective f hf, hp0_order]
  have ht0_two : (2 : ℕ) • t0 = 0 := by
    decide
  have hT_two : (2 : ℕ) • f t0 = 0 := by
    rw [← f.map_nsmul, ht0_two, map_zero]
  have ht0_ne_zero : t0 ≠ 0 := by
    decide
  have hT_ne_zero : f t0 ≠ 0 := by
    intro h
    exact ht0_ne_zero (hf (by simpa using h))
  have hp6_eq : (6 : ℕ) • p0 = p6 := by
    decide
  have h6P_eq : (6 : ℕ) • f p0 = f p6 := by
    rw [← f.map_nsmul, hp6_eq]
  have hp6_ne_zero : p6 ≠ 0 := by
    decide
  have h6P_ne_zero : (6 : ℕ) • f p0 ≠ 0 := by
    intro h
    rw [h6P_eq] at h
    exact hp6_ne_zero (hf (by simpa using h))
  have hp6_two : (2 : ℕ) • p6 = 0 := by
    decide
  have h6P_two : (2 : ℕ) • ((6 : ℕ) • f p0) = 0 := by
    rw [h6P_eq, ← f.map_nsmul, hp6_two, map_zero]
  have ht0_ne_p6 : t0 ≠ p6 := by
    decide
  have hT_ne_6P : f t0 ≠ (6 : ℕ) • f p0 := by
    intro h
    rw [h6P_eq] at h
    exact ht0_ne_p6 (hf h)
  simpa [p0, t0, p6] using
    And.intro hP_order <|
      And.intro hT_two <|
      And.intro hT_ne_zero <|
      And.intro h6P_eq <|
      And.intro h6P_ne_zero <|
      And.intro h6P_two hT_ne_6P

private noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private lemma pointCurveEqAddEquiv_some
    {W W' : WeierstrassCurve ℚ} (h : W = W') {x y : ℚ}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    pointCurveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst h
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

theorem exists_tate_normalized_order12_coordinate_data
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point)
    (hP : addOrderOf P = 12)
    (hT2 : (2 : ℕ) • T = 0)
    (hTne0 : T ≠ 0)
    (h6Pne0 : (6 : ℕ) • P ≠ 0)
    (h6P2 : (2 : ℕ) • ((6 : ℕ) • P) = 0)
    (hTne6P : T ≠ (6 : ℕ) • P) :
    ∃ b c xT yT : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
      ∃ hT : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) xT yT,
      ∃ h6 : WeierstrassCurve.Affine.Nonsingular
          (tateNormalFormCurve b c) (tateX6 b c) (tateY6 b c),
        b ≠ 0 ∧ c ≠ 0 ∧ b - c ≠ 0 ∧ b - c ^ 2 - c ≠ 0 ∧
          (2 : ℕ) •
              (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0 ∧
          (2 : ℕ) •
              (WeierstrassCurve.Affine.Point.some (tateX6 b c) (tateY6 b c) h6 :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0 ∧
          (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) ≠
            WeierstrassCurve.Affine.Point.some (tateX6 b c) (tateY6 b c) h6 := by
  let Psmall :
      ∀ m < 12, 0 < m → (m : ℕ) • P ≠ 0 :=
    ((addOrderOf_eq_iff (x := P) (by norm_num : 0 < 12)).mp hP).2
  cases P with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hP
      norm_num at hP
  | some x₀ y₀ hPaff =>
      let hPaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        change WeierstrassCurve.Affine.Nonsingular (E⁄ℚ) x₀ y₀
        exact hPaff
      let P₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hPaffE
      have hP₀_order : addOrderOf P₀ = 12 := by
        dsimp [P₀, hPaffE]
        change addOrderOf (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff) = 12
        exact hP
      let Psmall₀ :
          ∀ m < 12, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by norm_num : 0 < 12)).mp hP₀_order).2
      have h6P2₀ : (2 : ℕ) • ((6 : ℕ) • P₀) = 0 := by
        dsimp [P₀, hPaffE]
        change (2 : ℕ) • ((6 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff : (E⁄ℚ).Point)) = 0
        exact h6P2
      have hTne6P₀ : T ≠ (6 : ℕ) • P₀ := by
        intro h
        apply hTne6P
        dsimp [P₀, hPaffE] at h
        exact h
      let T₀ : WeierstrassCurve.Affine.Point E := T
      have hT2₀ : (2 : ℕ) • T₀ = 0 := by
        change (2 : ℕ) • (T : WeierstrassCurve.Affine.Point E) = 0
        simpa using hT2
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden0
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h2zero : (2 : ℕ) • P₀ = 0 := by
          simpa [P₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hPaff) hy)
        exact Psmall₀ 2 (by norm_num) (by norm_num) h2zero
      let C0 := translateToOriginTangent E x₀ y₀
      let W1 : WeierstrassCurve ℚ := C0 • E
      haveI : W1.IsElliptic := by
        dsimp [W1]
        infer_instance
      let φ0 : WeierstrassCurve.Affine.Point E ≃+
          WeierstrassCurve.Affine.Point W1 := by
        dsimp [W1]
        exact variableChangePointAddEquiv E C0
      have hW1a₆ : W1.a₆ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₆_eq_zero E (x₀ := x₀) (y₀ := y₀) hPaffE.1
      have hW1a₄ : W1.a₄ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₄_eq_zero E (x₀ := x₀) (y₀ := y₀) hden
      have hW1a₃_formula : W1.a₃ = E.a₃ + E.a₁ * x₀ + 2 * y₀ := by
        simp [W1, C0]
      have hW1a₃_ne : W1.a₃ ≠ 0 := by
        rw [hW1a₃_formula]
        intro h
        apply hden
        linarith
      have hW1origin : WeierstrassCurve.Affine.Nonsingular W1 0 0 := by
        apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        rw [WeierstrassCurve.Affine.equation_iff]
        simp [hW1a₆]
      have hφ0P_origin :
          φ0 P₀ = WeierstrassCurve.Affine.Point.some 0 0 hW1origin := by
        change variableChangePointMap E C0 P₀ =
          WeierstrassCurve.Affine.Point.some 0 0 hW1origin
        dsimp [variableChangePointMap, P₀]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor <;>
          simp [C0, variableChangePointX,
            variableChangePointY, translateToOriginTangent]
      have hW1a₂_ne : W1.a₂ ≠ 0 := by
        intro hW1a₂
        have h3zero_origin :
            (3 : ℕ) •
                (WeierstrassCurve.Affine.Point.some 0 0 hW1origin :
                  WeierstrassCurve.Affine.Point W1) = 0 :=
          origin_three_nsmul_eq_zero_of_a2_eq_zero W1 hW1a₂ hW1a₃_ne hW1a₄ hW1a₆
        have h3zero_map : (3 : ℕ) • φ0 P₀ = 0 := by
          simpa [hφ0P_origin] using h3zero_origin
        have h3zero : (3 : ℕ) • P₀ = 0 := by
          apply (EquivLike.injective φ0)
          rw [map_nsmul, h3zero_map, map_zero]
        exact Psmall₀ 3 (by norm_num) (by norm_num) h3zero
      let ρ : ℚ := W1.a₃ / W1.a₂
      have hρ : ρ ≠ 0 := div_ne_zero hW1a₃_ne hW1a₂_ne
      let C1 := scaleByRho ρ hρ
      let b : ℚ := tateBFromCoefficients W1.a₂ W1.a₃
      let c : ℚ := tateCFromCoefficients W1.a₁ W1.a₂ W1.a₃
      have hW2eq : C1 • W1 = tateNormalFormCurve b c := by
        ext <;> dsimp [C1, ρ, b, c, tateNormalFormCurve,
          tateBFromCoefficients, tateCFromCoefficients]
        · rw [WeierstrassCurve.variableChange_a₁]
          simp [scaleByRho]
          field_simp [hW1a₂_ne, hW1a₃_ne]
        · rw [scaleByTateRho_a₂ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · rw [scaleByTateRho_a₃ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · simp [WeierstrassCurve.variableChange_a₄, scaleByRho, hW1a₄]
        · simp [WeierstrassCurve.variableChange_a₆, scaleByRho, hW1a₆]
      haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := by
        rw [← hW2eq]
        infer_instance
      let φ1raw : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (C1 • W1) :=
        variableChangePointAddEquiv W1 C1
      let φ1 : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
        φ1raw.trans (pointCurveEqAddEquiv hW2eq)
      have hφ1φ0P_origin :
          φ1 (φ0 P₀) = tateOriginPoint b c := by
        rw [hφ0P_origin]
        have hRawOrigin : WeierstrassCurve.Affine.Nonsingular (C1 • W1) 0 0 := by
          simpa [hW2eq] using tate_origin_nonsingular b c
        have hφ1raw_origin :
            φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
              WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin := by
          change variableChangePointMap W1 C1
              (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
            WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin
          dsimp [variableChangePointMap]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor <;>
            simp [C1, variableChangePointX, variableChangePointY,
              scaleByRho]
        change (pointCurveEqAddEquiv hW2eq)
            (φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin)) =
          tateOriginPoint b c
        rw [hφ1raw_origin]
        exact pointCurveEqAddEquiv_some hW2eq
      have hOriginOrder : addOrderOf (tateOriginPoint b c) = 12 := by
        have hmaporder : addOrderOf (φ1 (φ0 P₀)) = 12 := by
          calc
            addOrderOf (φ1 (φ0 P₀)) = addOrderOf (φ0 P₀) :=
              addOrderOf_injective φ1.toAddMonoidHom (EquivLike.injective φ1) (φ0 P₀)
            _ = addOrderOf P₀ :=
              addOrderOf_injective φ0.toAddMonoidHom (EquivLike.injective φ0) P₀
            _ = 12 := hP₀_order
        rw [hφ1φ0P_origin] at hmaporder
        exact hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W1.a₂ ^ 3 / W1.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW1a₂_ne) (pow_ne_zero 2 hW1a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      have hOriginSmall :
          ∀ m < 12, 0 < m → (m : ℕ) • tateOriginPoint b c ≠ 0 :=
        ((addOrderOf_eq_iff (x := tateOriginPoint b c) (by norm_num : 0 < 12)).mp
          hOriginOrder).2
      have hc : c ≠ 0 := by
        intro hc0
        exact hOriginSmall 4 (by norm_num) (by norm_num)
          (tate_fourP_eq_zero_of_c_eq_zero b c hb hc0)
      have hbc : b - c ≠ 0 := by
        intro hbc0
        exact hOriginSmall 5 (by norm_num) (by norm_num)
          (tate_fiveP_eq_zero_of_b_eq_c b c hb (sub_eq_zero.mp hbc0))
      have hD : b - c ^ 2 - c ≠ 0 := by
        intro hD0
        exact hOriginSmall 6 (by norm_num) (by norm_num)
          (tate_sixP_eq_zero_of_b_sub_c_sq_sub_c_eq_zero b c hb hc hbc hD0)
      rcases tate_sixP_eq b c hb hc hbc hD with ⟨h6, h6eq⟩
      have hT2map : (2 : ℕ) • φ1 (φ0 T₀) = 0 := by
        calc
          (2 : ℕ) • φ1 (φ0 T₀) = φ1 ((2 : ℕ) • φ0 T₀) :=
            (map_nsmul φ1 2 (φ0 T₀)).symm
          _ = φ1 (φ0 ((2 : ℕ) • T₀)) := by
            rw [← map_nsmul φ0 2 T₀]
          _ = 0 := by
            rw [hT2₀, map_zero, map_zero]
      have h6two_origin : (2 : ℕ) • ((6 : ℕ) • tateOriginPoint b c) = 0 := by
        rw [← hφ1φ0P_origin]
        rw [← map_nsmul φ1 6 (φ0 P₀)]
        rw [← map_nsmul φ1 2 ((6 : ℕ) • φ0 P₀)]
        rw [← map_nsmul φ0 6 P₀]
        rw [← map_nsmul φ0 2 ((6 : ℕ) • P₀)]
        rw [h6P2₀, map_zero, map_zero]
      have hTmap_ne0 : φ1 (φ0 T₀) ≠ 0 := by
        intro hT0
        have hφ0T0 : φ0 T₀ = 0 := by
          apply (EquivLike.injective φ1)
          simpa [map_zero] using hT0
        have hT₀0 : T₀ = 0 := by
          apply (EquivLike.injective φ0)
          simpa [map_zero] using hφ0T0
        apply hTne0
        exact hT₀0
      have hTmap_ne6 : φ1 (φ0 T₀) ≠ (6 : ℕ) • tateOriginPoint b c := by
        intro hT6
        apply hTne6P₀
        change T₀ = (6 : ℕ) • P₀
        apply (EquivLike.injective φ0)
        apply (EquivLike.injective φ1)
        rw [map_nsmul φ0, map_nsmul φ1, hφ1φ0P_origin]
        exact hT6
      cases hTpoint : φ1 (φ0 T₀) with
      | zero =>
          exact False.elim (hTmap_ne0 hTpoint)
      | some xT yT hT =>
          refine ⟨b, c, xT, yT, inferInstance, hT, h6, hb, hc, hbc, hD, ?_, ?_, ?_⟩
          · simpa [hTpoint] using hT2map
          · rw [← h6eq]
            exact h6two_origin
          · intro hsame
            apply hTmap_ne6
            rw [hTpoint, h6eq]
            exact hsame

theorem exists_tate_parameters_of_order12_and_independent_2torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point)
    (hP : addOrderOf P = 12)
    (hT2 : (2 : ℕ) • T = 0)
    (hTne0 : T ≠ 0)
    (h6Pne0 : (6 : ℕ) • P ≠ 0)
    (h6P2 : (2 : ℕ) • ((6 : ℕ) • P) = 0)
    (hTne6P : T ≠ (6 : ℕ) • P) :
    ∃ b c xT : ℚ,
      b ≠ 0 ∧ c ≠ 0 ∧ b - c ≠ 0 ∧ b - c ^ 2 - c ≠ 0 ∧
        Phi12 b c = 0 ∧
        tateTwoTorsionCubic b c xT = 0 ∧ xT ≠ tateX6 b c := by
  rcases exists_tate_normalized_order12_coordinate_data
      E P T hP hT2 hTne0 h6Pne0 h6P2 hTne6P with
    ⟨b, c, xT, yT, hEll, hT, h6, hb, hc, hbc, hD, hT2', h6P2', hne⟩
  haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := hEll
  have h6rel : 2 * tateY6 b c + (1 - c) * tateX6 b c - b = 0 :=
    tate_linear_relation_of_two_torsion
      (b := b) (c := c) (x := tateX6 b c) (y := tateY6 b c) (h := h6) h6P2'
  refine ⟨b, c, xT, hb, hc, hbc, hD, ?_, ?_, ?_⟩
  · exact Phi12_of_tate_6P_twoTorsion b c hc hD h6rel
  · exact tate_cubic_of_two_torsion
      (b := b) (c := c) (x := xT) (y := yT) (h := hT) hT2'
  · exact tate_two_torsion_x_ne_of_point_ne
      (b := b) (c := c) (x₁ := xT) (y₁ := yT)
      (x₂ := tateX6 b c) (y₂ := tateY6 b c)
      (h₁ := hT) (h₂ := h6) hT2' h6P2' hne

/-! ## The explicit map to the `N = 12` obstruction curve -/

def R12 (q t : ℚ) : ℚ :=
  -q ^ 8 * t ^ 3
    + 24 * q ^ 6 * t ^ 3
    + 88 * q ^ 5 * t ^ 2
    + 22 * q ^ 4 * t ^ 3
    + 128 * q ^ 4 * t
    + 80 * q ^ 3 * t ^ 2
    + 64 * q ^ 3
    + 16 * q ^ 2 * t ^ 3
    + 64 * q ^ 2 * t
    + 24 * q * t ^ 2
    + 3 * t ^ 3

def K12 (q t : ℚ) : ℚ :=
  q ^ 4 * t + 4 * q ^ 3 + 6 * q ^ 2 * t + 4 * q + t

def q12 (b c x : ℚ) : ℚ :=
  c * x / (x - b)

def t12 (b c x : ℚ) : ℚ :=
  b * (b - x) / (-b ^ 2 + 2 * b * x + (c - 1) * x ^ 2)

def A12 (q t : ℚ) : ℚ :=
  4 * q + t * (3 * q ^ 2 + 1)

def B12 (q t : ℚ) : ℚ :=
  t * (q ^ 2 - 1)

def uN12 (b c x : ℚ) : ℚ :=
  let q := q12 b c x
  let t := t12 b c x
  let A := A12 q t
  let B := B12 q t
  (A ^ 2 + B ^ 2) / (A * B)

def wN12 (b c x : ℚ) : ℚ :=
  let q := q12 b c x
  let t := t12 b c x
  let A := A12 q t
  let B := B12 q t
  q * (A ^ 2 - B ^ 2) / A ^ 2

lemma N12_target_identity
    (q t : ℚ)
    (hA : A12 q t ≠ 0) (hB : B12 q t ≠ 0) :
    let A := A12 q t
    let B := B12 q t
    let u := (A ^ 2 + B ^ 2) / (A * B)
    let w := q * (A ^ 2 - B ^ 2) / A ^ 2
    w ^ 2 - (u ^ 3 - u ^ 2 - 4 * u + 4)
      =
    - ((A - B) ^ 2 * (A + B) ^ 2 * R12 q t) / (A ^ 4 * B ^ 3) := by
  field_simp [A12, B12, R12, hA, hB]
  simp only [A12, B12, R12]
  ring_nf

lemma E_N12_point_of_R12
    (q t : ℚ)
    (hA : A12 q t ≠ 0) (hB : B12 q t ≠ 0)
    (hR : R12 q t = 0) :
    let A := A12 q t
    let B := B12 q t
    let u := (A ^ 2 + B ^ 2) / (A * B)
    let w := q * (A ^ 2 - B ^ 2) / A ^ 2
    w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := by
  have h := N12_target_identity q t hA hB
  dsimp at h ⊢
  rw [hR, mul_zero] at h
  norm_num at h
  nlinarith

lemma tate_two_torsion_x_ne_zero
    {b c x : ℚ}
    (hb : b ≠ 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    x ≠ 0 := by
  intro hx
  rw [hx] at hroot
  unfold tateTwoTorsionCubic at hroot
  simp at hroot
  exact hb hroot

lemma tate_two_torsion_x_ne_b
    {b c x : ℚ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    x - b ≠ 0 := by
  intro hxb
  have hx : x = b := sub_eq_zero.mp hxb
  rw [hx] at hroot
  unfold tateTwoTorsionCubic at hroot
  ring_nf at hroot
  exact (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hc)) hroot

end

end Scratch.TateZ2xZ12Reduction
