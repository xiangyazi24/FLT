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
open Polynomial

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

lemma tate_two_torsion_b_add_cx_sub_x_ne_zero
    {b c x : ℚ}
    (hc : c ≠ 0) (hx : x ≠ 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    b + c * x - x ≠ 0 := by
  intro hF
  unfold tateTwoTorsionCubic at hroot
  ring_nf at hroot
  have hcx3 : c * x ^ 3 = 0 := by
    nlinarith
  exact (mul_ne_zero hc (pow_ne_zero 3 hx)) hcx3

private def N12den (b c x : ℚ) : ℚ :=
  -b ^ 2 + 2 * b * x + (c - 1) * x ^ 2

private def N12J (b c : ℚ) : ℚ :=
  16 * b ^ 2 - 8 * b * c ^ 2 - 24 * b * c + c ^ 4 - 3 * c ^ 3 + 3 * c ^ 2 - c

private def N12P1 (c : ℚ) : ℚ :=
  c ^ 2 + 6 * c + 1

private def N12P2 (c : ℚ) : ℚ :=
  c ^ 4 - 24 * c ^ 3 - 22 * c ^ 2 - 16 * c - 3

private lemma N12P1_ne_zero (c : ℚ) : N12P1 c ≠ 0 := by
  intro h
  have h' : c ^ 2 + 6 * c + 1 = 0 := by
    simpa [N12P1] using h
  let p : ℤ[X] := X ^ 2 + C 6 * X + C 1
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval c p = 0 := by
    simp [p, aeval_def]
    ring_nf at h' ⊢
    exact h'
  rcases exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot with
    ⟨z, hcz, hzdiv⟩
  have hzdiv1 : z ∣ (1 : ℤ) := by
    simpa [p] using hzdiv
  have hunit : IsUnit z := isUnit_of_dvd_one hzdiv1
  rcases Int.isUnit_iff.mp hunit with hz | hz
  · rw [hcz, hz] at h
    norm_num [N12P1] at h
  · rw [hcz, hz] at h
    norm_num [N12P1] at h

private lemma N12P2_ne_zero (c : ℚ) : N12P2 c ≠ 0 := by
  intro h
  have h' : c ^ 4 - 24 * c ^ 3 - 22 * c ^ 2 - 16 * c - 3 = 0 := by
    simpa [N12P2] using h
  let p : ℤ[X] := X ^ 4 - C 24 * X ^ 3 - C 22 * X ^ 2 - C 16 * X - C 3
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval c p = 0 := by
    simp [p, aeval_def]
    ring_nf at h' ⊢
    exact h'
  rcases exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot with
    ⟨z, hcz, hzdiv⟩
  have hzdiv3 : z ∣ (-3 : ℤ) := by
    simpa [p] using hzdiv
  have hzabs : z.natAbs ∣ 3 := (Int.natAbs_dvd_natAbs).mpr hzdiv3
  have hzabs_cases : z.natAbs = 1 ∨ z.natAbs = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hzabs
  have hzcases : z = 1 ∨ z = -1 ∨ z = 3 ∨ z = -3 := by
    rcases hzabs_cases with h1 | h3
    · have hsq : z ^ 2 = (1 : ℤ) ^ 2 :=
        Int.natAbs_eq_iff_sq_eq.mp (by simpa using h1)
      have hzsq : z ^ 2 = 1 := by
        simpa using hsq
      rw [sq_eq_one_iff] at hzsq
      rcases hzsq with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl hz)
    · have hsq : z ^ 2 = (3 : ℤ) ^ 2 :=
        Int.natAbs_eq_iff_sq_eq.mp (by simpa using h3)
      have hzsq : z ^ 2 = 9 := by
        simpa using hsq
      have hzmod :
          z % 7 = 0 ∨ z % 7 = 1 ∨ z % 7 = 2 ∨ z % 7 = 3 ∨
            z % 7 = 4 ∨ z % 7 = 5 ∨ z % 7 = 6 := by
        omega
      omega
  rcases hzcases with hz | hz | hz | hz <;>
    rw [hcz, hz] at h <;>
    norm_num [N12P2] at h

private lemma N12J_of_root_and_den_zero
    {b c x : ℚ}
    (hroot : tateTwoTorsionCubic b c x = 0)
    (hden : N12den b c x = 0) :
    b ^ 2 * c * N12J b c = 0 := by
  unfold tateTwoTorsionCubic at hroot
  unfold N12den at hden
  unfold N12J
  ring_nf at hroot hden ⊢
  linear_combination
    (-4 * b * c ^ 2 - 24 * b * c - 4 * b + c ^ 4 - 3 * c ^ 3
      - 12 * c ^ 2 * x + 3 * c ^ 2 + 8 * c * x - c + 4 * x) * hroot +
    (-16 * b ^ 2 * c + 8 * b * c ^ 3 + 20 * b * c ^ 2 - 32 * b * c * x
      - 24 * b * c - 4 * b - c ^ 5 + 4 * c ^ 4 + 8 * c ^ 3 * x
      - 6 * c ^ 3 - 12 * c ^ 2 * x + 4 * c ^ 2 + 48 * c * x ^ 2 - c
      + 16 * x ^ 2 + 4 * x) * hden

private lemma N12P1P2_of_Phi_and_J
    {b c : ℚ}
    (hPhi : Phi12 b c = 0)
    (hJ : N12J b c = 0) :
    c ^ 2 * N12P1 c * N12P2 c = 0 := by
  unfold Phi12 at hPhi
  unfold N12J at hJ
  unfold N12P1 N12P2
  ring_nf at hPhi hJ ⊢
  linear_combination
    (-256) * hPhi +
    (48 * b ^ 2 + 8 * b * c ^ 2 - 72 * b * c + c ^ 4 - 15 * c ^ 3
      + 43 * c ^ 2 + 3 * c) * hJ

private lemma N12den_ne_zero
    {b c x : ℚ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hPhi : Phi12 b c = 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    N12den b c x ≠ 0 := by
  intro hden
  have hJprod : b ^ 2 * c * N12J b c = 0 :=
    N12J_of_root_and_den_zero hroot hden
  have hb2c : b ^ 2 * c ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hb) hc
  have hJ : N12J b c = 0 :=
    (mul_eq_zero.mp hJprod).resolve_left hb2c
  have hprod : c ^ 2 * N12P1 c * N12P2 c = 0 :=
    N12P1P2_of_Phi_and_J hPhi hJ
  rcases mul_eq_zero.mp hprod with hc2p1 | hp2
  · rcases mul_eq_zero.mp hc2p1 with hc2 | hp1
    · exact (pow_ne_zero 2 hc) hc2
    · exact N12P1_ne_zero c hp1
  · exact N12P2_ne_zero c hp2

private lemma q12_sub_one_eq
    {b c x : ℚ}
    (hxb : x - b ≠ 0) :
    q12 b c x - 1 = (b + c * x - x) / (x - b) := by
  unfold q12
  field_simp [hxb]
  ring

private lemma t12_add_one_eq
    {b c x : ℚ}
    (hden : N12den b c x ≠ 0) :
    t12 b c x + 1 = x * (b + c * x - x) / N12den b c x := by
  have hone : (1 : ℚ) = N12den b c x / N12den b c x := by
    rw [div_self hden]
  calc
    t12 b c x + 1 =
        b * (b - x) / N12den b c x + N12den b c x / N12den b c x := by
      rw [hone]
      rfl
    _ = (b * (b - x) + N12den b c x) / N12den b c x := by
      rw [add_div]
    _ = x * (b + c * x - x) / N12den b c x := by
      congr 1
      unfold N12den
      ring

private lemma q12_mul_t12_add_one_eq
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hden : N12den b c x ≠ 0) :
    q12 b c x * t12 b c x + 1 =
      (x - b) * (b + c * x - x) / N12den b c x := by
  have hqt : q12 b c x * t12 b c x = -(b * c * x) / N12den b c x := by
    unfold q12 t12 N12den
    field_simp [hxb]
    ring
  have hone : (1 : ℚ) = N12den b c x / N12den b c x := by
    rw [div_self hden]
  calc
    q12 b c x * t12 b c x + 1 =
        -(b * c * x) / N12den b c x + N12den b c x / N12den b c x := by
      rw [hqt, hone]
    _ = (-(b * c * x) + N12den b c x) / N12den b c x := by
      rw [add_div]
    _ = (x - b) * (b + c * x - x) / N12den b c x := by
      congr 1
      unfold N12den
      ring

private lemma q12_ne_zero
    {b c x : ℚ}
    (hc : c ≠ 0) (hx : x ≠ 0) (hxb : x - b ≠ 0) :
    q12 b c x ≠ 0 := by
  unfold q12
  exact div_ne_zero (mul_ne_zero hc hx) hxb

private lemma q12_ne_one
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hF : b + c * x - x ≠ 0) :
    q12 b c x ≠ 1 := by
  intro hq
  have hsub := q12_sub_one_eq (b := b) (c := c) (x := x) hxb
  rw [hq] at hsub
  norm_num at hsub
  have hdiv : (b + c * x - x) / (x - b) = 0 := by
    exact hsub.symm
  rcases div_eq_zero_iff.mp hdiv with hnum | hden0
  · exact hF hnum
  · exact hxb hden0

private lemma q12_ne_neg_one
    {b c x : ℚ}
    (hc : c ≠ 0) (hx : x ≠ 0) (hxb : x - b ≠ 0)
    (hPhi : Phi12 b c = 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    q12 b c x ≠ -1 := by
  intro hq
  have hg : -b + c * x + x = 0 := by
    unfold q12 at hq
    field_simp [hxb] at hq
    nlinarith
  have hbexpr : b = (c + 1) * x := by
    nlinarith
  have hx_eq_c : x = c := by
    have hroot' := hroot
    unfold tateTwoTorsionCubic at hroot'
    rw [hbexpr] at hroot'
    ring_nf at hroot'
    have hprod : c * x ^ 2 * (x - c) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hcx2 | hxc
    · rcases mul_eq_zero.mp hcx2 with hc0 | hx20
      · exact False.elim (hc hc0)
      · exact False.elim ((pow_ne_zero 2 hx) hx20)
    · exact sub_eq_zero.mp hxc
  have hPhi' := hPhi
  rw [hbexpr, hx_eq_c] at hPhi'
  unfold Phi12 at hPhi'
  ring_nf at hPhi'
  have hc8 : c ^ 8 = 0 := by
    nlinarith
  exact (pow_ne_zero 8 hc) hc8

private lemma t12_add_one_ne_zero
    {b c x : ℚ}
    (hx : x ≠ 0) (hF : b + c * x - x ≠ 0)
    (hden : N12den b c x ≠ 0) :
    t12 b c x + 1 ≠ 0 := by
  rw [t12_add_one_eq (b := b) (c := c) (x := x) hden]
  exact div_ne_zero (mul_ne_zero hx hF) hden

private lemma q12_mul_t12_add_one_ne_zero
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hF : b + c * x - x ≠ 0)
    (hden : N12den b c x ≠ 0) :
    q12 b c x * t12 b c x + 1 ≠ 0 := by
  rw [q12_mul_t12_add_one_eq (b := b) (c := c) (x := x) hxb hden]
  exact div_ne_zero (mul_ne_zero hxb hF) hden

private lemma t12_ne_zero
    {b c x : ℚ}
    (hb : b ≠ 0) (hxb : x - b ≠ 0) (hden : N12den b c x ≠ 0) :
    t12 b c x ≠ 0 := by
  have hbx : b - x ≠ 0 := by
    intro h
    apply hxb
    linarith
  unfold t12 N12den at *
  exact div_ne_zero (mul_ne_zero hb hbx) hden

private def bQT (q t : ℚ) : ℚ :=
  t * (q - 1) ^ 3 * (q * t + 1) / (4 * (t + 1) ^ 2)

private def cQT (q t : ℚ) : ℚ :=
  q * (q * t + 1) / (t + 1)

private def xQT (q t : ℚ) : ℚ :=
  -((q - 1) ^ 2 * (q * t + 1)) / (4 * (t + 1))

private lemma bQT_simpl_field
    {b x F D : ℚ}
    (hxb : x - b ≠ 0) (hD : D ≠ 0) (hx : x ≠ 0) (hF : F ≠ 0) :
    (b * (b - x) / D) * (F / (x - b)) ^ 3 * ((x - b) * F / D) /
        (4 * (x * F / D) ^ 2)
      =
    -b * F ^ 2 / (4 * x ^ 2 * (x - b)) := by
  field_simp [hxb, hD, hx, hF]
  ring

private lemma cQT_simpl_field
    {b c x F D : ℚ}
    (hxb : x - b ≠ 0) (hD : D ≠ 0) (hx : x ≠ 0) (hF : F ≠ 0) :
    (c * x / (x - b)) * ((x - b) * F / D) / (x * F / D) = c := by
  field_simp [hxb, hD, hx, hF]

private lemma xQT_simpl_field
    {b x F D : ℚ}
    (hxb : x - b ≠ 0) (hD : D ≠ 0) (hx : x ≠ 0) (hF : F ≠ 0) :
    -((F / (x - b)) ^ 2 * ((x - b) * F / D)) / (4 * (x * F / D))
      =
    -F ^ 2 / (4 * x * (x - b)) := by
  field_simp [hxb, hD, hx, hF]

private lemma b_eq_bQT_q12_t12
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hden : N12den b c x ≠ 0)
    (hx : x ≠ 0) (hF : b + c * x - x ≠ 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    b = bQT (q12 b c x) (t12 b c x) := by
  have hq1 := q12_sub_one_eq (b := b) (c := c) (x := x) hxb
  have ht := t12_add_one_eq (b := b) (c := c) (x := x) hden
  have hqt := q12_mul_t12_add_one_eq (b := b) (c := c) (x := x) hxb hden
  have hs :
      bQT (q12 b c x) (t12 b c x) =
        -b * (b + c * x - x) ^ 2 / (4 * x ^ 2 * (x - b)) := by
    unfold bQT
    rw [hq1, hqt, ht]
    unfold t12
    simpa [N12den] using
      (bQT_simpl_field
        (b := b) (x := x) (F := b + c * x - x) (D := N12den b c x)
        hxb hden hx hF)
  have hback :
      -b * (b + c * x - x) ^ 2 / (4 * x ^ 2 * (x - b)) = b := by
    field_simp [hx, hxb]
    unfold tateTwoTorsionCubic at hroot
    ring_nf at hroot ⊢
    linear_combination (-b) * hroot
  exact (hs.trans hback).symm

private lemma c_eq_cQT_q12_t12
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hden : N12den b c x ≠ 0)
    (hx : x ≠ 0) (hF : b + c * x - x ≠ 0) :
    c = cQT (q12 b c x) (t12 b c x) := by
  have ht := t12_add_one_eq (b := b) (c := c) (x := x) hden
  have hqt := q12_mul_t12_add_one_eq (b := b) (c := c) (x := x) hxb hden
  unfold cQT
  rw [hqt, ht]
  exact
    (cQT_simpl_field
      (b := b) (c := c) (x := x) (F := b + c * x - x) (D := N12den b c x)
      hxb hden hx hF).symm

private lemma x_eq_xQT_q12_t12
    {b c x : ℚ}
    (hxb : x - b ≠ 0) (hden : N12den b c x ≠ 0)
    (hx : x ≠ 0) (hF : b + c * x - x ≠ 0)
    (hroot : tateTwoTorsionCubic b c x = 0) :
    x = xQT (q12 b c x) (t12 b c x) := by
  have hq1 := q12_sub_one_eq (b := b) (c := c) (x := x) hxb
  have ht := t12_add_one_eq (b := b) (c := c) (x := x) hden
  have hqt := q12_mul_t12_add_one_eq (b := b) (c := c) (x := x) hxb hden
  have hs :
      xQT (q12 b c x) (t12 b c x) =
        -(b + c * x - x) ^ 2 / (4 * x * (x - b)) := by
    unfold xQT
    rw [hq1, hqt, ht]
    simpa using
      (xQT_simpl_field
        (b := b) (x := x) (F := b + c * x - x) (D := N12den b c x)
        hxb hden hx hF)
  have hback :
      -(b + c * x - x) ^ 2 / (4 * x * (x - b)) = x := by
    field_simp [hx, hxb]
    unfold tateTwoTorsionCubic at hroot
    ring_nf at hroot ⊢
    linear_combination (-1) * hroot
  exact (hs.trans hback).symm

private lemma Phi12_bQT_cQT
    (q t : ℚ) (ht1 : t + 1 ≠ 0) :
    Phi12 (bQT q t) (cQT q t) =
      ((q * t + 1) ^ 4 * R12 q t * K12 q t) / (256 * (t + 1) ^ 8) := by
  unfold Phi12 bQT cQT R12 K12
  field_simp [ht1]
  ring

private lemma D_bQT_cQT
    (q t : ℚ) (ht1 : t + 1 ≠ 0) :
    bQT q t - cQT q t ^ 2 - cQT q t =
      -((q + 1) * (q * t + 1) * A12 q t) / (4 * (t + 1) ^ 2) := by
  unfold bQT cQT A12
  field_simp [ht1]
  ring

private def N12P1qt (q t : ℚ) : ℚ :=
  q ^ 3 * t - 3 * q ^ 2 * t - q * t - 4 * q - t

private def N12P2qt (q t : ℚ) : ℚ :=
  q ^ 6 * t ^ 2 - 6 * q ^ 5 * t ^ 2 - 5 * q ^ 4 * t ^ 2 - 20 * q ^ 4 * t
    - 8 * q ^ 3 * t ^ 2 - 4 * q ^ 3 * t - 16 * q ^ 3 + 3 * q ^ 2 * t ^ 2
    - 12 * q ^ 2 * t - 2 * q * t ^ 2 + 4 * q * t + t ^ 2

private lemma bQT_sub_cQT
    (q t : ℚ) (ht1 : t + 1 ≠ 0) :
    bQT q t - cQT q t =
      (q * t + 1) * N12P1qt q t / (4 * (t + 1) ^ 2) := by
  unfold bQT cQT N12P1qt
  field_simp [ht1]
  ring

private lemma bQT_num2
    (q t : ℚ) (ht1 : t + 1 ≠ 0) :
    (bQT q t) ^ 2 - bQT q t * cQT q t - (cQT q t) ^ 3 =
      (q * t + 1) ^ 2 * N12P2qt q t / (16 * (t + 1) ^ 4) := by
  unfold bQT cQT N12P2qt
  field_simp [ht1]
  ring

private lemma N12P1P2qt_identity (q t : ℚ) :
    N12P1qt q t * N12P2qt q t
      + (q - 1) ^ 2 * (q + 1) ^ 2 * (t + 1) * (A12 q t) ^ 2
      =
    (q * t + 1) * (K12 q t) ^ 2 := by
  unfold N12P1qt N12P2qt A12 K12
  ring

private lemma K12_zero_forces_xQT_eq_tateX6
    (q t : ℚ)
    (hqplus : q + 1 ≠ 0) (hqt1 : q * t + 1 ≠ 0)
    (ht1 : t + 1 ≠ 0) (hA : A12 q t ≠ 0)
    (hK : K12 q t = 0) :
    xQT q t = tateX6 (bQT q t) (cQT q t) := by
  have hpoly := N12P1P2qt_identity q t
  rw [hK] at hpoly
  norm_num at hpoly
  have hPprod :
      N12P1qt q t * N12P2qt q t =
        -((q - 1) ^ 2 * (q + 1) ^ 2 * (t + 1) * (A12 q t) ^ 2) := by
    nlinarith
  have hx6 :
      tateX6 (bQT q t) (cQT q t) =
        (q * t + 1) * N12P1qt q t * N12P2qt q t /
          (4 * (q + 1) ^ 2 * (t + 1) ^ 2 * (A12 q t) ^ 2) := by
    unfold tateX6
    rw [bQT_sub_cQT q t ht1, bQT_num2 q t ht1, D_bQT_cQT q t ht1]
    field_simp [hqplus, hqt1, ht1, hA]
    ring
  rw [hx6]
  rw [show (q * t + 1) * N12P1qt q t * N12P2qt q t =
      (q * t + 1) * (N12P1qt q t * N12P2qt q t) by ring]
  rw [hPprod]
  unfold xQT
  field_simp [hqplus, hqt1, ht1, hA]

private lemma rat_sq_ne_three (r : ℚ) : r ^ 2 ≠ 3 := by
  intro h
  have hs : IsSquare (3 : ℚ) := ⟨r, by simpa [sq] using h.symm⟩
  have hs_nat : IsSquare (3 : ℕ) :=
    Rat.isSquare_natCast_iff.mp (by simpa using hs)
  norm_num [IsSquare] at hs_nat

private lemma N12_u_two_false
    {q t : ℚ}
    (hR : R12 q t = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqm1 : q ≠ -1)
    (hrel : q ^ 2 * t + 2 * q + t = 0) :
    False := by
  have hq2 : q ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg q]
  have ht : t = -2 * q / (q ^ 2 + 1) := by
    field_simp [hq2] at hrel ⊢
    linarith
  rw [ht] at hR
  unfold R12 at hR
  field_simp [hq2] at hR
  ring_nf at hR
  have hprod : q ^ 3 * (q - 1) ^ 4 * (q + 1) ^ 4 = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hleft | hplus
  · rcases mul_eq_zero.mp hleft with hq3 | hq1p
    · exact (pow_ne_zero 3 hq0) hq3
    · have hq1sub : q - 1 ≠ 0 := by
        intro h
        exact hq1 (sub_eq_zero.mp h)
      exact (pow_ne_zero 4 hq1sub) hq1p
  · have hqplus_ne : q + 1 ≠ 0 := by
      intro h
      exact hqm1 (eq_neg_of_add_eq_zero_left h)
    exact (pow_ne_zero 4 hqplus_ne) hplus

private lemma N12_bad_u_false
    (q t : ℚ)
    (hA : A12 q t ≠ 0) (hB : B12 q t ≠ 0)
    (hR : R12 q t = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqm1 : q ≠ -1)
    (hqt1 : q * t + 1 ≠ 0) :
    let A := A12 q t
    let B := B12 q t
    let u := (A ^ 2 + B ^ 2) / (A * B)
    ¬(u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4) := by
  dsimp
  intro hbad
  rcases hbad with hneg2 | hzero | hone | htwo | hfour
  · have hsum : A12 q t + B12 q t = 0 := by
      field_simp [hA, hB] at hneg2
      nlinarith
    have hAB : A12 q t + B12 q t = 4 * q * (q * t + 1) := by
      unfold A12 B12
      ring
    rw [hAB] at hsum
    exact (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (mul_ne_zero hq0 hqt1))
      (by simpa [mul_assoc] using hsum)
  · have hrel : (A12 q t) ^ 2 + (B12 q t) ^ 2 = 0 := by
      field_simp [hA, hB] at hzero
      nlinarith
    have hAzero : A12 q t = 0 := by
      nlinarith [sq_nonneg (A12 q t), sq_nonneg (B12 q t)]
    exact hA hAzero
  · have hrel : (A12 q t) ^ 2 + (B12 q t) ^ 2 = A12 q t * B12 q t := by
      field_simp [hA, hB] at hone
      exact hone
    have hzero :
        (2 * A12 q t - B12 q t) ^ 2 + 3 * (B12 q t) ^ 2 = 0 := by
      nlinarith
    have hBzero : B12 q t = 0 := by
      nlinarith [sq_nonneg (2 * A12 q t - B12 q t), sq_nonneg (B12 q t)]
    exact hB hBzero
  · have hdiff : A12 q t - B12 q t = 0 := by
      field_simp [hA, hB] at htwo
      nlinarith
    have hrel : q ^ 2 * t + 2 * q + t = 0 := by
      unfold A12 B12 at hdiff
      nlinarith
    exact N12_u_two_false hR hq0 hq1 hqm1 hrel
  · have hsq : (A12 q t - 2 * B12 q t) ^ 2 = 3 * (B12 q t) ^ 2 := by
      field_simp [hA, hB] at hfour
      nlinarith
    have hthree : ((A12 q t - 2 * B12 q t) / B12 q t) ^ 2 = 3 := by
      field_simp [hB]
      nlinarith
    exact rat_sq_ne_three ((A12 q t - 2 * B12 q t) / B12 q t) hthree

/--
The remaining pure algebraic branch step for the `N = 12` bridge.

This is the exact residual statement after the group-law and normalization
work above: `b,c` are nondegenerate Tate parameters, `x` is the independent
two-torsion root, `Phi12` is the order-12 condition, and `x` is not the known
root `x(6P)`.  The roadmap proves this by the `q,t` map, the `R12/K12` branch
split, and finite bad-`u` eliminations.
-/
theorem N12_tate_algebra_bridge
    (b c x : ℚ)
    (hb : b ≠ 0) (hc : c ≠ 0) (_hbc : b - c ≠ 0)
    (hD : b - c ^ 2 - c ≠ 0)
    (hPhi : Phi12 b c = 0)
    (hroot : tateTwoTorsionCubic b c x = 0)
    (hxne : x ≠ tateX6 b c) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 ∧
        ¬(u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4) := by
  let q := q12 b c x
  let t := t12 b c x
  have hx : x ≠ 0 := tate_two_torsion_x_ne_zero hb hroot
  have hxb : x - b ≠ 0 := tate_two_torsion_x_ne_b hb hc hroot
  have hF : b + c * x - x ≠ 0 :=
    tate_two_torsion_b_add_cx_sub_x_ne_zero hc hx hroot
  have hden : N12den b c x ≠ 0 := N12den_ne_zero hb hc hPhi hroot
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact q12_ne_zero hc hx hxb
  have hq1 : q ≠ 1 := by
    dsimp [q]
    exact q12_ne_one hxb hF
  have hqm1 : q ≠ -1 := by
    dsimp [q]
    exact q12_ne_neg_one hc hx hxb hPhi hroot
  have hqplus : q + 1 ≠ 0 := by
    intro h
    apply hqm1
    linarith
  have ht1 : t + 1 ≠ 0 := by
    dsimp [t]
    exact t12_add_one_ne_zero hx hF hden
  have hqt1 : q * t + 1 ≠ 0 := by
    dsimp [q, t]
    exact q12_mul_t12_add_one_ne_zero hxb hF hden
  have ht0 : t ≠ 0 := by
    dsimp [t]
    exact t12_ne_zero hb hxb hden
  have hbq : b = bQT q t := by
    dsimp [q, t]
    exact b_eq_bQT_q12_t12 hxb hden hx hF hroot
  have hcq : c = cQT q t := by
    dsimp [q, t]
    exact c_eq_cQT_q12_t12 hxb hden hx hF
  have hxq : x = xQT q t := by
    dsimp [q, t]
    exact x_eq_xQT_q12_t12 hxb hden hx hF hroot
  have hA : A12 q t ≠ 0 := by
    have hDqt := D_bQT_cQT q t ht1
    rw [← hbq, ← hcq] at hDqt
    intro hAzero
    apply hD
    rw [hDqt, hAzero]
    ring
  have hB : B12 q t ≠ 0 := by
    have hq2m1 : q ^ 2 - 1 ≠ 0 := by
      intro h
      have hfac : (q - 1) * (q + 1) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfac with hqsub | hqadd
      · exact hq1 (sub_eq_zero.mp hqsub)
      · exact hqplus hqadd
    unfold B12
    exact mul_ne_zero ht0 hq2m1
  have hKne : K12 q t ≠ 0 := by
    intro hK
    have hxqt := K12_zero_forces_xQT_eq_tateX6 q t hqplus hqt1 ht1 hA hK
    apply hxne
    calc
      x = xQT q t := hxq
      _ = tateX6 (bQT q t) (cQT q t) := hxqt
      _ = tateX6 b c := by
        rw [← hbq, ← hcq]
  have hPhiqt : Phi12 (bQT q t) (cQT q t) = 0 := by
    rw [← hbq, ← hcq]
    exact hPhi
  have hfrac :
      ((q * t + 1) ^ 4 * R12 q t * K12 q t) / (256 * (t + 1) ^ 8) = 0 := by
    rw [← Phi12_bQT_cQT q t ht1]
    exact hPhiqt
  have hnum : (q * t + 1) ^ 4 * R12 q t * K12 q t = 0 := by
    have hdenom : (256 : ℚ) * (t + 1) ^ 8 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 8 ht1)
    rcases div_eq_zero_iff.mp hfrac with hnum | hdenzero
    · exact hnum
    · exact False.elim (hdenom hdenzero)
  have hRK : R12 q t * K12 q t = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hqt1)
    simpa [mul_assoc] using hnum
  have hR : R12 q t = 0 := by
    rcases mul_eq_zero.mp hRK with hR | hK
    · exact hR
    · exact False.elim (hKne hK)
  refine ⟨uN12 b c x, wN12 b c x, ?_, ?_⟩
  · have hcurve := E_N12_point_of_R12 q t hA hB hR
    simpa [uN12, wN12, q, t] using hcurve
  · have hbad := N12_bad_u_false q t hA hB hR hq0 hq1 hqm1 hqt1
    simpa [uN12, q, t] using hbad

theorem Z2xZ12_gives_non_degenerate_N12_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 ∧
        ¬(u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4) := by
  rcases hE with ⟨f, hf⟩
  let P : (E⁄ℚ).Point := f ((0 : ZMod 2), (1 : ZMod 12))
  let T : (E⁄ℚ).Point := f ((1 : ZMod 2), (0 : ZMod 12))
  have hdata :=
    injective_Z2xZ12_gives_order12_and_independent_2torsion E f hf
  dsimp only [P, T] at hdata
  rcases hdata with
    ⟨hPorder, hT2, hTne0, _h6Peq, h6Pne0, h6P2, hTne6P⟩
  rcases exists_tate_parameters_of_order12_and_independent_2torsion
      E P T hPorder hT2 hTne0 h6Pne0 h6P2 hTne6P with
    ⟨b, c, xT, hb, hc, hbc, hD, hPhi, hroot, hxne⟩
  exact N12_tate_algebra_bridge b c xT hb hc hbc hD hPhi hroot hxne

end

end Scratch.TateZ2xZ12Reduction
