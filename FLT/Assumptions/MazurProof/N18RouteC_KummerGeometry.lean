import FLT.Assumptions.MazurProof.N18RouteC_IsogenyPoints

/-!
# Direct Kummer geometry for the N18 three-isogeny

The dual Kummer value is defined on every point, including its two special
zeros.  Translation by the rational kernel points is handled by explicit
affine formulas, avoiding an abstract divisor or cohomology API.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.KummerGeometry

open Isogeny IsogenyPoints

noncomputable section

private theorem residual_eq_zero_of_nonsingular
    {W : WeierstrassCurve L} [W.IsElliptic]
    {x y : L} (h : WeierstrassCurve.Affine.Nonsingular W x y) :
    affineResidual W x y = 0 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simpa [affineResidual] using heq

theorem translated_curve_equation {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y) :
    tateW x y * (tateW x y - 3 * tateU x + 2) = tateU x ^ 3 := by
  have hres := residual_eq_zero_of_nonsingular h
  rw [← tate_change_identity] at hres
  unfold tateResidual at hres
  linear_combination hres

/-- Total dual Kummer value.  The special value at `T` is the tangent value
`1/2`; the other affine points use the translated `w` coordinate. -/
def kappa : E0Point → L
  | .zero => 1
  | .some x y _ => if x = 1 ∧ y = 0 then 1 / 2 else tateW x y

@[simp] theorem kappa_zero : kappa 0 = 1 := rfl

@[simp] theorem kappa_T : kappa T = 1 / 2 := by
  simp [kappa, T]

@[simp] theorem kappa_negT : kappa negT = -2 := by
  simp [kappa, negT, tateW]

theorem kappa_some_of_ne_T {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hne : ¬(x = 1 ∧ y = 0)) :
    kappa (.some x y h) = tateW x y := by
  simp [kappa, hne]

theorem kappa_ne_zero (P : E0Point) : kappa P ≠ 0 := by
  cases P with
  | zero => norm_num [kappa]
  | some x y h =>
      by_cases hT : x = 1 ∧ y = 0
      · simp [kappa, hT]
      · rw [kappa_some_of_ne_T h hT]
        intro hw
        have hcurve := translated_curve_equation h
        rw [hw] at hcurve
        have hu : tateU x = 0 := by
          have : tateU x ^ 3 = 0 := by simpa using hcurve.symm
          exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
        have hx : x = 1 := by
          unfold tateU at hu
          linear_combination hu
        have hy : y = 0 := by
          unfold tateW at hw
          rw [hx] at hw
          linear_combination hw
        exact hT ⟨hx, hy⟩

def kappaUnit (P : E0Point) : Lˣ := Units.mk0 (kappa P) (kappa_ne_zero P)

@[simp] theorem kappaUnit_coe (P : E0Point) : (kappaUnit P : L) = kappa P := rfl

theorem add_T_tateW {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) :
    (match (WeierstrassCurve.Affine.Point.some x y h : E0Point) + T with
      | .zero => (0 : L)
      | .some x' y' _ => tateW x' y') =
        -4 * tateW x y / tateU x ^ 3 := by
  have hx : x ≠ (1 : L) := by
    intro hx
    apply hu
    simp [tateU, hx]
  rw [T, WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  change tateW
      (WeierstrassCurve.Affine.addX E0 x 1
        (WeierstrassCurve.Affine.slope E0 x 1 y 0))
      (WeierstrassCurve.Affine.addY E0 x 1 y
        (WeierstrassCurve.Affine.slope E0 x 1 y 0)) = _
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  have hcurve := translated_curve_equation h
  unfold tateU tateW at hcurve
  unfold WeierstrassCurve.Affine.addX WeierstrassCurve.Affine.addY
    WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.negY
    E0 tateU tateW
  unfold WeierstrassCurve.Affine.addX
  field_simp [sub_ne_zero.mpr hx]
  ring_nf at hcurve ⊢
  linear_combination (x - y + 1) * hcurve

theorem sub_T_tateW {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) :
    (match (WeierstrassCurve.Affine.Point.some x y h : E0Point) - T with
      | .zero => (0 : L)
      | .some x' y' _ => tateW x' y') =
        -2 * tateU x ^ 3 / tateW x y ^ 2 := by
  have hx : x ≠ (1 : L) := by
    intro hx
    apply hu
    simp [tateU, hx]
  have hw : tateW x y ≠ 0 := by
    intro hw
    have hcurve := translated_curve_equation h
    rw [hw] at hcurve
    have hu0 : tateU x = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
        (by simpa using hcurve.symm)
    exact hu hu0
  rw [sub_eq_add_neg, neg_T, negT,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  change tateW
      (WeierstrassCurve.Affine.addX E0 x 1
        (WeierstrassCurve.Affine.slope E0 x 1 y (-2)))
      (WeierstrassCurve.Affine.addY E0 x 1 y
        (WeierstrassCurve.Affine.slope E0 x 1 y (-2))) = _
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  have hcurve := translated_curve_equation h
  unfold tateU tateW at hcurve
  unfold tateU at hu
  unfold tateW at hw
  unfold WeierstrassCurve.Affine.addX WeierstrassCurve.Affine.addY
    WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.negY
    E0 tateU tateW
  unfold WeierstrassCurve.Affine.addX
  field_simp [sub_ne_zero.mpr hx, hw]
  ring_nf at hcurve ⊢
  linear_combination
    (2 * x ^ 3 - 10 * x ^ 2 - 3 * x * y ^ 2 - 10 * x * y +
      6 * x - y ^ 3 - y ^ 2 + 6 * y + 2) * hcurve

private theorem affine_x_eq_one_cases {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x = 1) :
    (WeierstrassCurve.Affine.Point.some x y h : E0Point) = T ∨
      (WeierstrassCurve.Affine.Point.some x y h : E0Point) = negT := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  have hy : y * (y + 2) = 0 := by
    simp only [E0] at heq
    rw [hx] at heq
    linear_combination heq
  rcases mul_eq_zero.mp hy with hy | hy
  · left
    rw [T, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · right
    have hy' : y = -2 := by linear_combination hy
    rw [negT, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, hy'⟩

private theorem generic_add_T_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x ≠ 1) :
    (WeierstrassCurve.Affine.Point.some x y h : E0Point) + T ≠ 0 := by
  intro hzero
  have hneg : (WeierstrassCurve.Affine.Point.some x y h : E0Point) = -T := by
    calc
      (WeierstrassCurve.Affine.Point.some x y h : E0Point) =
          ((WeierstrassCurve.Affine.Point.some x y h : E0Point) + T) - T := by
            abel
      _ = -T := by rw [hzero]; simp
  rw [neg_T] at hneg
  have hx' := congrArg (fun P : E0Point ↦ match P with
    | .zero => (0 : L)
    | .some x _ _ => x) hneg
  exact hx (by simpa [negT] using hx')

private theorem generic_sub_T_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x ≠ 1) :
    (WeierstrassCurve.Affine.Point.some x y h : E0Point) - T ≠ 0 := by
  intro hzero
  have heq : (WeierstrassCurve.Affine.Point.some x y h : E0Point) = T :=
    sub_eq_zero.mp hzero
  have hx' := congrArg (fun P : E0Point ↦ match P with
    | .zero => (0 : L)
    | .some x _ _ => x) heq
  exact hx (by simpa [T] using hx')

private theorem generic_add_T_ne_T {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    : (WeierstrassCurve.Affine.Point.some x y h : E0Point) + T ≠ T := by
  intro heq
  have hzero : (WeierstrassCurve.Affine.Point.some x y h : E0Point) = 0 := by
    calc
      (WeierstrassCurve.Affine.Point.some x y h : E0Point) =
          ((WeierstrassCurve.Affine.Point.some x y h : E0Point) + T) - T := by
            abel
      _ = T - T := by rw [heq]
      _ = 0 := sub_self T
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hzero

private theorem generic_sub_T_ne_T {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x ≠ 1) :
    (WeierstrassCurve.Affine.Point.some x y h : E0Point) - T ≠ T := by
  intro heq
  have hneg : (WeierstrassCurve.Affine.Point.some x y h : E0Point) = negT := by
    calc
      (WeierstrassCurve.Affine.Point.some x y h : E0Point) =
          ((WeierstrassCurve.Affine.Point.some x y h : E0Point) - T) + T := by
            abel
      _ = T + T := by rw [heq]
      _ = negT := by simpa only [two_nsmul] using two_nsmul_T
  have hx' := congrArg (fun Q : E0Point ↦ match Q with
    | .zero => (0 : L)
    | .some x _ _ => x) hneg
  exact hx (by simpa [negT] using hx')

/-- Translation by `T` multiplies the dual Kummer value by its special
class, up to an explicit nonzero cube. -/
theorem kappa_add_T_cube_relation (P : E0Point) :
    ∃ c : L, c ≠ 0 ∧
      kappa (P + T) = kappa P * kappa T * c ^ 3 := by
  by_cases h0 : P = 0
  · subst P
    refine ⟨1, one_ne_zero, ?_⟩
    rw [show (0 : E0Point) + T = T from zero_add T]
    simp only [kappa_T, kappa_zero, one_mul, pow_three]
    ring
  by_cases hT : P = T
  · subst P
    refine ⟨-2, by norm_num, ?_⟩
    change kappa (2 • T) = _
    rw [two_nsmul_T]
    norm_num [kappa_T, kappa_negT]
  by_cases hnT : P = negT
  · subst P
    refine ⟨-1, by norm_num, ?_⟩
    have hz : negT + T = 0 := by
      rw [← neg_T]
      exact neg_add_cancel T
    rw [hz, kappa_zero]
    norm_num [kappa_zero, kappa_T, kappa_negT]
  cases P with
  | zero => exact (h0 rfl).elim
  | some x y h =>
      have hx : x ≠ 1 := by
        intro hx
        rcases affine_x_eq_one_cases h hx with hPT | hPnT
        · exact hT hPT
        · exact hnT hPnT
      have hu : tateU x ≠ 0 := by
        unfold tateU
        exact sub_ne_zero.mpr hx
      have hw : tateW x y ≠ 0 := by
        intro hw
        have hcurve := translated_curve_equation h
        rw [hw] at hcurve
        have hu0 : tateU x = 0 :=
          (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
            (by simpa using hcurve.symm)
        exact hu hu0
      let S : E0Point :=
        (WeierstrassCurve.Affine.Point.some x y h : E0Point) + T
      have hS0 : S ≠ 0 := generic_add_T_ne_zero h hx
      cases hS : S with
      | zero => exact (hS0 hS).elim
      | some x' y' h' =>
          have hSneT : ¬(x' = 1 ∧ y' = 0) := by
            intro hcoords
            have heq : S = T := by
              rw [hS, T, WeierstrassCurve.Affine.Point.some.injEq]
              exact hcoords
            exact (generic_add_T_ne_T h) (by simpa [S] using heq)
          refine ⟨-2 / tateU x, div_ne_zero (by norm_num) hu, ?_⟩
          change kappa S = _
          rw [hS, kappa_some_of_ne_T h' hSneT,
            kappa_some_of_ne_T h (by exact fun hxy => hx hxy.1)]
          have hraw := add_T_tateW h hu
          change (match S with
            | .zero => (0 : L)
            | .some x' y' _ => tateW x' y') = _ at hraw
          rw [hS] at hraw
          have hraw' : tateW x' y' =
              -4 * tateW x y / tateU x ^ 3 := by simpa only using hraw
          rw [hraw', kappa_T]
          field_simp [hu]
          ring

/-- Translation by `-T` has the analogous cube relation. -/
theorem kappa_sub_T_cube_relation (P : E0Point) :
    ∃ c : L, c ≠ 0 ∧
      kappa (P - T) = kappa P * kappa negT * c ^ 3 := by
  by_cases h0 : P = 0
  · subst P
    refine ⟨1, one_ne_zero, ?_⟩
    change kappa (-T) = _
    rw [neg_T]
    norm_num [kappa_zero, kappa_negT]
  by_cases hT : P = T
  · subst P
    exact ⟨-1, by norm_num, by norm_num [kappa_T, kappa_negT]⟩
  by_cases hnT : P = negT
  · subst P
    refine ⟨1 / 2, by norm_num, ?_⟩
    have hdouble : negT - T = T := by
      calc
        negT - T = -(T + T) := by rw [← neg_T]; abel
        _ = -negT := by rw [show T + T = negT by
          simpa only [two_nsmul] using two_nsmul_T]
        _ = T := by rw [← neg_T]; simp
    rw [hdouble]
    norm_num [kappa_T, kappa_negT]
  cases P with
  | zero => exact (h0 rfl).elim
  | some x y h =>
      have hx : x ≠ 1 := by
        intro hx
        rcases affine_x_eq_one_cases h hx with hPT | hPnT
        · exact hT hPT
        · exact hnT hPnT
      have hu : tateU x ≠ 0 := sub_ne_zero.mpr hx
      have hw : tateW x y ≠ 0 := by
        intro hw
        have hcurve := translated_curve_equation h
        rw [hw] at hcurve
        have hu0 : tateU x = 0 :=
          (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
            (by simpa using hcurve.symm)
        exact hu hu0
      let S : E0Point :=
        (WeierstrassCurve.Affine.Point.some x y h : E0Point) - T
      have hS0 : S ≠ 0 := generic_sub_T_ne_zero h hx
      cases hS : S with
      | zero => exact (hS0 hS).elim
      | some x' y' h' =>
          have hSneT : ¬(x' = 1 ∧ y' = 0) := by
            intro hcoords
            have heq : S = T := by
              rw [hS, T, WeierstrassCurve.Affine.Point.some.injEq]
              exact hcoords
            exact (generic_sub_T_ne_T h hx) (by simpa [S] using heq)
          refine ⟨tateU x / tateW x y, div_ne_zero hu hw, ?_⟩
          change kappa S = _
          rw [hS, kappa_some_of_ne_T h' hSneT,
            kappa_some_of_ne_T h (by exact fun hxy => hx hxy.1)]
          have hraw := sub_T_tateW h hu
          change (match S with
            | .zero => (0 : L)
            | .some x' y' _ => tateW x' y') = _ at hraw
          rw [hS] at hraw
          have hraw' : tateW x' y' =
              -2 * tateU x ^ 3 / tateW x y ^ 2 := by simpa only using hraw
          rw [hraw', kappa_negT]
          field_simp [hu, hw]

end

end MazurProof.N18RouteC.KummerGeometry
