import FLT.Assumptions.MazurProof.RationalPointsN15Isogeny

/-!
# Additivity of the explicit order-15 two-isogeny maps

This file proves the group-law branches of the two total point maps from
`RationalPointsN15Isogeny`.  The first layer covers identity, inverse,
doubling, and translation by the respective rational kernel point.
-/

namespace MazurProof.RationalPointsN15IsogenyHom

open RationalPointsN15Descent
open RationalPointsN15Isogeny
open WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

/-! ## Formal group-law branches already forced by the composition identities -/

@[simp] theorem forwardPoint_add_zero (P : FullTwoPoint) :
    forwardPoint (P + 0) = forwardPoint P + forwardPoint 0 := by
  simp

@[simp] theorem forwardPoint_zero_add (P : FullTwoPoint) :
    forwardPoint (0 + P) = forwardPoint 0 + forwardPoint P := by
  simp

@[simp] theorem dualPoint_add_zero (P : IsogenousPoint) :
    dualPoint (P + 0) = dualPoint P + dualPoint 0 := by
  simp

@[simp] theorem dualPoint_zero_add (P : IsogenousPoint) :
    dualPoint (0 + P) = dualPoint 0 + dualPoint P := by
  simp

theorem forwardPoint_add_neg (P : FullTwoPoint) :
    forwardPoint (P + -P) = forwardPoint P + forwardPoint (-P) := by
  rw [add_neg_cancel, forwardPoint_zero, forwardPoint_neg, add_neg_cancel]

theorem dualPoint_add_neg (P : IsogenousPoint) :
    dualPoint (P + -P) = dualPoint P + dualPoint (-P) := by
  rw [add_neg_cancel, dualPoint_zero, dualPoint_neg, add_neg_cancel]

theorem forwardPoint_add_self (P : FullTwoPoint) :
    forwardPoint (P + P) = forwardPoint P + forwardPoint P := by
  rw [← two_nsmul]
  calc
    forwardPoint (2 • P) =
        forwardPoint (dualPoint (forwardPoint P)) := by
      rw [dual_comp_forwardPoint]
    _ = 2 • forwardPoint P := forward_comp_dualPoint _

theorem dualPoint_add_self (P : IsogenousPoint) :
    dualPoint (P + P) = dualPoint P + dualPoint P := by
  rw [← two_nsmul]
  calc
    dualPoint (2 • P) =
        dualPoint (forwardPoint (dualPoint P)) := by
      rw [forward_comp_dualPoint]
    _ = 2 • dualPoint P := dual_comp_forwardPoint _

/-! ## Translation by the kernel point -/

private theorem fullEquation_of_nonsingular {x y : ℚ}
    (h : Nonsingular fullTwoCurve x y) : FullTwoEquation x y :=
  (fullTwoCurve_equation_iff x y).mp h.1

private theorem isogenousEquation_of_nonsingular {x y : ℚ}
    (h : Nonsingular isogenousCurve x y) : IsogenousEquation x y :=
  (isogenousCurve_equation_iff x y).mp h.1

private theorem full_y_zero_of_x_zero {x y : ℚ}
    (h : Nonsingular fullTwoCurve x y) (hx : x = 0) : y = 0 := by
  have heq := fullEquation_of_nonsingular h
  unfold FullTwoEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem isogenous_y_zero_of_x_zero {x y : ℚ}
    (h : Nonsingular isogenousCurve x y) (hx : x = 0) : y = 0 := by
  have heq := isogenousEquation_of_nonsingular h
  unfold IsogenousEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem full_slope_kernel {x y : ℚ} (hx : x ≠ 0) :
    slope fullTwoCurve x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

private theorem isogenous_slope_kernel {x y : ℚ} (hx : x ≠ 0) :
    slope isogenousCurve x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

private theorem full_add_kernel_x {x y : ℚ}
    (h : Nonsingular fullTwoCurve x y) (hx : x ≠ 0) :
    addX fullTwoCurve x 0 (slope fullTwoCurve x 0 y 0) = 16 / x := by
  rw [full_slope_kernel hx]
  have heq := fullEquation_of_nonsingular h
  unfold FullTwoEquation at heq
  unfold addX fullTwoCurve
  field_simp [hx]
  linear_combination heq

private theorem full_add_kernel_y {x y : ℚ}
    (h : Nonsingular fullTwoCurve x y) (hx : x ≠ 0) :
    addY fullTwoCurve x 0 y (slope fullTwoCurve x 0 y 0) =
      -(16 * y / x ^ 2) := by
  rw [full_slope_kernel hx]
  unfold addY negAddY negY
  have hX : addX fullTwoCurve x 0 (y / x) = 16 / x := by
    rw [← full_slope_kernel hx]
    exact full_add_kernel_x h hx
  rw [hX]
  simp [fullTwoCurve]
  field_simp [hx]
  ring

private theorem isogenous_add_kernel_x {x y : ℚ}
    (h : Nonsingular isogenousCurve x y) (hx : x ≠ 0) :
    addX isogenousCurve x 0 (slope isogenousCurve x 0 y 0) = 225 / x := by
  rw [isogenous_slope_kernel hx]
  have heq := isogenousEquation_of_nonsingular h
  unfold IsogenousEquation at heq
  unfold addX isogenousCurve
  field_simp [hx]
  linear_combination heq

private theorem isogenous_add_kernel_y {x y : ℚ}
    (h : Nonsingular isogenousCurve x y) (hx : x ≠ 0) :
    addY isogenousCurve x 0 y (slope isogenousCurve x 0 y 0) =
      -(225 * y / x ^ 2) := by
  rw [isogenous_slope_kernel hx]
  unfold addY negAddY negY
  have hX : addX isogenousCurve x 0 (y / x) = 225 / x := by
    rw [← isogenous_slope_kernel hx]
    exact isogenous_add_kernel_x h hx
  rw [hX]
  simp [isogenousCurve]
  field_simp [hx]
  ring

private theorem forward_translation_coordinates {x y : ℚ} (hx : x ≠ 0) :
    forwardX (16 / x) (-(16 * y / x ^ 2)) = forwardX x y ∧
      forwardY (16 / x) (-(16 * y / x ^ 2)) = forwardY x y := by
  constructor
  · unfold forwardX
    field_simp [hx]
  · unfold forwardY
    field_simp [hx]
    ring

private theorem dual_translation_coordinates {x y : ℚ} (hx : x ≠ 0) :
    dualX (225 / x) (-(225 * y / x ^ 2)) = dualX x y ∧
      dualY (225 / x) (-(225 * y / x ^ 2)) = dualY x y := by
  constructor
  · unfold dualX
    field_simp [hx]
  · unfold dualY
    field_simp [hx]
    ring

/-- The forward quotient map is invariant under translation by its kernel. -/
theorem forwardPoint_add_fullKernel (P : FullTwoPoint) :
    forwardPoint (P + fullKernel) = forwardPoint P := by
  cases P with
  | zero =>
      change forwardPoint fullKernel = forwardPoint 0
      rw [forwardPoint_fullKernel, forwardPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := full_y_zero_of_x_zero h hx
        subst x
        subst y
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : FullTwoPoint) =
            fullKernel by rfl]
        rw [← two_nsmul, two_nsmul_fullKernel]
        rw [forwardPoint_zero, forwardPoint_fullKernel]
      · change forwardPoint
            ((WeierstrassCurve.Affine.Point.some x y h : FullTwoPoint) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        have hax : addX fullTwoCurve x 0
            (slope fullTwoCurve x 0 y 0) ≠ 0 := by
          rw [full_add_kernel_x h hx]
          exact div_ne_zero (by norm_num) hx
        rw [forwardPoint_some_of_x_ne_zero _ hax,
          forwardPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (forwardX
              (addX fullTwoCurve x 0 (slope fullTwoCurve x 0 y 0))
              (addY fullTwoCurve x 0 y (slope fullTwoCurve x 0 y 0)))
            (forwardY
              (addX fullTwoCurve x 0 (slope fullTwoCurve x 0 y 0))
              (addY fullTwoCurve x 0 y (slope fullTwoCurve x 0 y 0))) _ =
          WeierstrassCurve.Affine.Point.some
            (forwardX x y) (forwardY x y) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := forward_translation_coordinates (x := x) (y := y) hx
        constructor
        · rw [full_add_kernel_x h hx, full_add_kernel_y h hx]
          exact hc.1
        · rw [full_add_kernel_x h hx, full_add_kernel_y h hx]
          exact hc.2

/-- The dual quotient map is invariant under translation by its kernel. -/
theorem dualPoint_add_isogenousKernel (P : IsogenousPoint) :
    dualPoint (P + isogenousKernel) = dualPoint P := by
  cases P with
  | zero =>
      change dualPoint isogenousKernel = dualPoint 0
      rw [dualPoint_isogenousKernel, dualPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := isogenous_y_zero_of_x_zero h hx
        subst x
        subst y
        rw [show (WeierstrassCurve.Affine.Point.some 0 0 h : IsogenousPoint) =
            isogenousKernel by rfl]
        rw [← two_nsmul, two_nsmul_isogenousKernel]
        rw [dualPoint_zero, dualPoint_isogenousKernel]
      · change dualPoint
            ((WeierstrassCurve.Affine.Point.some x y h : IsogenousPoint) +
              WeierstrassCurve.Affine.Point.some 0 0 _) = _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        have hax : addX isogenousCurve x 0
            (slope isogenousCurve x 0 y 0) ≠ 0 := by
          rw [isogenous_add_kernel_x h hx]
          exact div_ne_zero (by norm_num) hx
        rw [dualPoint_some_of_x_ne_zero _ hax,
          dualPoint_some_of_x_ne_zero h hx]
        change WeierstrassCurve.Affine.Point.some
            (dualX
              (addX isogenousCurve x 0 (slope isogenousCurve x 0 y 0))
              (addY isogenousCurve x 0 y (slope isogenousCurve x 0 y 0)))
            (dualY
              (addX isogenousCurve x 0 (slope isogenousCurve x 0 y 0))
              (addY isogenousCurve x 0 y (slope isogenousCurve x 0 y 0))) _ =
          WeierstrassCurve.Affine.Point.some
            (dualX x y) (dualY x y) _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        have hc := dual_translation_coordinates (x := x) (y := y) hx
        constructor
        · rw [isogenous_add_kernel_x h hx, isogenous_add_kernel_y h hx]
          exact hc.1
        · rw [isogenous_add_kernel_x h hx, isogenous_add_kernel_y h hx]
          exact hc.2

theorem forwardPoint_fullKernel_add (P : FullTwoPoint) :
    forwardPoint (fullKernel + P) = forwardPoint P := by
  rw [add_comm, forwardPoint_add_fullKernel]

theorem dualPoint_isogenousKernel_add (P : IsogenousPoint) :
    dualPoint (isogenousKernel + P) = dualPoint P := by
  rw [add_comm, dualPoint_add_isogenousKernel]

/-- Additivity for a pair differing by the forward kernel point. -/
theorem forwardPoint_add_kernelTranslate (P : FullTwoPoint) :
    forwardPoint (P + (P + fullKernel)) =
      forwardPoint P + forwardPoint (P + fullKernel) := by
  rw [← add_assoc, forwardPoint_add_fullKernel,
    forwardPoint_add_fullKernel, forwardPoint_add_self]

/-- Additivity for a pair whose sum is the forward kernel point. -/
theorem forwardPoint_add_neg_kernelTranslate (P : FullTwoPoint) :
    forwardPoint (P + (-P + fullKernel)) =
      forwardPoint P + forwardPoint (-P + fullKernel) := by
  rw [← add_assoc, add_neg_cancel, zero_add, forwardPoint_fullKernel,
    forwardPoint_add_fullKernel, forwardPoint_neg, add_neg_cancel]

/-- Additivity for a pair differing by the dual kernel point. -/
theorem dualPoint_add_kernelTranslate (P : IsogenousPoint) :
    dualPoint (P + (P + isogenousKernel)) =
      dualPoint P + dualPoint (P + isogenousKernel) := by
  rw [← add_assoc, dualPoint_add_isogenousKernel,
    dualPoint_add_isogenousKernel, dualPoint_add_self]

/-- Additivity for a pair whose sum is the dual kernel point. -/
theorem dualPoint_add_neg_kernelTranslate (P : IsogenousPoint) :
    dualPoint (P + (-P + isogenousKernel)) =
      dualPoint P + dualPoint (-P + isogenousKernel) := by
  rw [← add_assoc, add_neg_cancel, zero_add, dualPoint_isogenousKernel,
    dualPoint_add_isogenousKernel, dualPoint_neg, add_neg_cancel]

/-- A single eliminator for all forward-map group-law branches that do not
require the generic secant calculation. -/
theorem forwardPoint_add_of_basic_or_kernel_relation
    (P Q : FullTwoPoint)
    (hQ : Q = 0 ∨ Q = fullKernel ∨ Q = P ∨ Q = -P ∨
      Q = P + fullKernel ∨ Q = -P + fullKernel) :
    forwardPoint (P + Q) = forwardPoint P + forwardPoint Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact forwardPoint_add_zero P
  · rw [hQ, forwardPoint_add_fullKernel, forwardPoint_fullKernel, add_zero]
  · rw [hQ]
    exact forwardPoint_add_self P
  · rw [hQ]
    exact forwardPoint_add_neg P
  · rw [hQ]
    exact forwardPoint_add_kernelTranslate P
  · rw [hQ]
    exact forwardPoint_add_neg_kernelTranslate P

/-- A single eliminator for all dual-map group-law branches that do not
require the generic secant calculation. -/
theorem dualPoint_add_of_basic_or_kernel_relation
    (P Q : IsogenousPoint)
    (hQ : Q = 0 ∨ Q = isogenousKernel ∨ Q = P ∨ Q = -P ∨
      Q = P + isogenousKernel ∨ Q = -P + isogenousKernel) :
    dualPoint (P + Q) = dualPoint P + dualPoint Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact dualPoint_add_zero P
  · rw [hQ, dualPoint_add_isogenousKernel, dualPoint_isogenousKernel, add_zero]
  · rw [hQ]
    exact dualPoint_add_self P
  · rw [hQ]
    exact dualPoint_add_neg P
  · rw [hQ]
    exact dualPoint_add_kernelTranslate P
  · rw [hQ]
    exact dualPoint_add_neg_kernelTranslate P

/-! ## Affine fibre separation -/

private theorem forward_x_fibre_factor
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : FullTwoEquation x₁ y₁) (h₂ : FullTwoEquation x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : forwardX x₁ y₁ = forwardX x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = 16 := by
  unfold forwardX at hX
  unfold FullTwoEquation at h₁ h₂
  field_simp [hx₁, hx₂] at hX
  rw [h₁, h₂] at hX
  have hmul : x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - 16)) = 0 := by
    linear_combination hX
  have hfac : (x₁ - x₂) * (x₁ * x₂ - 16) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hx₁ hx₂)
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem dual_x_fibre_factor
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : IsogenousEquation x₁ y₁)
    (h₂ : IsogenousEquation x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hX : dualX x₁ y₁ = dualX x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = 225 := by
  unfold dualX at hX
  unfold IsogenousEquation at h₁ h₂
  field_simp [hx₁, hx₂] at hX
  rw [h₁, h₂] at hX
  have hmul : x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - 225)) = 0 := by
    linear_combination hX
  have hfac : (x₁ - x₂) * (x₁ * x₂ - 225) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hx₁ hx₂)
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem forward_affine_fibre
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Nonsingular fullTwoCurve x₁ y₁)
    (h₂ : Nonsingular fullTwoCurve x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : forwardPoint
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
      forwardPoint
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : FullTwoPoint) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : FullTwoPoint) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + fullKernel := by
  rw [forwardPoint_some_of_x_ne_zero h₁ hx₁,
    forwardPoint_some_of_x_ne_zero h₂ hx₂] at hmap
  change WeierstrassCurve.Affine.Point.some
      (forwardX x₁ y₁) (forwardY x₁ y₁) _ =
    WeierstrassCurve.Affine.Point.some
      (forwardX x₂ y₂) (forwardY x₂ y₂) _ at hmap
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hmap
  have heq₁ := fullEquation_of_nonsingular h₁
  have heq₂ := fullEquation_of_nonsingular h₂
  have hxf := forward_x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : FullTwoPoint) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : FullTwoPoint) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + fullKernel := by
    by_cases hyeq : y₁ = y₂
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hyroots := Y_eq_of_X_eq h₁.1 h₂.1 hxeq
      have hyneg : y₂ = -y₁ := by
        rcases hyroots with hy | hy
        · exact (hyeq hy).elim
        · rw [fullTwoCurve_negY] at hy
          linarith
      have hy₁ : y₁ ≠ 0 := by
        intro hyzero
        apply hyeq
        rw [hyzero] at hyneg ⊢
        simpa using hyneg.symm
      have hY := hcoords.2
      unfold forwardY at hY
      rw [← hxeq] at hY
      field_simp [hx₁] at hY
      rw [hyneg] at hY
      have hprod : y₁ * (16 - x₁ ^ 2) = 0 := by
        linear_combination (1 / 2 : ℚ) * hY
      have hsquare : x₁ ^ 2 = 16 := by
        have := (mul_eq_zero.mp hprod).resolve_left hy₁
        linarith
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : FullTwoPoint) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [full_add_kernel_x h₁ hx₁, ← hxeq]
        field_simp [hx₁]
        nlinarith
      · rw [full_add_kernel_y h₁ hx₁, hyneg]
        field_simp [hx₁]
        nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = 16 / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ 16 := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      unfold forwardY at hY
      rw [hx₂val] at hY
      field_simp [hx₁] at hY
      have hfac : (x₁ ^ 2 - 16) * (x₁ ^ 2 * y₂ + 16 * y₁) = 0 := by
        calc
          (x₁ ^ 2 - 16) * (x₁ ^ 2 * y₂ + 16 * y₁) =
              -(y₁ * 16 * (16 - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - 16)) := by ring
          _ = 0 := by rw [hY]; ring
      have hyrel : x₁ ^ 2 * y₂ + 16 * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : FullTwoPoint) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [full_add_kernel_x h₁ hx₁, hx₂val]
      · rw [full_add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

/-- The fibres of the forward rational-point map are exactly the cosets of
its two-element kernel. -/
theorem forwardPoint_eq_iff (P Q : FullTwoPoint) :
    forwardPoint P = forwardPoint Q ↔
      Q = P ∨ Q = P + fullKernel := by
  constructor
  · intro hPQ
    by_cases hPzero : forwardPoint P = 0
    · have hQzero : forwardPoint Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (forwardPoint_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (forwardPoint_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left; rw [hP, hQ]
      · right; rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, ← two_nsmul, two_nsmul_fullKernel]
      · left; rw [hP, hQ]
    · have hQzero : forwardPoint Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero forwardPoint_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero forwardPoint_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                exact forwardPoint_some_of_x_eq_zero h₁ hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                exact forwardPoint_some_of_x_eq_zero h₂ hx
              exact forward_affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (forwardPoint_add_fullKernel P).symm

private theorem dual_affine_fibre
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : Nonsingular isogenousCurve x₁ y₁)
    (h₂ : Nonsingular isogenousCurve x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : dualPoint
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
      dualPoint
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)) :
    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : IsogenousPoint) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : IsogenousPoint) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          isogenousKernel := by
  rw [dualPoint_some_of_x_ne_zero h₁ hx₁,
    dualPoint_some_of_x_ne_zero h₂ hx₂] at hmap
  change WeierstrassCurve.Affine.Point.some
      (dualX x₁ y₁) (dualY x₁ y₁) _ =
    WeierstrassCurve.Affine.Point.some
      (dualX x₂ y₂) (dualY x₂ y₂) _ at hmap
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hmap
  have heq₁ := isogenousEquation_of_nonsingular h₁
  have heq₂ := isogenousEquation_of_nonsingular h₂
  have hxf := dual_x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : IsogenousPoint) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∨
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : IsogenousPoint) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
            isogenousKernel := by
    by_cases hyeq : y₁ = y₂
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hyroots := Y_eq_of_X_eq h₁.1 h₂.1 hxeq
      have hyneg : y₂ = -y₁ := by
        rcases hyroots with hy | hy
        · exact (hyeq hy).elim
        · rw [isogenousCurve_negY] at hy
          linarith
      have hy₁ : y₁ ≠ 0 := by
        intro hyzero
        apply hyeq
        rw [hyzero] at hyneg ⊢
        simpa using hyneg.symm
      have hY := hcoords.2
      unfold dualY at hY
      rw [← hxeq] at hY
      field_simp [hx₁] at hY
      rw [hyneg] at hY
      have hprod : y₁ * (225 - x₁ ^ 2) = 0 := by
        linear_combination (1 / 2 : ℚ) * hY
      have hsquare : x₁ ^ 2 = 225 := by
        have := (mul_eq_zero.mp hprod).resolve_left hy₁
        linarith
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
            IsogenousPoint) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [isogenous_add_kernel_x h₁ hx₁, ← hxeq]
        field_simp [hx₁]
        nlinarith
      · rw [isogenous_add_kernel_y h₁ hx₁, hyneg]
        field_simp [hx₁]
        nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = 225 / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ 225 := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      unfold dualY at hY
      rw [hx₂val] at hY
      field_simp [hx₁] at hY
      have hfac :
          (x₁ ^ 2 - 225) * (x₁ ^ 2 * y₂ + 225 * y₁) = 0 := by
        calc
          (x₁ ^ 2 - 225) * (x₁ ^ 2 * y₂ + 225 * y₁) =
              -(y₁ * 225 * (225 - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - 225)) := by ring
          _ = 0 := by rw [hY]; ring
      have hyrel : x₁ ^ 2 * y₂ + 225 * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
            IsogenousPoint) +
          WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [isogenous_add_kernel_x h₁ hx₁, hx₂val]
      · rw [isogenous_add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

/-- The fibres of the dual rational-point map are exactly the cosets of its
two-element kernel. -/
theorem dualPoint_eq_iff (P Q : IsogenousPoint) :
    dualPoint P = dualPoint Q ↔
      Q = P ∨ Q = P + isogenousKernel := by
  constructor
  · intro hPQ
    by_cases hPzero : dualPoint P = 0
    · have hQzero : dualPoint Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (dualPoint_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (dualPoint_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left; rw [hP, hQ]
      · right; rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, ← two_nsmul, two_nsmul_isogenousKernel]
      · left; rw [hP, hQ]
    · have hQzero : dualPoint Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero dualPoint_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero dualPoint_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                exact dualPoint_some_of_x_eq_zero h₁ hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                exact dualPoint_some_of_x_eq_zero h₂ hx
              exact dual_affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (dualPoint_add_isogenousKernel P).symm

/-! ## The generic forward secant: x-coordinate -/

private theorem forwardX_secant_form {x y : ℚ}
    (h : FullTwoEquation x y) (hx : x ≠ 0) :
    forwardX x y = x + 17 + 16 / x := by
  unfold forwardX
  rw [h]
  field_simp [hx]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The cleared-denominator certificate requires unbounded polynomial normalization.
private theorem forward_secant_x_identity
    {x1 y1 x2 y2 : ℚ}
    (h1 : y1 ^ 2 = x1 * (x1 + 1) * (x1 + 16))
    (h2 : y2 ^ 2 = x2 * (x2 + 1) * (x2 + 16))
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : ((y1 - y2) / (x1 - x2)) ^ 2 - 17 - x1 - x2 ≠ 0)
    (hF : x1 + 17 + 16 / x1 ≠ x2 + 17 + 16 / x2) :
    let ell := (y1 - y2) / (x1 - x2)
    let rx := ell ^ 2 - 17 - x1 - x2
    let m :=
      (y1 * (16 - x1 ^ 2) / x1 ^ 2 -
        y2 * (16 - x2 ^ 2) / x2 ^ 2) /
      ((x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2))
    rx + 17 + 16 / rx =
      m ^ 2 + 34 - (x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2) := by
  dsimp
  have h16 : x1 * x2 - 16 ≠ 0 := by
    intro hzero
    apply hF
    apply sub_eq_zero.mp
    calc
      (x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2) =
          (x1 - x2) * (x1 * x2 - 16) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hAeq :
      (y1 - y2) ^ 2 - (x1 - x2) ^ 2 * 17 - x1 * (x1 - x2) ^ 2 -
          x2 * (x1 - x2) ^ 2 =
        (x1 - x2) ^ 2 *
          (((y1 - y2) / (x1 - x2)) ^ 2 - 17 - x1 - x2) := by
    field_simp [sub_ne_zero.mpr hx12]
  have hA :
      (y1 - y2) ^ 2 - (x1 - x2) ^ 2 * 17 - x1 * (x1 - x2) ^ 2 -
          x2 * (x1 - x2) ^ 2 ≠ 0 := by
    rw [hAeq]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx12)) hr
  have hBeq :
      x2 * (x1 * (x1 + 17) + 16) - x1 * (x2 * (x2 + 17) + 16) =
        (x1 - x2) * (x1 * x2 - 16) := by ring
  have hB :
      x2 * (x1 * (x1 + 17) + 16) - x1 * (x2 * (x2 + 17) + 16) ≠ 0 := by
    rw [hBeq]
    exact mul_ne_zero (sub_ne_zero.mpr hx12) h16
  field_simp [hx1, hx2, sub_ne_zero.mpr hx12, hr,
    sub_ne_zero.mpr hF, h16]
  field_simp [hA, hB]
  linear_combination
    (16 * (x1 - x2) ^ 3 *
      (x1 ^ 5 * x2 ^ 3 - 2 * x1 ^ 4 * x2 ^ 4 -
        32 * x1 ^ 4 * x2 ^ 2 - 3 * x1 ^ 3 * x2 ^ 5 -
        68 * x1 ^ 3 * x2 ^ 4 - 16 * x1 ^ 3 * x2 ^ 3 -
        2 * x1 ^ 3 * x2 ^ 2 * y1 * y2 +
        6 * x1 ^ 3 * x2 ^ 2 * y2 ^ 2 + 256 * x1 ^ 3 * x2 -
        16 * x1 ^ 3 * y2 ^ 2 + 2 * x1 ^ 2 * x2 ^ 6 +
        34 * x1 ^ 2 * x2 ^ 5 + 64 * x1 ^ 2 * x2 ^ 4 -
        2 * x1 ^ 2 * x2 ^ 3 * y1 ^ 2 +
        6 * x1 ^ 2 * x2 ^ 3 * y1 * y2 -
        6 * x1 ^ 2 * x2 ^ 3 * y2 ^ 2 + 544 * x1 ^ 2 * x2 ^ 3 +
        256 * x1 ^ 2 * x2 ^ 2 - 16 * x1 ^ 2 * x2 * y2 ^ 2 +
        272 * x1 * x2 ^ 4 + 16 * x1 * x2 ^ 2 * y1 ^ 2 -
        32 * x1 * x2 ^ 2 * y1 * y2 + 16 * x1 * x2 ^ 2 * y2 ^ 2 -
        16 * x2 ^ 6 - 272 * x2 ^ 5 + 16 * x2 ^ 3 * y1 ^ 2 -
        32 * x2 ^ 3 * y1 * y2 + 16 * x2 ^ 3 * y2 ^ 2)) * h1 +
    (16 * x1 ^ 2 * (x1 - x2) ^ 3 *
      (4 * x1 ^ 4 * x2 ^ 2 - 3 * x1 ^ 3 * x2 ^ 3 +
        68 * x1 ^ 3 * x2 ^ 2 - 16 * x1 ^ 3 * x2 +
        2 * x1 ^ 2 * x2 ^ 4 - 34 * x1 ^ 2 * x2 ^ 3 +
        48 * x1 ^ 2 * x2 ^ 2 - 544 * x1 ^ 2 * x2 - 256 * x1 ^ 2 -
        x1 * x2 ^ 5 - 64 * x1 * x2 ^ 3 -
        6 * x1 * x2 ^ 2 * y1 * y2 + 2 * x1 * x2 ^ 2 * y2 ^ 2 -
        272 * x1 * x2 ^ 2 - 256 * x1 * x2 + 32 * x1 * y1 * y2 -
        16 * x1 * y2 ^ 2 + 32 * x2 ^ 4 + 2 * x2 ^ 3 * y1 * y2 +
        272 * x2 ^ 3 + 32 * x2 * y1 * y2 - 16 * x2 * y2 ^ 2)) * h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The secant coefficient identities require unbounded polynomial normalization.
private theorem forward_secant_y_identity
    {x1 y1 x2 y2 ell r : ℚ}
    (h1 : y1 ^ 2 = x1 * (x1 + 1) * (x1 + 16))
    (h2 : y2 ^ 2 = x2 * (x2 + 1) * (x2 + 16))
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hell : ell = (y1 - y2) / (x1 - x2))
    (hrdef : r = ell ^ 2 - 17 - x1 - x2)
    (hr : r ≠ 0) (h16 : x1 * x2 - 16 ≠ 0) :
    let s := ell * (x1 - r) - y1
    let m :=
      (y1 * (16 - x1 ^ 2) / x1 ^ 2 -
        y2 * (16 - x2 ^ 2) / x2 ^ 2) /
      ((x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2))
    s * (16 - r ^ 2) / r ^ 2 =
      m * ((x1 + 17 + 16 / x1) - (r + 17 + 16 / r)) -
        y1 * (16 - x1 ^ 2) / x1 ^ 2 := by
  have hline : y2 = y1 - ell * (x1 - x2) := by
    rw [hell]
    field_simp [sub_ne_zero.mpr hx12]
    ring
  have h2' := h2
  rw [hline] at h2'
  have hBmul :
      (x1 - x2) *
        (x1 * x2 + x1 * r + x2 * r -
          (16 - 2 * ell * y1 + 2 * ell ^ 2 * x1)) = 0 := by
    rw [hrdef]
    linear_combination h1 - h2'
  have hB :
      x1 * x2 + x1 * r + x2 * r -
          (16 - 2 * ell * y1 + 2 * ell ^ 2 * x1) = 0 :=
    (mul_eq_zero.mp hBmul).resolve_left (sub_ne_zero.mpr hx12)
  have hC : x1 * x2 * r - (y1 - ell * x1) ^ 2 = 0 := by
    linear_combination x1 * hB - h1 - x1 ^ 2 * hrdef
  have hH :
      ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
          16 * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
          16 * y1 = 0 := by
    linear_combination (ell * x1 - y1) * hB - 2 * ell * hC
  have hFD_eq :
      (x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2) =
        (x1 - x2) * (x1 * x2 - 16) / (x1 * x2) := by
    field_simp [hx1, hx2]
    ring
  have hm :
      (y1 * (16 - x1 ^ 2) / x1 ^ 2 -
          y2 * (16 - x2 ^ 2) / x2 ^ 2) /
        ((x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2)) =
      (-16 * y1 * (x1 + x2) + ell * x1 ^ 2 * (16 - x2 ^ 2)) /
        (x1 * x2 * (x1 * x2 - 16)) := by
    rw [hline, hFD_eq]
    field_simp [hx1, hx2, sub_ne_zero.mpr hx12, h16]
    ring
  dsimp
  rw [hm]
  apply sub_eq_zero.mp
  calc
    (ell * (x1 - r) - y1) * (16 - r ^ 2) / r ^ 2 -
          ((-16 * y1 * (x1 + x2) + ell * x1 ^ 2 * (16 - x2 ^ 2)) /
              (x1 * x2 * (x1 * x2 - 16)) *
            ((x1 + 17 + 16 / x1) - (r + 17 + 16 / r)) -
          y1 * (16 - x1 ^ 2) / x1 ^ 2) =
        16 * (x1 - r) * (x2 - r) *
            (ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
              16 * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
              16 * y1) /
          (r ^ 2 * x1 * x2 * (x1 * x2 - 16)) := by
      field_simp [hx1, hx2, hr, h16]
      ring
    _ = 0 := by rw [hH]; ring

/-- In the generic affine secant branch, the forward two-isogeny preserves
the x-coordinate of addition. -/
theorem forward_add_x_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular fullTwoCurve x1 y1)
    (h2 : Nonsingular fullTwoCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX fullTwoCurve x1 x2
        (slope fullTwoCurve x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    forwardX
        (addX fullTwoCurve x1 x2 (slope fullTwoCurve x1 x2 y1 y2))
        (addY fullTwoCurve x1 x2 y1 (slope fullTwoCurve x1 x2 y1 y2)) =
      addX isogenousCurve (forwardX x1 y1) (forwardX x2 y2)
        (slope isogenousCurve (forwardX x1 y1) (forwardX x2 y2)
          (forwardY x1 y1) (forwardY x2 y2)) := by
  have heq1 := fullEquation_of_nonsingular h1
  have heq2 := fullEquation_of_nonsingular h2
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := fullEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 - 17 - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, fullTwoCurve] using hr
  have hF' : x1 + 17 + 16 / x1 ≠ x2 + 17 + 16 / x2 := by
    simpa [forwardX_secant_form heq1 hx1,
      forwardX_secant_form heq2 hx2] using hF
  have hid := forward_secant_x_identity heq1 heq2 hx1 hx2 hx12 hr' hF'
  rw [forwardX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, slope_of_X_ne hF]
  rw [forwardX_secant_form heq1 hx1, forwardX_secant_form heq2 hx2]
  simpa [addX, fullTwoCurve, isogenousCurve, forwardY] using hid

/-- In the generic affine secant branch, the forward two-isogeny preserves
the y-coordinate of addition. -/
theorem forward_add_y_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular fullTwoCurve x1 y1)
    (h2 : Nonsingular fullTwoCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX fullTwoCurve x1 x2
        (slope fullTwoCurve x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    forwardY
        (addX fullTwoCurve x1 x2 (slope fullTwoCurve x1 x2 y1 y2))
        (addY fullTwoCurve x1 x2 y1 (slope fullTwoCurve x1 x2 y1 y2)) =
      addY isogenousCurve (forwardX x1 y1) (forwardX x2 y2) (forwardY x1 y1)
        (slope isogenousCurve (forwardX x1 y1) (forwardX x2 y2)
          (forwardY x1 y1) (forwardY x2 y2)) := by
  have heq1 := fullEquation_of_nonsingular h1
  have heq2 := fullEquation_of_nonsingular h2
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := fullEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 - 17 - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, fullTwoCurve] using hr
  have hF' : x1 + 17 + 16 / x1 ≠ x2 + 17 + 16 / x2 := by
    simpa [forwardX_secant_form heq1 hx1,
      forwardX_secant_form heq2 hx2] using hF
  have h16 : x1 * x2 - 16 ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x1 + 17 + 16 / x1) - (x2 + 17 + 16 / x2) =
          (x1 - x2) * (x1 * x2 - 16) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := forward_secant_y_identity heq1 heq2 hx1 hx2 hx12
    (ell := (y1 - y2) / (x1 - x2))
    (r := ((y1 - y2) / (x1 - x2)) ^ 2 - 17 - x1 - x2)
    rfl rfl hr' h16
  have hX := forward_add_x_generic h1 h2 hx1 hx2 hx12 hr hF
  unfold addY negAddY
  rw [isogenousCurve_negY, fullTwoCurve_negY]
  rw [← hX]
  rw [forwardX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, slope_of_X_ne hF]
  rw [forwardX_secant_form heq1 hx1, forwardX_secant_form heq2 hx2]
  simp only [forwardY, addX, fullTwoCurve]
  convert hid using 1 <;> ring

/-- The forward point map is additive in the generic affine secant branch. -/
theorem forwardPoint_add_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular fullTwoCurve x1 y1)
    (h2 : Nonsingular fullTwoCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX fullTwoCurve x1 x2
        (slope fullTwoCurve x1 x2 y1 y2) ≠ 0)
    (hF : forwardX x1 y1 ≠ forwardX x2 y2) :
    forwardPoint
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      forwardPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        forwardPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12]
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  rw [forwardPoint_some_of_x_ne_zero hsum hr,
    forwardPoint_some_of_x_ne_zero h1 hx1,
    forwardPoint_some_of_x_ne_zero h2 hx2]
  change WeierstrassCurve.Affine.Point.some
      (forwardX
        (addX fullTwoCurve x1 x2 (slope fullTwoCurve x1 x2 y1 y2))
        (addY fullTwoCurve x1 x2 y1 (slope fullTwoCurve x1 x2 y1 y2)))
      (forwardY
        (addX fullTwoCurve x1 x2 (slope fullTwoCurve x1 x2 y1 y2))
        (addY fullTwoCurve x1 x2 y1 (slope fullTwoCurve x1 x2 y1 y2))) _ =
    (WeierstrassCurve.Affine.Point.some
        (forwardX x1 y1) (forwardY x1 y1) _ : IsogenousPoint) +
      WeierstrassCurve.Affine.Point.some
        (forwardX x2 y2) (forwardY x2 y2) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hF,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨forward_add_x_generic h1 h2 hx1 hx2 hx12 hr hF,
    forward_add_y_generic h1 h2 hx1 hx2 hx12 hr hF⟩

private theorem forwardPoint_add_of_forwardX_eq
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular fullTwoCurve x1 y1)
    (h2 : Nonsingular fullTwoCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hF : forwardX x1 y1 = forwardX x2 y2) :
    forwardPoint
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      forwardPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        forwardPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  have hf1 : Nonsingular isogenousCurve (forwardX x1 y1) (forwardY x1 y1) :=
    equation_iff_nonsingular.mp
      (forward_equation hx1 (equation_iff_nonsingular.mpr h1))
  have hf2 : Nonsingular isogenousCurve (forwardX x2 y2) (forwardY x2 y2) :=
    equation_iff_nonsingular.mp
      (forward_equation hx2 (equation_iff_nonsingular.mpr h2))
  have hKneg : -fullKernel = fullKernel := by
    rw [neg_eq_iff_add_eq_zero, ← two_nsmul, two_nsmul_fullKernel]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (h₁ := hf1) (h₂ := hf2)).mp hF with hsame | hneg
  · have hmap :
        forwardPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          forwardPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [forwardPoint_some_of_x_ne_zero h1 hx1,
        forwardPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hsame
    rcases (forwardPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (WeierstrassCurve.Affine.Point.some x2 y2 h2)).mp hmap with hQ | hQ
    · exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inl hQ)))
    · exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  · have hmapneg :
        forwardPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          -forwardPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [forwardPoint_some_of_x_ne_zero h1 hx1,
        forwardPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hneg
    have hmap :
        forwardPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          forwardPoint (-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) := by
      rw [forwardPoint_neg]
      exact hmapneg
    rcases (forwardPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (-(WeierstrassCurve.Affine.Point.some x2 y2 h2))).mp hmap with hQ | hQ
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
            congrArg Neg.neg hQ
      exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inl hQ'))))
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) + fullKernel := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -((WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
                fullKernel) := by rw [hQ]
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) + fullKernel := by
            simp [hKneg, add_comm]
      exact forwardPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ')))))

/-- The explicit forward two-isogeny is additive on all rational points. -/
theorem forwardPoint_add (P Q : FullTwoPoint) :
    forwardPoint (P + Q) = forwardPoint P + forwardPoint Q := by
  cases P with
  | zero => exact forwardPoint_zero_add Q
  | some x1 y1 h1 =>
      cases Q with
      | zero => exact forwardPoint_add_zero _
      | some x2 y2 h2 =>
          by_cases hx1 : x1 = 0
          · have hy1 := full_y_zero_of_x_zero h1 hx1
            subst x1
            subst y1
            rw [show (WeierstrassCurve.Affine.Point.some 0 0 h1 : FullTwoPoint) =
              fullKernel by rfl]
            rw [forwardPoint_fullKernel_add, forwardPoint_fullKernel, zero_add]
          · by_cases hx2 : x2 = 0
            · have hy2 := full_y_zero_of_x_zero h2 hx2
              subst x2
              subst y2
              rw [show (WeierstrassCurve.Affine.Point.some 0 0 h2 : FullTwoPoint) =
                fullKernel by rfl]
              rw [forwardPoint_add_fullKernel, forwardPoint_fullKernel, add_zero]
            · by_cases hx12 : x1 = x2
              · rcases (WeierstrassCurve.Affine.Point.X_eq_iff
                  (h₁ := h1) (h₂ := h2)).mp hx12 with hsame | hneg
                · rw [← hsame]
                  exact forwardPoint_add_self _
                · have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
                          -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
                        (neg_neg _).symm
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
                        (congrArg Neg.neg hneg).symm
                  rw [hQ]
                  exact forwardPoint_add_neg _
              · by_cases hr : addX fullTwoCurve x1 x2
                    (slope fullTwoCurve x1 x2 y1 y2) = 0
                · have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
                  have hsumY := full_y_zero_of_x_zero hsum hr
                  have hsumK :
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 = fullKernel := by
                    change
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 =
                        WeierstrassCurve.Affine.Point.some 0 0 _
                    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12,
                      WeierstrassCurve.Affine.Point.some.injEq]
                    exact ⟨hr, hsumY⟩
                  have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          fullKernel := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 : FullTwoPoint) =
                          -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                            ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : FullTwoPoint) +
                              WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
                        symm
                        rw [← add_assoc, neg_add_cancel, zero_add]
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          fullKernel := by rw [hsumK]
                  exact forwardPoint_add_of_basic_or_kernel_relation _ _
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))
                · by_cases hF : forwardX x1 y1 = forwardX x2 y2
                  · exact forwardPoint_add_of_forwardX_eq h1 h2 hx1 hx2 hF
                  · exact forwardPoint_add_generic h1 h2 hx1 hx2 hx12 hr hF

/-- The explicit forward two-isogeny as an additive homomorphism. -/
noncomputable def forwardPointHom : FullTwoPoint →+ IsogenousPoint where
  toFun := forwardPoint
  map_zero' := forwardPoint_zero
  map_add' := forwardPoint_add

@[simp] theorem forwardPointHom_apply (P : FullTwoPoint) :
    forwardPointHom P = forwardPoint P := rfl

/-! ## A parameterized secant identity for the dual map -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- These parameterized cubic coefficient identities require unbounded normalization.
private theorem standard_secant_relations
    {a b x1 y1 x2 y2 ell r : ℚ}
    (h1 : y1 ^ 2 = x1 * (x1 ^ 2 + a * x1 + b))
    (h2 : y2 ^ 2 = x2 * (x2 ^ 2 + a * x2 + b))
    (hx12 : x1 ≠ x2)
    (hell : ell = (y1 - y2) / (x1 - x2))
    (hrdef : r = ell ^ 2 - a - x1 - x2) :
    x1 * x2 + x1 * r + x2 * r -
          (b - 2 * ell * y1 + 2 * ell ^ 2 * x1) = 0 ∧
      x1 * x2 * r - (y1 - ell * x1) ^ 2 = 0 := by
  have hline : y2 = y1 - ell * (x1 - x2) := by
    rw [hell]
    field_simp [sub_ne_zero.mpr hx12]
    ring
  have h2' := h2
  rw [hline] at h2'
  have hBmul :
      (x1 - x2) *
        (x1 * x2 + x1 * r + x2 * r -
          (b - 2 * ell * y1 + 2 * ell ^ 2 * x1)) = 0 := by
    rw [hrdef]
    linear_combination h1 - h2'
  have hB :
      x1 * x2 + x1 * r + x2 * r -
          (b - 2 * ell * y1 + 2 * ell ^ 2 * x1) = 0 :=
    (mul_eq_zero.mp hBmul).resolve_left (sub_ne_zero.mpr hx12)
  refine ⟨hB, ?_⟩
  linear_combination x1 * hB - h1 - x1 ^ 2 * hrdef

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The parameterized x-coordinate calculation requires unbounded normalization.
private theorem standard_secant_x_identity
    {a b x1 y1 x2 y2 ell r : ℚ}
    (h1 : y1 ^ 2 = x1 * (x1 ^ 2 + a * x1 + b))
    (h2 : y2 ^ 2 = x2 * (x2 ^ 2 + a * x2 + b))
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hell : ell = (y1 - y2) / (x1 - x2))
    (hrdef : r = ell ^ 2 - a - x1 - x2)
    (hr : r ≠ 0) (hb : x1 * x2 - b ≠ 0) :
    r + a + b / r =
      ((y1 * (b - x1 ^ 2) / x1 ^ 2 -
          y2 * (b - x2 ^ 2) / x2 ^ 2) /
        ((x1 + a + b / x1) - (x2 + a + b / x2))) ^ 2 +
        2 * a - (x1 + a + b / x1) - (x2 + a + b / x2) := by
  have hline : y2 = y1 - ell * (x1 - x2) := by
    rw [hell]
    field_simp [sub_ne_zero.mpr hx12]
    ring
  obtain ⟨hB, hC⟩ := standard_secant_relations h1 h2 hx12 hell hrdef
  have hCeq : r * x1 * x2 = (ell * x1 - y1) ^ 2 := by
    linear_combination hC
  have hu : ell * x1 - y1 ≠ 0 := by
    intro hu0
    have hprod : r * x1 * x2 ≠ 0 := mul_ne_zero (mul_ne_zero hr hx1) hx2
    apply hprod
    rw [hCeq, hu0]
    norm_num
  have hu' : -y1 + x1 * ell ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hu'' : x1 * ell - y1 ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hT :
      x1 * x2 + r * (x1 + x2) = b + 2 * ell * (ell * x1 - y1) := by
    linear_combination hB
  have hA : r + x1 + x2 + a = ell ^ 2 := by
    linear_combination hrdef
  have hFD_eq :
      (x1 + a + b / x1) - (x2 + a + b / x2) =
        (x1 - x2) * (x1 * x2 - b) / (x1 * x2) := by
    field_simp [hx1, hx2]
    ring
  have hm0 :
      (y1 * (b - x1 ^ 2) / x1 ^ 2 -
          y2 * (b - x2 ^ 2) / x2 ^ 2) /
        ((x1 + a + b / x1) - (x2 + a + b / x2)) =
      (-b * y1 * (x1 + x2) + ell * x1 ^ 2 * (b - x2 ^ 2)) /
        (x1 * x2 * (x1 * x2 - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx1, hx2, sub_ne_zero.mpr hx12, hb]
    ring
  have hcross :
      (-b * y1 * (x1 + x2) + ell * x1 ^ 2 * (b - x2 ^ 2)) *
          (ell * x1 - y1) +
        (ell * (ell * x1 - y1) + b) * (x1 * x2 * (x1 * x2 - b)) = 0 := by
    linear_combination (b * x1 * x2) * hB - (b * (x1 + x2)) * hC
  have hden : x1 * x2 * (x1 * x2 - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx1 hx2) hb
  have hm1 :
      (-b * y1 * (x1 + x2) + ell * x1 ^ 2 * (b - x2 ^ 2)) /
          (x1 * x2 * (x1 * x2 - b)) =
        -(ell * (ell * x1 - y1) + b) / (ell * x1 - y1) := by
    apply (div_eq_iff hden).2
    field_simp [hu, hu', hu'']
    linear_combination hcross
  have hsum :
      (r + a + b / r) + (x1 + a + b / x1) +
          (x2 + a + b / x2) - 2 * a =
        ((ell * (ell * x1 - y1) + b) / (ell * x1 - y1)) ^ 2 := by
    calc
      (r + a + b / r) + (x1 + a + b / x1) +
            (x2 + a + b / x2) - 2 * a =
          r + x1 + x2 + a +
            b * (x1 * x2 + r * (x1 + x2)) / (r * x1 * x2) := by
        field_simp [hr, hx1, hx2]
        ring
      _ = ell ^ 2 +
            b * (x1 * x2 + r * (x1 + x2)) / (r * x1 * x2) := by rw [hA]
      _ = ell ^ 2 +
            b * (b + 2 * ell * (ell * x1 - y1)) /
              ((ell * x1 - y1) ^ 2) := by rw [hT, hCeq]
      _ = ((ell * (ell * x1 - y1) + b) / (ell * x1 - y1)) ^ 2 := by
        field_simp [hu]
        ring
  rw [hm0, hm1]
  linear_combination hsum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The parameterized y-coordinate factorization requires unbounded normalization.
private theorem standard_secant_y_identity
    {a b x1 y1 x2 y2 ell r : ℚ}
    (h1 : y1 ^ 2 = x1 * (x1 ^ 2 + a * x1 + b))
    (h2 : y2 ^ 2 = x2 * (x2 ^ 2 + a * x2 + b))
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hell : ell = (y1 - y2) / (x1 - x2))
    (hrdef : r = ell ^ 2 - a - x1 - x2)
    (hr : r ≠ 0) (hb : x1 * x2 - b ≠ 0) :
    (ell * (x1 - r) - y1) * (b - r ^ 2) / r ^ 2 =
      ((y1 * (b - x1 ^ 2) / x1 ^ 2 -
          y2 * (b - x2 ^ 2) / x2 ^ 2) /
        ((x1 + a + b / x1) - (x2 + a + b / x2))) *
          ((x1 + a + b / x1) - (r + a + b / r)) -
        y1 * (b - x1 ^ 2) / x1 ^ 2 := by
  have hline : y2 = y1 - ell * (x1 - x2) := by
    rw [hell]
    field_simp [sub_ne_zero.mpr hx12]
    ring
  obtain ⟨hB, hC⟩ := standard_secant_relations h1 h2 hx12 hell hrdef
  have hH :
      ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
          b * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
          b * y1 = 0 := by
    linear_combination (ell * x1 - y1) * hB - 2 * ell * hC
  have hFD_eq :
      (x1 + a + b / x1) - (x2 + a + b / x2) =
        (x1 - x2) * (x1 * x2 - b) / (x1 * x2) := by
    field_simp [hx1, hx2]
    ring
  have hm :
      (y1 * (b - x1 ^ 2) / x1 ^ 2 -
          y2 * (b - x2 ^ 2) / x2 ^ 2) /
        ((x1 + a + b / x1) - (x2 + a + b / x2)) =
      (-b * y1 * (x1 + x2) + ell * x1 ^ 2 * (b - x2 ^ 2)) /
        (x1 * x2 * (x1 * x2 - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx1, hx2, sub_ne_zero.mpr hx12, hb]
    ring
  rw [hm]
  apply sub_eq_zero.mp
  calc
    (ell * (x1 - r) - y1) * (b - r ^ 2) / r ^ 2 -
          ((-b * y1 * (x1 + x2) + ell * x1 ^ 2 * (b - x2 ^ 2)) /
              (x1 * x2 * (x1 * x2 - b)) *
            ((x1 + a + b / x1) - (r + a + b / r)) -
          y1 * (b - x1 ^ 2) / x1 ^ 2) =
        b * (x1 - r) * (x2 - r) *
            (ell * r * x1 ^ 2 - ell * r * x1 * x2 + ell * x1 ^ 2 * x2 -
              b * ell * x1 - r * x1 * y1 - r * x2 * y1 - x1 * x2 * y1 +
              b * y1) /
          (r ^ 2 * x1 * x2 * (x1 * x2 - b)) := by
      field_simp [hx1, hx2, hr, hb]
      ring
    _ = 0 := by rw [hH]; ring

private theorem dualX_secant_form {x y : ℚ}
    (h : IsogenousEquation x y) (hx : x ≠ 0) :
    dualX x y = (x - 34 + 225 / x) / 4 := by
  unfold dualX
  rw [h]
  field_simp [hx]
  ring

/-- In the generic affine secant branch, the dual two-isogeny preserves
the x-coordinate of addition. -/
theorem dual_add_x_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular isogenousCurve x1 y1)
    (h2 : Nonsingular isogenousCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX isogenousCurve x1 x2
        (slope isogenousCurve x1 x2 y1 y2) ≠ 0)
    (hF : dualX x1 y1 ≠ dualX x2 y2) :
    dualX
        (addX isogenousCurve x1 x2 (slope isogenousCurve x1 x2 y1 y2))
        (addY isogenousCurve x1 x2 y1 (slope isogenousCurve x1 x2 y1 y2)) =
      addX fullTwoCurve (dualX x1 y1) (dualX x2 y2)
        (slope fullTwoCurve (dualX x1 y1) (dualX x2 y2)
          (dualY x1 y1) (dualY x2 y2)) := by
  have heq1 := isogenousEquation_of_nonsingular h1
  have heq2 := isogenousEquation_of_nonsingular h2
  have hg1 : y1 ^ 2 = x1 * (x1 ^ 2 + (-34 : ℚ) * x1 + 225) := by
    unfold IsogenousEquation at heq1
    rw [heq1]
    ring
  have hg2 : y2 ^ 2 = x2 * (x2 ^ 2 + (-34 : ℚ) * x2 + 225) := by
    unfold IsogenousEquation at heq2
    rw [heq2]
    ring
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := isogenousEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 + 34 - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, isogenousCurve] using hr
  have hF' : x1 - 34 + 225 / x1 ≠ x2 - 34 + 225 / x2 := by
    intro hEq
    apply hF
    rw [dualX_secant_form heq1 hx1, dualX_secant_form heq2 hx2, hEq]
  have h225 : x1 * x2 - 225 ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x1 - 34 + 225 / x1) - (x2 - 34 + 225 / x2) =
          (x1 - x2) * (x1 * x2 - 225) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hslope :
      slope fullTwoCurve (dualX x1 y1) (dualX x2 y2)
          (dualY x1 y1) (dualY x2 y2) =
        ((y1 * (225 - x1 ^ 2) / x1 ^ 2 -
            y2 * (225 - x2 ^ 2) / x2 ^ 2) /
          ((x1 - 34 + 225 / x1) - (x2 - 34 + 225 / x2))) / 2 := by
    rw [slope_of_X_ne hF,
      dualX_secant_form heq1 hx1, dualX_secant_form heq2 hx2]
    unfold dualY
    field_simp [hx1, hx2, sub_ne_zero.mpr hF']
    ring
  have hid := standard_secant_x_identity hg1 hg2 hx1 hx2 hx12
    (a := (-34 : ℚ)) (b := 225)
    (ell := (y1 - y2) / (x1 - x2))
    (r := ((y1 - y2) / (x1 - x2)) ^ 2 + 34 - x1 - x2)
    rfl (by ring) hr' h225
  have hid4 := congrArg (fun z : ℚ ↦ z / 4) hid
  rw [dualX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, hslope]
  rw [dualX_secant_form heq1 hx1, dualX_secant_form heq2 hx2]
  simp only [addX, isogenousCurve, fullTwoCurve]
  convert hid4 using 1 <;> ring

/-- In the generic affine secant branch, the dual two-isogeny preserves
the y-coordinate of addition. -/
theorem dual_add_y_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular isogenousCurve x1 y1)
    (h2 : Nonsingular isogenousCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX isogenousCurve x1 x2
        (slope isogenousCurve x1 x2 y1 y2) ≠ 0)
    (hF : dualX x1 y1 ≠ dualX x2 y2) :
    dualY
        (addX isogenousCurve x1 x2 (slope isogenousCurve x1 x2 y1 y2))
        (addY isogenousCurve x1 x2 y1 (slope isogenousCurve x1 x2 y1 y2)) =
      addY fullTwoCurve (dualX x1 y1) (dualX x2 y2) (dualY x1 y1)
        (slope fullTwoCurve (dualX x1 y1) (dualX x2 y2)
          (dualY x1 y1) (dualY x2 y2)) := by
  have heq1 := isogenousEquation_of_nonsingular h1
  have heq2 := isogenousEquation_of_nonsingular h2
  have hg1 : y1 ^ 2 = x1 * (x1 ^ 2 + (-34 : ℚ) * x1 + 225) := by
    unfold IsogenousEquation at heq1
    rw [heq1]
    ring
  have hg2 : y2 ^ 2 = x2 * (x2 ^ 2 + (-34 : ℚ) * x2 + 225) := by
    unfold IsogenousEquation at heq2
    rw [heq2]
    ring
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  have hsumEq := isogenousEquation_of_nonsingular hsum
  have hr' :
      ((y1 - y2) / (x1 - x2)) ^ 2 + 34 - x1 - x2 ≠ 0 := by
    simpa [slope_of_X_ne hx12, addX, isogenousCurve] using hr
  have hF' : x1 - 34 + 225 / x1 ≠ x2 - 34 + 225 / x2 := by
    intro hEq
    apply hF
    rw [dualX_secant_form heq1 hx1, dualX_secant_form heq2 hx2, hEq]
  have h225 : x1 * x2 - 225 ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x1 - 34 + 225 / x1) - (x2 - 34 + 225 / x2) =
          (x1 - x2) * (x1 * x2 - 225) / (x1 * x2) := by
        field_simp [hx1, hx2]
        ring
      _ = 0 := by rw [hzero]; simp
  have hslope :
      slope fullTwoCurve (dualX x1 y1) (dualX x2 y2)
          (dualY x1 y1) (dualY x2 y2) =
        ((y1 * (225 - x1 ^ 2) / x1 ^ 2 -
            y2 * (225 - x2 ^ 2) / x2 ^ 2) /
          ((x1 - 34 + 225 / x1) - (x2 - 34 + 225 / x2))) / 2 := by
    rw [slope_of_X_ne hF,
      dualX_secant_form heq1 hx1, dualX_secant_form heq2 hx2]
    unfold dualY
    field_simp [hx1, hx2, sub_ne_zero.mpr hF']
    ring
  have hid := standard_secant_y_identity hg1 hg2 hx1 hx2 hx12
    (a := (-34 : ℚ)) (b := 225)
    (ell := (y1 - y2) / (x1 - x2))
    (r := ((y1 - y2) / (x1 - x2)) ^ 2 + 34 - x1 - x2)
    rfl (by ring) hr' h225
  have hid8 := congrArg (fun z : ℚ ↦ z / 8) hid
  have hX := dual_add_x_generic h1 h2 hx1 hx2 hx12 hr hF
  unfold addY negAddY
  rw [fullTwoCurve_negY, isogenousCurve_negY]
  rw [← hX]
  rw [dualX_secant_form hsumEq hr]
  rw [slope_of_X_ne hx12, hslope]
  rw [dualX_secant_form heq1 hx1]
  simp only [dualY, addX, isogenousCurve]
  convert hid8 using 1 <;> ring

/-- The dual point map is additive in the generic affine secant branch. -/
theorem dualPoint_add_generic
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular isogenousCurve x1 y1)
    (h2 : Nonsingular isogenousCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx12 : x1 ≠ x2)
    (hr : addX isogenousCurve x1 x2
        (slope isogenousCurve x1 x2 y1 y2) ≠ 0)
    (hF : dualX x1 y1 ≠ dualX x2 y2) :
    dualPoint
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : IsogenousPoint) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      dualPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        dualPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12]
  have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
  rw [dualPoint_some_of_x_ne_zero hsum hr,
    dualPoint_some_of_x_ne_zero h1 hx1,
    dualPoint_some_of_x_ne_zero h2 hx2]
  change WeierstrassCurve.Affine.Point.some
      (dualX
        (addX isogenousCurve x1 x2 (slope isogenousCurve x1 x2 y1 y2))
        (addY isogenousCurve x1 x2 y1 (slope isogenousCurve x1 x2 y1 y2)))
      (dualY
        (addX isogenousCurve x1 x2 (slope isogenousCurve x1 x2 y1 y2))
        (addY isogenousCurve x1 x2 y1 (slope isogenousCurve x1 x2 y1 y2))) _ =
    (WeierstrassCurve.Affine.Point.some
        (dualX x1 y1) (dualY x1 y1) _ : FullTwoPoint) +
      WeierstrassCurve.Affine.Point.some
        (dualX x2 y2) (dualY x2 y2) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hF,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨dual_add_x_generic h1 h2 hx1 hx2 hx12 hr hF,
    dual_add_y_generic h1 h2 hx1 hx2 hx12 hr hF⟩

private theorem dualPoint_add_of_dualX_eq
    {x1 y1 x2 y2 : ℚ}
    (h1 : Nonsingular isogenousCurve x1 y1)
    (h2 : Nonsingular isogenousCurve x2 y2)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hF : dualX x1 y1 = dualX x2 y2) :
    dualPoint
        ((WeierstrassCurve.Affine.Point.some x1 y1 h1 : IsogenousPoint) +
          WeierstrassCurve.Affine.Point.some x2 y2 h2) =
      dualPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) +
        dualPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
  have hf1 : Nonsingular fullTwoCurve (dualX x1 y1) (dualY x1 y1) :=
    equation_iff_nonsingular.mp
      (dual_equation hx1 (equation_iff_nonsingular.mpr h1))
  have hf2 : Nonsingular fullTwoCurve (dualX x2 y2) (dualY x2 y2) :=
    equation_iff_nonsingular.mp
      (dual_equation hx2 (equation_iff_nonsingular.mpr h2))
  have hKneg : -isogenousKernel = isogenousKernel := by
    rw [neg_eq_iff_add_eq_zero, ← two_nsmul, two_nsmul_isogenousKernel]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (h₁ := hf1) (h₂ := hf2)).mp hF with hsame | hneg
  · have hmap :
        dualPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          dualPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [dualPoint_some_of_x_ne_zero h1 hx1,
        dualPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hsame
    rcases (dualPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (WeierstrassCurve.Affine.Point.some x2 y2 h2)).mp hmap with hQ | hQ
    · exact dualPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inl hQ)))
    · exact dualPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  · have hmapneg :
        dualPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          -dualPoint (WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
      rw [dualPoint_some_of_x_ne_zero h1 hx1,
        dualPoint_some_of_x_ne_zero h2 hx2]
      simpa [WeierstrassCurve.Affine.Point.mk] using hneg
    have hmap :
        dualPoint (WeierstrassCurve.Affine.Point.some x1 y1 h1) =
          dualPoint (-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) := by
      rw [dualPoint_neg]
      exact hmapneg
    rcases (dualPoint_eq_iff
      (WeierstrassCurve.Affine.Point.some x1 y1 h1)
      (-(WeierstrassCurve.Affine.Point.some x2 y2 h2))).mp hmap with hQ | hQ
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : IsogenousPoint) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : IsogenousPoint) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
            congrArg Neg.neg hQ
      exact dualPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inl hQ'))))
    · have hQ' :
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : IsogenousPoint) =
            -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
              isogenousKernel := by
        calc
          (WeierstrassCurve.Affine.Point.some x2 y2 h2 : IsogenousPoint) =
              -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
            (neg_neg _).symm
          _ = -((WeierstrassCurve.Affine.Point.some x1 y1 h1 : IsogenousPoint) +
                isogenousKernel) := by rw [hQ]
          _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
              isogenousKernel := by simp [hKneg, add_comm]
      exact dualPoint_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ')))))

/-- The explicit dual two-isogeny is additive on all rational points. -/
theorem dualPoint_add (P Q : IsogenousPoint) :
    dualPoint (P + Q) = dualPoint P + dualPoint Q := by
  cases P with
  | zero => exact dualPoint_zero_add Q
  | some x1 y1 h1 =>
      cases Q with
      | zero => exact dualPoint_add_zero _
      | some x2 y2 h2 =>
          by_cases hx1 : x1 = 0
          · have hy1 := isogenous_y_zero_of_x_zero h1 hx1
            subst x1
            subst y1
            rw [show
              (WeierstrassCurve.Affine.Point.some 0 0 h1 : IsogenousPoint) =
                isogenousKernel by rfl]
            rw [dualPoint_isogenousKernel_add, dualPoint_isogenousKernel, zero_add]
          · by_cases hx2 : x2 = 0
            · have hy2 := isogenous_y_zero_of_x_zero h2 hx2
              subst x2
              subst y2
              rw [show
                (WeierstrassCurve.Affine.Point.some 0 0 h2 : IsogenousPoint) =
                  isogenousKernel by rfl]
              rw [dualPoint_add_isogenousKernel, dualPoint_isogenousKernel, add_zero]
            · by_cases hx12 : x1 = x2
              · rcases (WeierstrassCurve.Affine.Point.X_eq_iff
                  (h₁ := h1) (h₂ := h2)).mp hx12 with hsame | hneg
                · rw [← hsame]
                  exact dualPoint_add_self _
                · have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 :
                          IsogenousPoint) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 :
                          IsogenousPoint) =
                          -(-(WeierstrassCurve.Affine.Point.some x2 y2 h2)) :=
                        (neg_neg _).symm
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) :=
                        (congrArg Neg.neg hneg).symm
                  rw [hQ]
                  exact dualPoint_add_neg _
              · by_cases hr : addX isogenousCurve x1 x2
                    (slope isogenousCurve x1 x2 y1 y2) = 0
                · have hsum := nonsingular_add h1 h2 (fun hxy ↦ hx12 hxy.1)
                  have hsumY := isogenous_y_zero_of_x_zero hsum hr
                  have hsumK :
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 :
                          IsogenousPoint) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 =
                        isogenousKernel := by
                    change
                      (WeierstrassCurve.Affine.Point.some x1 y1 h1 :
                          IsogenousPoint) +
                          WeierstrassCurve.Affine.Point.some x2 y2 h2 =
                        WeierstrassCurve.Affine.Point.some 0 0 _
                    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12,
                      WeierstrassCurve.Affine.Point.some.injEq]
                    exact ⟨hr, hsumY⟩
                  have hQ :
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 :
                          IsogenousPoint) =
                        -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          isogenousKernel := by
                    calc
                      (WeierstrassCurve.Affine.Point.some x2 y2 h2 :
                          IsogenousPoint) =
                          -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                            ((WeierstrassCurve.Affine.Point.some x1 y1 h1 :
                                IsogenousPoint) +
                              WeierstrassCurve.Affine.Point.some x2 y2 h2) := by
                        symm
                        rw [← add_assoc, neg_add_cancel, zero_add]
                      _ = -(WeierstrassCurve.Affine.Point.some x1 y1 h1) +
                          isogenousKernel := by rw [hsumK]
                  exact dualPoint_add_of_basic_or_kernel_relation _ _
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))
                · by_cases hF : dualX x1 y1 = dualX x2 y2
                  · exact dualPoint_add_of_dualX_eq h1 h2 hx1 hx2 hF
                  · exact dualPoint_add_generic h1 h2 hx1 hx2 hx12 hr hF

/-- The explicit dual two-isogeny as an additive homomorphism. -/
noncomputable def dualPointHom : IsogenousPoint →+ FullTwoPoint where
  toFun := dualPoint
  map_zero' := dualPoint_zero
  map_add' := dualPoint_add

@[simp] theorem dualPointHom_apply (P : IsogenousPoint) :
    dualPointHom P = dualPoint P := rfl

end MazurProof.RationalPointsN15IsogenyHom
