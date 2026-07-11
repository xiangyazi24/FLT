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

end MazurProof.RationalPointsN15IsogenyHom
