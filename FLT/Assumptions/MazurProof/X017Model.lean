import FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints
import FLT.Assumptions.MazurProof.VeluTwoIsogeny

/-!
# The explicit genus-one model used for X₀(17)

This file verifies concrete Weierstrass-curve algebra for the integral
genus-one equation

`y² + xy + y = x³ - x² - x - 14`.

It constructs an additive equivalence with the standard rational
two-isogeny model `Y² = X(X² + 30X + 289)` and proves that the visible point
`(17,136)` on the standard model has exact order four.  No modular
interpretation of the displayed curve is asserted here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017Model

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.N18RouteC.VariableChangePoints

noncomputable section

/-- The integral genus-one equation used as the concrete `X₀(17)` model. -/
@[reducible] def X017 : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := -1
  a₆ := -14

/-- The affine equation of the integral model in ordinary coordinates. -/
@[simp] theorem X017_equation_iff (x y : ℚ) :
    Equation X017 x y ↔
      y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14 := by
  rw [equation_iff]
  norm_num [X017]
  constructor <;> intro h <;> nlinarith

/-- The integral model has discriminant `-17^4`. -/
theorem X017_delta : X017.Δ = -(17 : ℚ) ^ 4 := by
  norm_num [X017, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- The nonzero discriminant makes the integral model elliptic over `ℚ`. -/
instance X017_isElliptic : X017.IsElliptic := by
  constructor
  rw [X017_delta]
  norm_num

/-- Rational variable change whose affine coordinates are
`U = 4x - 1` and `V = 8y + 4x + 4`. -/
def toShortChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 1 / 4
  s := -1 / 2
  t := -5 / 8

/-- The horizontal coordinate of the variable change is `4x-1`. -/
@[simp] theorem toShortChange_x (x : ℚ) :
    variableChangePointX toShortChange x = 4 * x - 1 := by
  norm_num [variableChangePointX, toShortChange]
  ring

/-- The vertical coordinate of the variable change is `8y+4x+4`. -/
@[simp] theorem toShortChange_y (x y : ℚ) :
    variableChangePointY toShortChange x y = 8 * y + 4 * x + 4 := by
  norm_num [variableChangePointY, toShortChange]
  ring

/-- The short Weierstrass model `V² = U³ - 11U - 890`. -/
@[reducible] def short : WeierstrassCurve ℚ :=
  shortWS (-11) (-890)

/-- The displayed variable change carries the integral model to `short`. -/
theorem toShortChange_curve :
    toShortChange • X017 = short := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> norm_num [toShortChange, X017, short, shortWS]

/-- The short model is elliptic because it is variable-change equivalent to
the nonsingular integral model. -/
instance short_isElliptic : short.IsElliptic := by
  rw [← toShortChange_curve]
  infer_instance

/-- The rational two-torsion root `U=10` on the short model. -/
theorem ten_is_root :
    (10 : ℚ) ^ 3 + (-11) * 10 + (-890) = 0 := by
  norm_num

/-- Vélu quotient of the short model by its visible rational two-torsion. -/
@[reducible] def shortDual : WeierstrassCurve ℚ :=
  veluQuotCurve (-11) (-890) 10

/-- The Vélu quotient remains elliptic. -/
instance shortDual_isElliptic : shortDual.IsElliptic :=
  veluQuotCurve_isElliptic ten_is_root
    (inferInstance : short.IsElliptic)

/-- The linear coefficient `30` in the translated two-isogeny model. -/
abbrev a17 : ℚ :=
  3 * 10

/-- The constant coefficient `289` in the translated two-isogeny model. -/
abbrev b17 : ℚ :=
  veluT (-11) 10

/-- Translating the source two-torsion point to zero gives
`Y² = X(X² + 30X + 289)`.

The coefficients retain the expressions produced by the general Vélu API so
that its source equivalence is definitionally applicable. -/
@[reducible] def standard : WeierstrassCurve ℚ :=
  StandardTwoIsogeny.curve a17 b17

/-- The standard dual is
`Y² = X(X² - 60X - 256) = X(X-64)(X+4)`. -/
@[reducible] def standardDual : WeierstrassCurve ℚ :=
  StandardTwoIsogeny.curve (-2 * a17) (a17 ^ 2 - 4 * b17)

/-- The standard source change identifies `short` with `standard`. -/
theorem sourceChange_curve :
    StandardTwoIsogeny.sourceChange 10 • short = standard := by
  simpa only [short, standard, a17, b17] using
    StandardTwoIsogeny.sourceChange_eq ten_is_root

/-- The standard target change identifies the Vélu quotient with
`standardDual`. -/
theorem targetChange_curve :
    StandardTwoIsogeny.targetChange 10 • shortDual = standardDual := by
  simpa only [shortDual, standardDual, a17, b17] using
    StandardTwoIsogeny.targetChange_eq ten_is_root

/-- The standard source model is elliptic. -/
instance standard_isElliptic : standard.IsElliptic := by
  rw [← sourceChange_curve]
  infer_instance

/-- The standard dual model is elliptic. -/
instance standardDual_isElliptic : standardDual.IsElliptic := by
  rw [← targetChange_curve]
  infer_instance

/-- Additive equivalence from the integral model to the short model. -/
noncomputable def X017ToShort : Point X017 ≃+ Point short :=
  (variableChangePointAddEquiv X017 toShortChange).trans
    (StandardTwoIsogeny.curveCastAddEquiv toShortChange_curve)

/-- Additive equivalence from the short model to the standard source model. -/
noncomputable def ShortToStandard : Point short ≃+ Point standard := by
  simpa only [short, standard, a17, b17] using
    StandardTwoIsogeny.sourceEquiv ten_is_root

/-- Additive equivalence from the integral model to the standard
two-isogeny source model. -/
noncomputable def X017ToStandard : Point X017 ≃+ Point standard :=
  X017ToShort.trans ShortToStandard

/-- The coordinates `(17,136)` satisfy the standard source equation and are
nonsingular. -/
private theorem T_nonsingular :
    Nonsingular standard 17 136 := by
  apply equation_iff_nonsingular.mp
  rw [StandardTwoIsogeny.curve_equation]
  norm_num [a17, b17, veluT]

/-- The visible standard-model point corresponding to `(7,13)` on the
integral equation. -/
noncomputable def T : Point standard :=
  Point.some 17 136 T_nonsingular

/-- The visible rational two-torsion point `(0,0)` on the standard source. -/
noncomputable def K : Point standard :=
  StandardTwoIsogeny.kernelPoint a17 b17

/-- The coordinates `(64,0)` define a nonsingular point on the standard
dual curve. -/
private theorem U_nonsingular :
    Nonsingular standardDual 64 0 := by
  apply equation_iff_nonsingular.mp
  rw [StandardTwoIsogeny.curve_equation]
  norm_num [a17, b17, veluT]

/-- The forward two-isogeny image of `T` on the standard dual curve. -/
noncomputable def U : Point standardDual :=
  Point.some 64 0 U_nonsingular

/-- The standard forward two-isogeny sends `T` to `(64,0)`. -/
theorem pointMap_T :
    StandardTwoIsogeny.pointMap T = U := by
  change
    StandardTwoIsogeny.pointMap (a := a17) (b := b17)
        (Point.some 17 136 T_nonsingular) =
      Point.some 64 0 U_nonsingular
  rw [StandardTwoIsogeny.pointMap_some T_nonsingular (by norm_num)]
  rw [Point.some.injEq]
  constructor
  · norm_num [a17, b17, veluT, StandardTwoIsogeny.fx]
  · norm_num [a17, b17, veluT, StandardTwoIsogeny.fy]

/-- The standard dual isogeny sends `(64,0)` to the source kernel point. -/
theorem dualPoint_U :
    StandardTwoIsogeny.dualPoint U = K := by
  change
    StandardTwoIsogeny.dualPoint (a := a17) (b := b17)
        (Point.some 64 0 U_nonsingular) =
      StandardTwoIsogeny.kernelPoint a17 b17
  rw [StandardTwoIsogeny.dualPoint_some U_nonsingular (by norm_num)]
  unfold StandardTwoIsogeny.kernelPoint
  rw [Point.some.injEq]
  constructor
  · norm_num [StandardTwoIsogeny.dx]
  · norm_num [StandardTwoIsogeny.dy]

/-- The dual-composition theorem computes `2T` as the visible kernel point. -/
theorem two_nsmul_T_eq_K : 2 • T = K := by
  have h := StandardTwoIsogeny.dual_comp_pointMap T
  rw [pointMap_T, dualPoint_U] at h
  exact h.symm

/-- The visible point `T` is not the point at infinity. -/
theorem T_ne_zero : T ≠ 0 :=
  Point.some_ne_zero _

/-- The visible kernel point is not the point at infinity. -/
theorem K_ne_zero : K ≠ 0 := by
  unfold K StandardTwoIsogeny.kernelPoint
  exact Point.some_ne_zero _

/-- The visible point `T` has exact additive order four. -/
theorem T_order_four : addOrderOf T = 4 := by
  have h2K : 2 • K = 0 := by
    change 2 • StandardTwoIsogeny.kernelPoint a17 b17 = 0
    simpa [two_nsmul] using
      (StandardTwoIsogeny.kernel_add_self (a := a17) (b := b17))
  have h4 : 4 • T = 0 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_nsmul,
      two_nsmul_T_eq_K, h2K]
  apply (addOrderOf_eq_iff (x := T) (by norm_num)).2
  refine ⟨h4, ?_⟩
  intro m hm hmpos
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl
  · simpa using T_ne_zero
  · simpa [two_nsmul_T_eq_K] using K_ne_zero
  · intro h3
    have h43 : 4 • T = 3 • T + T := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
    rw [h4, h3, zero_add] at h43
    exact T_ne_zero h43.symm

end

end MazurProof.X017Model
