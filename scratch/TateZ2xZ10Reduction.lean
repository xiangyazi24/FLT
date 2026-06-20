import Mathlib
import scratch.TateZ2xZ10

/-!
# Tate-normal-form reduction layer for `ZMod 2 × ZMod 10`

This file builds the forward-direction reduction up to the current formal wall.

API survey, from the local tree and Mathlib as used here:

* Nonzero affine coordinates.  `WeierstrassCurve.Affine.Point W` is the
  inductive type `zero | some x y h`.  For elliptic curves, Mathlib also has
  `WeierstrassCurve.Affine.Point.pointEquiv`, sending a point to
  `WithZero {xy : R × R // W.Equation xy.1 xy.2}`, plus `Point.mk`,
  `Point.some_ne_zero`, and `Point.xRep`.  There is no extra abstraction needed
  to extract `(x,y)` from a proof `P ≠ 0`: case-splitting on `P` gives the
  affine coordinates.

* Variable changes.  `WeierstrassCurve.VariableChange R` exists and acts on
  Weierstrass curves by `(X,Y) ↦ (u^2 X + r, u^3 Y + u^2 s X + t)`.  Mathlib
  provides the coefficient formulas `variableChange_a₁` through
  `variableChange_a₆`, preservation of `IsElliptic`, and `variableChange_j`.
  `Affine.Basic` has specialized equation/nonsingularity lemmas for translating
  a point to `(0,0)`.

  Missing for the descent bridge: a point-level additive equivalence for a
  general variable change.  The needed shape is recorded below as the single
  `sorry` helper:

  ```
  noncomputable def variableChangePointAddEquiv
      (W : WeierstrassCurve ℚ) [W.IsElliptic]
      (C : WeierstrassCurve.VariableChange ℚ) :
      WeierstrassCurve.Affine.Point W ≃+
        WeierstrassCurve.Affine.Point (C • W)
  ```

  together with simp lemmas saying that it sends an affine point `(x,y)` to the
  inverse coordinates `(X,Y)` satisfying
  `x = C.u^2 * X + C.r` and `y = C.u^3 * Y + C.u^2 * C.s * X + C.t`.
  This would transport `n • P`, `addOrderOf P`, and the independent 2-torsion
  point through the Tate-coordinate normalization.

* Computing `n • P`.  The affine point file has explicit group-law lemmas:
  `Point.add_of_X_ne`, `Point.add_of_Y_eq`, `Point.add_self_of_Y_eq`,
  `Point.add_self_of_Y_ne`, and the underlying formulas `slope`, `addX`,
  `addY`.  This supports direct coordinate calculations, as in the existing
  obstruction files.  Mathlib does not provide Tate normal form, Kubert's
  order-10 table, or a canned theorem that a point of order `10` can be
  normalized to `(0,0)` with the roadmap's `b,c` formulas.

The proven content below is split accordingly:

* the pure finite-group extraction from an injective `ZMod 2 × ZMod 10`;
* raw Tate-normal-form and change-of-variable algebra;
* one precisely named helper marking the missing point-level group-law
  preservation/normalization theorem.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The Tate normal form `y^2 + (1-c)xy - by = x^3 - bx^2`. -/
def tateNormalFormCurve (b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

@[simp] lemma tateNormalFormCurve_a₁ (b c : ℚ) :
    (tateNormalFormCurve b c).a₁ = 1 - c := rfl

@[simp] lemma tateNormalFormCurve_a₂ (b c : ℚ) :
    (tateNormalFormCurve b c).a₂ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₃ (b c : ℚ) :
    (tateNormalFormCurve b c).a₃ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₄ (b c : ℚ) :
    (tateNormalFormCurve b c).a₄ = 0 := rfl

@[simp] lemma tateNormalFormCurve_a₆ (b c : ℚ) :
    (tateNormalFormCurve b c).a₆ = 0 := rfl

/-- The order-10 Tate condition from the roadmap. -/
def Phi10 (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c
    + b * c ^ 4 + 3 * b * c ^ 3 + b * c ^ 2 + c ^ 5

/-- The two-torsion cubic specialized to Tate normal form. -/
def tateTwoTorsionCubic (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

/-- The rational `u` parameter recovered from Tate parameters `b,c`. -/
def uOfTateParameters (b c : ℚ) : ℚ :=
  (5 * b ^ 2 - 2 * b * c ^ 2 - 6 * b * c - 2 * c ^ 3 + c ^ 2) / (b - c) ^ 2

/-- Tangent slope at `(x₀,y₀)` in a general Weierstrass equation. -/
def tangentSlope (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) : ℚ :=
  (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
    / (2 * y₀ + W.a₁ * x₀ + W.a₃)

/-- The translation/shear sending `(x₀,y₀)` to `(0,0)` with tangent `Y=0`. -/
def translateToOriginTangent (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := x₀
  s := tangentSlope W x₀ y₀
  t := y₀

@[simp] lemma translateToOriginTangent_a₁ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₁ =
      W.a₁ + 2 * tangentSlope W x₀ y₀ := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp [translateToOriginTangent]

@[simp] lemma translateToOriginTangent_a₂ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₂ =
      W.a₂ - tangentSlope W x₀ y₀ * W.a₁ + 3 * x₀ - tangentSlope W x₀ y₀ ^ 2 := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [translateToOriginTangent]

@[simp] lemma translateToOriginTangent_a₃ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₃ =
      W.a₃ + W.a₁ * x₀ + 2 * y₀ := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [translateToOriginTangent]
  ring

/-- If `(x₀,y₀)` lies on `W`, the translated curve has constant term zero. -/
lemma translateToOriginTangent_a₆_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hP : WeierstrassCurve.Affine.Equation W x₀ y₀) :
    ((translateToOriginTangent W x₀ y₀) • W).a₆ = 0 := by
  rw [WeierstrassCurve.variableChange_a₆]
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  simp [translateToOriginTangent]
  nlinarith

/-- If the point is not 2-torsion, the tangent choice kills the linear `X` term. -/
lemma translateToOriginTangent_a₄_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hden : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    ((translateToOriginTangent W x₀ y₀) • W).a₄ = 0 := by
  have hs :
      tangentSlope W x₀ y₀ * (2 * y₀ + W.a₁ * x₀ + W.a₃) =
        3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
    unfold tangentSlope
    exact div_mul_cancel₀ _ hden
  rw [WeierstrassCurve.variableChange_a₄]
  simp [translateToOriginTangent]
  linear_combination -hs

/-- Scaling `X = ρ^2 X'`, `Y = ρ^3 Y'`. -/
def scaleByRho (ρ : ℚ) (hρ : ρ ≠ 0) : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 ρ hρ
  r := 0
  s := 0
  t := 0

lemma scaleByRho_a₂ (W : WeierstrassCurve ℚ) (ρ : ℚ) (hρ : ρ ≠ 0) :
    ((scaleByRho ρ hρ) • W).a₂ = W.a₂ / ρ ^ 2 := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [scaleByRho, div_eq_mul_inv, inv_pow]
  ring

lemma scaleByRho_a₃ (W : WeierstrassCurve ℚ) (ρ : ℚ) (hρ : ρ ≠ 0) :
    ((scaleByRho ρ hρ) • W).a₃ = W.a₃ / ρ ^ 3 := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [scaleByRho, div_eq_mul_inv, inv_pow]
  ring

lemma scaleByTateRho_a₂
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₂ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleByRho_a₂]
  field_simp [ha₂, ha₃]

lemma scaleByTateRho_a₃
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₃ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleByRho_a₃]
  field_simp [ha₂, ha₃]

/-- Tate `b` after the roadmap's scaling step. -/
def tateBFromCoefficients (a₂' a₃' : ℚ) : ℚ :=
  -a₂' ^ 3 / a₃' ^ 2

/-- Tate `c` after the roadmap's scaling step. -/
def tateCFromCoefficients (a₁' a₂' a₃' : ℚ) : ℚ :=
  1 - a₁' * a₂' / a₃'

/-- The transformed `x`-coordinate of an auxiliary point under the scaling step. -/
def scaledAuxiliaryX (xTold x₀ ρ : ℚ) : ℚ :=
  (xTold - x₀) / ρ ^ 2

lemma Phi10_b10_c10_eq_zero (u : ℚ) (hu : u ≠ 0)
    (_hD : u ^ 2 - 4 * u - 1 ≠ 0) :
    Phi10 (b10 u) (c10 u) = 0 := by
  unfold Phi10 b10 c10
  field_simp [hu, _hD]
  ring

/--
Pure group-theory extraction from an injective `ZMod 2 × ZMod 10`.

Lean's additive order is `addOrderOf`; this is the additive version of the
roadmap's `orderOf P = 10`.
-/
theorem injective_Z2xZ10_gives_order10_and_independent_2torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let P := f ((0 : ZMod 2), (1 : ZMod 10))
    let T := f ((1 : ZMod 2), (0 : ZMod 10))
    addOrderOf P = 10 ∧
      (2 : ℕ) • T = 0 ∧ T ≠ 0 ∧
      (5 : ℕ) • P = f ((0 : ZMod 2), (5 : ZMod 10)) ∧
      (5 : ℕ) • P ≠ 0 ∧
      (2 : ℕ) • ((5 : ℕ) • P) = 0 ∧
      T ≠ (5 : ℕ) • P := by
  classical
  let p0 : ZMod 2 × ZMod 10 := ((0 : ZMod 2), (1 : ZMod 10))
  let t0 : ZMod 2 × ZMod 10 := ((1 : ZMod 2), (0 : ZMod 10))
  let p5 : ZMod 2 × ZMod 10 := ((0 : ZMod 2), (5 : ZMod 10))
  have hp0_order : addOrderOf p0 = 10 := by
    simp [p0, Prod.addOrderOf_mk]
  have hP_order : addOrderOf (f p0) = 10 := by
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
  have hp5_eq : (5 : ℕ) • p0 = p5 := by
    decide
  have h5P_eq : (5 : ℕ) • f p0 = f p5 := by
    rw [← f.map_nsmul, hp5_eq]
  have hp5_ne_zero : p5 ≠ 0 := by
    decide
  have h5P_ne_zero : (5 : ℕ) • f p0 ≠ 0 := by
    intro h
    rw [h5P_eq] at h
    exact hp5_ne_zero (hf (by simpa using h))
  have hp5_two : (2 : ℕ) • p5 = 0 := by
    decide
  have h5P_two : (2 : ℕ) • ((5 : ℕ) • f p0) = 0 := by
    rw [h5P_eq, ← f.map_nsmul, hp5_two, map_zero]
  have ht0_ne_p5 : t0 ≠ p5 := by
    decide
  have hT_ne_5P : f t0 ≠ (5 : ℕ) • f p0 := by
    intro h
    rw [h5P_eq] at h
    exact ht0_ne_p5 (hf h)
  simpa [p0, t0, p5] using
    And.intro hP_order <|
      And.intro hT_two <|
      And.intro hT_ne_zero <|
      And.intro h5P_eq <|
      And.intro h5P_ne_zero <|
      And.intro h5P_two hT_ne_5P

/--
Precise formal wall: a variable change should give an additive equivalence on
affine point groups.  Mathlib currently has the curve-level action and
coefficient formulas, but not this point-level transport API.
-/
noncomputable def variableChangePointAddEquiv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point (C • W) := by
  sorry

end

end Scratch.TateZ2xZ10Reduction
