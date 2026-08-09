import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# Parameter action on the primitive order-25 Tate locus

Changing the marked generator from `P` to `2P` induces a rational
self-correspondence of the order-25 Tate parameter curve.  This file derives
the first explicit parameter formulas from the actual Weierstrass
normalization used by `TateNormalFormBridge`.

For `P=(0,0)` on `E(b,c)`, the doubled point is `(b,bc)`.  Translating this
point to the origin with horizontal tangent and applying the standard Tate
scaling produces

`B₂ = b F₆³ / c⁸`,
`C₂ = (c⁴ + (2b+c²-c)F₆) / c⁴`.

The primitive equation itself supplies both required denominators: setting
`c=0` gives `F25=b²⁵`, while setting `F6=0`, equivalently `b=c+c²`, gives
`F25=c⁵⁰`.  These are literal polynomial specializations, not consequences
of the desired rational-point classification.
-/

namespace MazurProof.TateOrder25ParameterAction

open Scratch.TateZ2xZ10Reduction
open scoped WeierstrassCurve.Affine

noncomputable section

/-! ## Denominators forced by the primitive equation -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- A primitive order-25 Tate point cannot lie on `c = 0`: there the stored
primitive division polynomial specializes to `b^25`. -/
theorem c_ne_zero_of_primitive25
    {b c : ℚ} (hb : b ≠ 0)
    (h25 : TateOrder25Factor.F25 b c = 0) :
    c ≠ 0 := by
  intro hc
  subst c
  have hb25 : b ^ 25 = 0 := by
    simpa [TateOrder25Factor.F25] using h25
  exact (pow_ne_zero 25 hb) hb25

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- On the divisor `F6=0`, the primitive order-25 polynomial specializes to
`c^50`.  Thus this divisor is disjoint from the locus `F25=0`, `b≠0`. -/
theorem F6_ne_zero_of_primitive25
    {b c : ℚ} (hb : b ≠ 0)
    (h25 : TateOrder25Factor.F25 b c = 0) :
    TateNFDivision.F6 b c ≠ 0 := by
  intro h6
  have hb_formula : b = c + c ^ 2 := by
    dsimp [TateNFDivision.F6] at h6
    linarith
  have hspecial : TateOrder25Factor.F25 (c + c ^ 2) c = c ^ 50 := by
    simp [TateOrder25Factor.F25]
    ring
  have hc50 : c ^ 50 = 0 := by
    rw [← hspecial, ← hb_formula]
    exact h25
  have hc : c = 0 := by
    by_contra hc
    exact (pow_ne_zero 50 hc) hc50
  apply hb
  rw [hb_formula, hc]
  norm_num

/-! ## Explicit re-normalization at the doubled point -/

private theorem tateDouble_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateOriginDivision.W b c)] :
    WeierstrassCurve.Affine.Nonsingular
      (TateOriginDivision.W b c) b (b * c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [TateOriginDivision.W, tateNormalFormCurve]
  ring

/-- The affine point `(b,bc)` on the original Tate normal form. -/
def tateDoublePoint25
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateOriginDivision.W b c)] :
    WeierstrassCurve.Affine.Point (TateOriginDivision.W b c) :=
  WeierstrassCurve.Affine.Point.some b (b * c)
    (tateDouble_nonsingular b c)

/-- The point `(b,bc)` is literally twice the marked Tate origin.  This
identifies the point used by the following normalization with the changed
generator `2P`, rather than merely choosing another point on the curve. -/
theorem two_nsmul_tateOrigin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateOriginDivision.W b c)]
    (hb : b ≠ 0) :
    (2 : ℕ) • TateOriginDivision.tateOrigin b c =
      tateDoublePoint25 b c := by
  rw [two_nsmul]
  have hy :
      (0 : ℚ) ≠
        WeierstrassCurve.Affine.negY (TateOriginDivision.W b c) 0 0 := by
    simpa [TateOriginDivision.W, tateNormalFormCurve] using hb.symm
  change
    WeierstrassCurve.Affine.Point.some 0 0 _ +
      WeierstrassCurve.Affine.Point.some 0 0 _ = tateDoublePoint25 b c
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  unfold tateDoublePoint25
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [TateOriginDivision.W, tateNormalFormCurve,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [TateOriginDivision.W, tateNormalFormCurve,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    ring

/-- Tangent slope used after translating the doubled point `(b,bc)` to the
origin. -/
def tateDoubleSlope25 (b c : ℚ) : ℚ :=
  (b - c + c ^ 2) / c

/-- First Tate parameter obtained by re-normalizing with marked point `2P`. -/
def tateDoubleB25 (b c : ℚ) : ℚ :=
  b * TateNFDivision.F6 b c ^ 3 / c ^ 8

/-- Second Tate parameter obtained by re-normalizing with marked point `2P`. -/
def tateDoubleC25 (b c : ℚ) : ℚ :=
  (c ^ 4 + (2 * b + c ^ 2 - c) * TateNFDivision.F6 b c) / c ^ 4

/-- The translation used for the `2P` normalization sends the doubled
point's horizontal coordinate to zero. -/
theorem translateAtTwo_pointX (b c : ℚ) :
    variableChangePointX
        (translateToOriginTangent
          (TateOriginDivision.W b c) b (b * c)) b = 0 := by
  simp [variableChangePointX, translateToOriginTangent]

/-- The same translation sends the doubled point's vertical coordinate to
zero; the subsequent Tate scaling therefore keeps it at the marked origin. -/
theorem translateAtTwo_pointY (b c : ℚ) :
    variableChangePointY
        (translateToOriginTangent
          (TateOriginDivision.W b c) b (b * c)) b (b * c) = 0 := by
  simp [variableChangePointY, translateToOriginTangent]

/-- The general tangent formula at the actual doubled point `(b,bc)` reduces
to the displayed order-25 slope. -/
theorem tangentSlope_at_tateDouble
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    tangentSlope (TateOriginDivision.W b c) b (b * c) =
      tateDoubleSlope25 b c := by
  change
    (3 * b ^ 2 + 2 * (-b) * b + 0 - (1 - c) * (b * c)) /
        (2 * (b * c) + (1 - c) * b + (-b)) =
      (b - c + c ^ 2) / c
  rw [show 3 * b ^ 2 + 2 * (-b) * b + 0 - (1 - c) * (b * c) =
      b * (b - c + c ^ 2) by ring]
  rw [show 2 * (b * c) + (1 - c) * b + (-b) = b * c by ring]
  field_simp [hb, hc]

/-- After translation at `(b,bc)`, the linear Weierstrass coefficient has
the numerator used in the formula for `C₂`. -/
theorem translatedAtTwo_a1
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((translateToOriginTangent
        (TateOriginDivision.W b c) b (b * c)) •
      TateOriginDivision.W b c).a₁ =
        (2 * b + c ^ 2 - c) / c := by
  rw [translateToOriginTangent_a₁,
    tangentSlope_at_tateDouble b c hb hc]
  simp [TateOriginDivision.W, tateNormalFormCurve, tateDoubleSlope25]
  field_simp [hc]
  ring

/-- The translated quadratic coefficient is `-b F6/c²`; in particular it is
nonzero on the primitive locus. -/
theorem translatedAtTwo_a2
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((translateToOriginTangent
        (TateOriginDivision.W b c) b (b * c)) •
      TateOriginDivision.W b c).a₂ =
        -(b * TateNFDivision.F6 b c / c ^ 2) := by
  rw [translateToOriginTangent_a₂,
    tangentSlope_at_tateDouble b c hb hc]
  simp [TateOriginDivision.W, tateNormalFormCurve, tateDoubleSlope25,
    TateNFDivision.F6]
  field_simp [hc]
  ring

/-- The translated cubic coefficient at `(b,bc)` is exactly `bc`. -/
theorem translatedAtTwo_a3 (b c : ℚ) :
    ((translateToOriginTangent
        (TateOriginDivision.W b c) b (b * c)) •
      TateOriginDivision.W b c).a₃ = b * c := by
  rw [translateToOriginTangent_a₃]
  simp [TateOriginDivision.W, tateNormalFormCurve]
  ring

/-- The Tate scaling ratio `a₃/a₂` after translation at `2P`. -/
def tateDoubleRho25 (b c : ℚ) : ℚ :=
  -(c ^ 3 / TateNFDivision.F6 b c)

/-- The coefficient ratio used by the standard Tate normalizer equals the
explicit scaling ratio `-c³/F6`. -/
theorem translatedAtTwo_a3_div_a2
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    let W₁ :=
      (translateToOriginTangent
        (TateOriginDivision.W b c) b (b * c)) •
      TateOriginDivision.W b c
    W₁.a₃ / W₁.a₂ = tateDoubleRho25 b c := by
  dsimp
  rw [translatedAtTwo_a2 b c hb hc, translatedAtTwo_a3]
  simp [tateDoubleRho25]
  field_simp [hb, hc]

/-- Scaling the translated curve by the explicit ratio produces exactly the
Tate normal form with parameters `B₂,C₂`.  This verifies the candidate
parameter action against the project's actual Weierstrass normalization. -/
theorem normalizedAtTwo_curve_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h6 : TateNFDivision.F6 b c ≠ 0) :
    let W₁ :=
      (translateToOriginTangent
        (TateOriginDivision.W b c) b (b * c)) •
      TateOriginDivision.W b c
    (scaleByRho (tateDoubleRho25 b c)
        (by exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 3 hc) h6))) • W₁ =
      TateOriginDivision.W (tateDoubleB25 b c) (tateDoubleC25 b c) := by
  dsimp
  have hpoint :
      WeierstrassCurve.Affine.Equation
        (TateOriginDivision.W b c) b (b * c) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [TateOriginDivision.W, tateNormalFormCurve]
    ring
  have hden :
      2 * (b * c) + (TateOriginDivision.W b c).a₁ * b +
          (TateOriginDivision.W b c).a₃ ≠ 0 := by
    rw [show
      2 * (b * c) + (TateOriginDivision.W b c).a₁ * b +
          (TateOriginDivision.W b c).a₃ = b * c by
        simp [TateOriginDivision.W, tateNormalFormCurve]
        ring]
    exact mul_ne_zero hb hc
  have hW₁a4 :
      ((translateToOriginTangent
          (TateOriginDivision.W b c) b (b * c)) •
        TateOriginDivision.W b c).a₄ = 0 :=
    translateToOriginTangent_a₄_eq_zero
      (TateOriginDivision.W b c) hden
  have hW₁a6 :
      ((translateToOriginTangent
          (TateOriginDivision.W b c) b (b * c)) •
        TateOriginDivision.W b c).a₆ = 0 :=
    translateToOriginTangent_a₆_eq_zero
      (TateOriginDivision.W b c) hpoint
  ext
  · rw [WeierstrassCurve.variableChange_a₁,
      translatedAtTwo_a1 b c hb hc]
    simp [scaleByRho, tateDoubleRho25, tateDoubleC25,
      TateOriginDivision.W, tateNormalFormCurve, TateNFDivision.F6]
    field_simp [hc, h6]
    all_goals ring
  · rw [scaleByRho_a₂, translatedAtTwo_a2 b c hb hc]
    simp [tateDoubleRho25, tateDoubleB25,
      TateOriginDivision.W, tateNormalFormCurve]
    field_simp [hb, hc, h6]
  · rw [scaleByRho_a₃, translatedAtTwo_a3]
    simp [tateDoubleRho25, tateDoubleB25,
      TateOriginDivision.W, tateNormalFormCurve]
    field_simp [hb, hc, h6]
  · rw [WeierstrassCurve.variableChange_a₄, hW₁a4]
    simp [scaleByRho, TateOriginDivision.W, tateNormalFormCurve]
  · rw [WeierstrassCurve.variableChange_a₆, hW₁a6]
    simp [scaleByRho, TateOriginDivision.W, tateNormalFormCurve]

end

end MazurProof.TateOrder25ParameterAction
