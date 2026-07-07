import Mathlib
import FLT.Assumptions.MazurProof.RealTopologyS3
import FLT.Assumptions.MazurProof.RealTorsionBound
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# No full 4-torsion: the elementary halving obstruction

This file isolates the elementary part of the standard proof that full
`(Z / 4Z)^2` rational torsion is impossible over `Q`.

The only geometric input left as a seam is the classical halving criterion:
for `y^2 = (x - e₁)(x - e₂)(x - e₃)`, the branch point `(eᵢ, 0)` is a double
over `Q` iff both differences `eᵢ - eⱼ` and `eᵢ - eₖ` are rational squares.

Everything after that criterion is proved here: two distinct branch points
being doubles force both `d` and `-d` to be rational squares, hence force `-1`
to be a rational square.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.NoFull4Torsion

/-- The short Weierstrass model over `Q`: `y^2 = x^3 + A*x^2 + B*x`. -/
def shortWQ (A B : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0
    a₂ := A
    a₃ := 0
    a₄ := B
    a₆ := 0 }

/-- The cubic on the right-hand side of `shortWQ`. -/
def shortCubicQ (A B x : ℚ) : ℚ :=
  x ^ 3 + A * x ^ 2 + B * x

@[simp] theorem shortWQ_equation_iff {A B x y : ℚ} :
    WeierstrassCurve.Affine.Equation (shortWQ A B) x y ↔
      y ^ 2 = shortCubicQ A B x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortWQ, shortCubicQ]

theorem shortCubicQ_eq_x_mul_quadratic (A B x : ℚ) :
    shortCubicQ A B x = x * (x ^ 2 + A * x + B) := by
  simp [shortCubicQ]
  ring

theorem shortWQ_baseChange_real (A B : ℚ) :
    (shortWQ A B)⁄ℝ = MazurProof.RealTopology.shortW (A : ℝ) (B : ℝ) := by
  ext <;> simp [shortWQ, MazurProof.RealTopology.shortW, WeierstrassCurve.baseChange]

theorem real_shortWQ_discriminant (A B : ℚ) :
    ((shortWQ A B)⁄ℝ).Δ =
      16 * (B : ℝ) ^ 2 * ((A : ℝ) ^ 2 - 4 * (B : ℝ)) := by
  rw [shortWQ_baseChange_real]
  simp [MazurProof.RealTopology.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A rational number is a rational square. -/
def IsRatSquare (q : ℚ) : Prop :=
  ∃ r : ℚ, r ^ 2 = q

/--
The nonzero 2-torsion of `shortWQ A B` is rational exactly when the quadratic
factor `x^2 + A*x + B` splits over `Q`.
-/
def ShortWFullTwoTorsionRational (A B : ℚ) : Prop :=
  ∃ e₂ e₃ : ℚ, e₂ + e₃ = -A ∧ e₂ * e₃ = B

theorem shortCubicQ_factor_of_quadratic_roots
    {A B e₂ e₃ : ℚ} (hsum : e₂ + e₃ = -A) (hprod : e₂ * e₃ = B)
    (x : ℚ) :
    shortCubicQ A B x = x * (x - e₂) * (x - e₃) := by
  have hA : A = -(e₂ + e₃) := by linarith
  have hB : B = e₂ * e₃ := hprod.symm
  rw [hA, hB]
  simp [shortCubicQ]
  ring

theorem shortW_full_two_torsion_rational_iff_discriminant_square (A B : ℚ) :
    ShortWFullTwoTorsionRational A B ↔ IsRatSquare (A ^ 2 - 4 * B) := by
  constructor
  · rintro ⟨e₂, e₃, hsum, hprod⟩
    refine ⟨e₂ - e₃, ?_⟩
    have hA : A = -(e₂ + e₃) := by linarith
    have hB : B = e₂ * e₃ := hprod.symm
    rw [hA, hB]
    ring
  · rintro ⟨d, hd⟩
    refine ⟨(-A + d) / 2, (-A - d) / 2, ?_, ?_⟩
    · ring
    · have h4 : (4 : ℚ) ≠ 0 := by norm_num
      field_simp [h4]
      nlinarith

theorem rat_neg_one_not_square : ¬ IsRatSquare (-1) := by
  rintro ⟨r, hr⟩
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) ^ 2 := sq_nonneg _
  have hsq : (r : ℝ) ^ 2 = (-1 : ℝ) := by
    exact_mod_cast hr
  linarith

theorem rat_neg_one_square_of_square_and_neg_square
    {d : ℚ} (hd : d ≠ 0) (hd_square : IsRatSquare d)
    (hneg_square : IsRatSquare (-d)) :
    IsRatSquare (-1) := by
  rcases hd_square with ⟨a, ha⟩
  rcases hneg_square with ⟨b, hb⟩
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    apply hd
    rw [← ha, ha_zero]
    ring
  refine ⟨b / a, ?_⟩
  field_simp [ha_ne]
  rw [hb, ha]

theorem false_of_square_and_neg_square
    {d : ℚ} (hd : d ≠ 0) (hd_square : IsRatSquare d)
    (hneg_square : IsRatSquare (-d)) :
    False :=
  rat_neg_one_not_square <|
    rat_neg_one_square_of_square_and_neg_square hd hd_square hneg_square

theorem contradiction_from_two_halved_branch_points
    {e₁ e₂ e₃ : ℚ} (h12 : e₁ ≠ e₂)
    (hhalf₁ : IsRatSquare (e₁ - e₂) ∧ IsRatSquare (e₁ - e₃))
    (hhalf₂ : IsRatSquare (e₂ - e₁) ∧ IsRatSquare (e₂ - e₃)) :
    False := by
  let d : ℚ := e₁ - e₂
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr h12
  have hneg : IsRatSquare (-d) := by
    dsimp [d]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hhalf₂.1
  exact false_of_square_and_neg_square hd hhalf₁.1 hneg

/-- The branch point `(e, 0)` is a double in `shortWQ A B` over `Q`. -/
def BranchPointIsDouble
    (A B e : ℚ) (hns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e 0) :
    Prop :=
  ∃ P : WeierstrassCurve.Affine.Point (shortWQ A B),
    (2 : ℕ) • P = WeierstrassCurve.Affine.Point.some e 0 hns

/--
Classical halving criterion for a branch point, stated as the remaining
geometric seam.

This is Knapp Theorem 4.2 / Silverman's standard criterion, and follows from
the duplication formula.
-/
theorem shortW_halving_criterion
    {A B eᵢ eⱼ eₖ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - eᵢ) * (x - eⱼ) * (x - eₖ))
    (hij : eᵢ ≠ eⱼ) (hik : eᵢ ≠ eₖ) (hjk : eⱼ ≠ eₖ)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) eᵢ 0) :
    BranchPointIsDouble A B eᵢ hns ↔
      IsRatSquare (eᵢ - eⱼ) ∧ IsRatSquare (eᵢ - eₖ) := by
  sorry

/--
The proved obstruction: if two distinct branch points are doubles, then the
halving criterion forces `-1` to be a rational square.
-/
theorem no_two_distinct_branch_points_both_double
    {A B e₁ e₂ e₃ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - e₁) * (x - e₂) * (x - e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {hns₁ : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e₁ 0}
    {hns₂ : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e₂ 0}
    (hd₁ : BranchPointIsDouble A B e₁ hns₁)
    (hd₂ : BranchPointIsDouble A B e₂ hns₂) :
    False := by
  have hhalf₁ :
      IsRatSquare (e₁ - e₂) ∧ IsRatSquare (e₁ - e₃) :=
    (shortW_halving_criterion hfactor h12 h13 h23 hns₁).mp hd₁
  have hfactor₂ : ∀ x : ℚ,
      shortCubicQ A B x = (x - e₂) * (x - e₁) * (x - e₃) := by
    intro x
    rw [hfactor x]
    ring
  have hhalf₂ :
      IsRatSquare (e₂ - e₁) ∧ IsRatSquare (e₂ - e₃) :=
    (shortW_halving_criterion hfactor₂ h12.symm h23 h13 hns₂).mp hd₂
  exact contradiction_from_two_halved_branch_points h12 hhalf₁ hhalf₂

/--
The same obstruction in the "all three branch points are doubles" form used by
full `4`-torsion.  Only two of the three doubled branch points are needed.
-/
theorem no_three_distinct_branch_points_all_double
    {A B e₁ e₂ e₃ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - e₁) * (x - e₂) * (x - e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {hns₁ : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e₁ 0}
    {hns₂ : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e₂ 0}
    {hns₃ : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) e₃ 0}
    (hd₁ : BranchPointIsDouble A B e₁ hns₁)
    (hd₂ : BranchPointIsDouble A B e₂ hns₂)
    (_hd₃ : BranchPointIsDouble A B e₃ hns₃) :
    False :=
  no_two_distinct_branch_points_both_double hfactor h12 h13 h23 hd₁ hd₂

end MazurProof.NoFull4Torsion
