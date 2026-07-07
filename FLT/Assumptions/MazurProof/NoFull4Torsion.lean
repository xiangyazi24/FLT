import Mathlib
import FLT.Assumptions.MazurProof.RealTopologyS3
import FLT.Assumptions.MazurProof.RealTorsionBound
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# No full 4-torsion: the elementary halving obstruction

This file isolates the elementary part of the standard proof that full
`(Z / 4Z)^2` rational torsion is impossible over `Q`.

The geometric input is the classical halving criterion: for
`y^2 = (x - e₁)(x - e₂)(x - e₃)`, the branch point `(eᵢ, 0)` is a double over
`Q` iff both differences `eᵢ - eⱼ` and `eᵢ - eₖ` are rational squares.  It is
proved directly below from Mathlib's affine group law formulas.

After that criterion, two distinct branch points being doubles force both `d`
and `-d` to be rational squares, hence force `-1` to be a rational square.
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

private theorem point_some_ext
    {W : WeierstrassCurve ℚ} {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular W x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular W x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
  subst x₂
  subst y₂
  rfl

private theorem shortCubicQ_factor_coeffs
    {A B eᵢ eⱼ eₖ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - eᵢ) * (x - eⱼ) * (x - eₖ)) :
    A = -(eᵢ + eⱼ + eₖ) ∧
      B = eᵢ * eⱼ + eᵢ * eₖ + eⱼ * eₖ ∧
        eᵢ * eⱼ * eₖ = 0 := by
  have h0raw := hfactor 0
  have h1 := hfactor 1
  have hm1 := hfactor (-1)
  simp only [shortCubicQ] at h0raw h1 hm1
  ring_nf at h0raw h1 hm1
  have h0 : eᵢ * eⱼ * eₖ = 0 := by nlinarith
  exact And.intro (by nlinarith : A = -(eᵢ + eⱼ + eₖ))
    (And.intro (by nlinarith : B = eᵢ * eⱼ + eᵢ * eₖ + eⱼ * eₖ) h0)

private theorem square_conditions_of_halving
    {A B eᵢ eⱼ eₖ x y : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - eᵢ) * (x - eⱼ) * (x - eₖ))
    (hjk : eⱼ ≠ eₖ)
    {hns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) eᵢ 0}
    {hPns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) x y}
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPns =
        WeierstrassCurve.Affine.Point.some eᵢ 0 hns) :
    IsRatSquare (eᵢ - eⱼ) ∧ IsRatSquare (eᵢ - eₖ) := by
  let W := shortWQ A B
  let ell := WeierstrassCurve.Affine.slope W x x y y
  have hcoeff := shortCubicQ_factor_coeffs hfactor
  have hA : A = -(eᵢ + eⱼ + eₖ) := hcoeff.1
  have hnotVertical : ¬(x = x ∧ y = WeierstrassCurve.Affine.negY W x y) := by
    intro hv
    have hadd0 :
        WeierstrassCurve.Affine.Point.some x y hPns +
          WeierstrassCurve.Affine.Point.some x y hPns = 0 := by
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq (W := W) hv.1 hv.2
    have htwo :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPns =
          WeierstrassCurve.Affine.Point.some x y hPns +
            WeierstrassCurve.Affine.Point.some x y hPns := by
      simp [two_nsmul]
    have hzero :
        (0 : WeierstrassCurve.Affine.Point W) =
          WeierstrassCurve.Affine.Point.some eᵢ 0 hns := by
      rw [← hdouble, htwo, hadd0]
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns hzero.symm
  have hadd :
      WeierstrassCurve.Affine.Point.some x y hPns +
        WeierstrassCurve.Affine.Point.some x y hPns =
      WeierstrassCurve.Affine.Point.some
        (WeierstrassCurve.Affine.addX W x x ell)
        (WeierstrassCurve.Affine.addY W x x y ell)
        (WeierstrassCurve.Affine.nonsingular_add hPns hPns hnotVertical) := by
    simpa [W, ell] using
      WeierstrassCurve.Affine.Point.add_some (W := W) (h₁ := hPns) (h₂ := hPns)
        hnotVertical
  have htwo :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPns =
        WeierstrassCurve.Affine.Point.some x y hPns +
          WeierstrassCurve.Affine.Point.some x y hPns := by
    simp [two_nsmul]
  have hsum :
      WeierstrassCurve.Affine.Point.some
        (WeierstrassCurve.Affine.addX W x x ell)
        (WeierstrassCurve.Affine.addY W x x y ell)
        (WeierstrassCurve.Affine.nonsingular_add hPns hPns hnotVertical) =
        WeierstrassCurve.Affine.Point.some eᵢ 0 hns := by
    rw [← hadd, ← htwo]
    exact hdouble
  have hxadd :
      WeierstrassCurve.Affine.addX W x x ell = eᵢ := by
    exact (WeierstrassCurve.Affine.Point.some.inj hsum).1
  have hyadd :
      WeierstrassCurve.Affine.addY W x x y ell = 0 := by
    exact (WeierstrassCurve.Affine.Point.some.inj hsum).2
  have hy_ne_neg : y ≠ WeierstrassCurve.Affine.negY W x y := by
    intro hy
    exact hnotVertical ⟨rfl, hy⟩
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    apply hy_ne_neg
    simp [W, shortWQ, WeierstrassCurve.Affine.negY, hy0]
  have hx_ne_ei : x ≠ eᵢ := by
    intro hxe
    have hcurve : y ^ 2 = (x - eᵢ) * (x - eⱼ) * (x - eₖ) := by
      have hcurve0 : y ^ 2 = shortCubicQ A B x := shortWQ_equation_iff.mp hPns.1
      rw [hcurve0, hfactor x]
    rw [hxe] at hcurve
    have : y ^ 2 = 0 := by simpa using hcurve
    exact hy_ne_zero (sq_eq_zero_iff.mp this)
  have hell_sq :
      ell ^ 2 = 2 * (x - eᵢ) + (eᵢ - eⱼ) + (eᵢ - eₖ) := by
    have hxadd' := hxadd
    simp [W, shortWQ, WeierstrassCurve.Affine.addX] at hxadd'
    nlinarith
  have hyline : y = ell * (x - eᵢ) := by
    have hyadd' :
        -(ell * (WeierstrassCurve.Affine.addX W x x ell - x) + y) = 0 := by
      simpa only [W, shortWQ, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        zero_mul, sub_zero] using hyadd
    rw [hxadd] at hyadd'
    nlinarith
  have hcurve_factor : y ^ 2 = (x - eᵢ) * (x - eⱼ) * (x - eₖ) := by
    have hcurve0 : y ^ 2 = shortCubicQ A B x := shortWQ_equation_iff.mp hPns.1
    rw [hcurve0, hfactor x]
  have hdiv :
      ell ^ 2 * (x - eᵢ) = (x - eⱼ) * (x - eₖ) := by
    have hxsub_ne : x - eᵢ ≠ 0 := sub_ne_zero.mpr hx_ne_ei
    have hcurve_line :
        (ell * (x - eᵢ)) ^ 2 = (x - eᵢ) * (x - eⱼ) * (x - eₖ) := by
      simpa [hyline] using hcurve_factor
    have hcancel :
        (x - eᵢ) * (ell ^ 2 * (x - eᵢ)) =
          (x - eᵢ) * ((x - eⱼ) * (x - eₖ)) := by
      calc
        (x - eᵢ) * (ell ^ 2 * (x - eᵢ)) = (ell * (x - eᵢ)) ^ 2 := by ring
        _ = (x - eᵢ) * (x - eⱼ) * (x - eₖ) := hcurve_line
        _ = (x - eᵢ) * ((x - eⱼ) * (x - eₖ)) := by ring
    exact mul_left_cancel₀ hxsub_ne hcancel
  let u := x - eᵢ
  let a := eᵢ - eⱼ
  let b := eᵢ - eₖ
  have hu_sq : u ^ 2 = a * b := by
    have hdiv' : ell ^ 2 * u = (u + a) * (u + b) := by
      dsimp [u, a, b]
      convert hdiv using 1
      ring
    have hell' : ell ^ 2 = 2 * u + a + b := by
      simpa [u, a, b] using hell_sq
    rw [hell'] at hdiv'
    ring_nf at hdiv'
    nlinarith
  have hell_ne_zero : ell ≠ 0 := by
    intro hell0
    have hsum : 2 * u + a + b = 0 := by
      have hsum0 : (0 : ℚ) = 2 * u + a + b := by
        simpa [hell0, u, a, b] using hell_sq
      exact hsum0.symm
    have hdiff : a = b := by
      have hsum_ab : a + b = -2 * u := by linarith
      have hdiff_sq : (a - b) ^ 2 = 0 := by
        calc
          (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
          _ = (-2 * u) ^ 2 - 4 * (a * b) := by rw [hsum_ab]
          _ = 0 := by rw [← hu_sq]; ring
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hdiff_sq)
    exact hjk (by dsimp [a, b] at hdiff; linarith)
  constructor
  · refine ⟨(ell ^ 2 + a - b) / (2 * ell), ?_⟩
    field_simp [hell_ne_zero]
    rw [hell_sq]
    dsimp [u, a, b] at hu_sq ⊢
    nlinarith
  · refine ⟨(ell ^ 2 - a + b) / (2 * ell), ?_⟩
    field_simp [hell_ne_zero]
    rw [hell_sq]
    dsimp [u, a, b] at hu_sq ⊢
    nlinarith

private theorem double_of_square_conditions
    {A B eᵢ eⱼ eₖ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - eᵢ) * (x - eⱼ) * (x - eₖ))
    (hij : eᵢ ≠ eⱼ) (hik : eᵢ ≠ eₖ) (hjk : eⱼ ≠ eₖ)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) eᵢ 0)
    (hsq : IsRatSquare (eᵢ - eⱼ) ∧ IsRatSquare (eᵢ - eₖ)) :
    BranchPointIsDouble A B eᵢ hns := by
  rcases hsq with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  let W := shortWQ A B
  let x : ℚ := eᵢ + r * s
  let y : ℚ := r * s * (r + s)
  let ell : ℚ := r + s
  have hcoeff := shortCubicQ_factor_coeffs hfactor
  have hA : A = -(eᵢ + eⱼ + eₖ) := hcoeff.1
  have hB : B = eᵢ * eⱼ + eᵢ * eₖ + eⱼ * eₖ := hcoeff.2.1
  have hej : eⱼ = eᵢ - r ^ 2 := by nlinarith
  have hek : eₖ = eᵢ - s ^ 2 := by nlinarith
  have hr_ne : r ≠ 0 := by
    intro hr0
    apply hij
    have : eᵢ - eⱼ = 0 := by rw [← hr, hr0]; ring
    exact sub_eq_zero.mp this
  have hs_ne : s ≠ 0 := by
    intro hs0
    apply hik
    have : eᵢ - eₖ = 0 := by rw [← hs, hs0]; ring
    exact sub_eq_zero.mp this
  have hell_ne : ell ≠ 0 := by
    intro hell0
    apply hjk
    have hsum : r + s = 0 := by simpa [ell] using hell0
    have hs_eq : s = -r := by linarith
    have hrsq : r ^ 2 = s ^ 2 := by rw [hs_eq]; ring
    have : eⱼ = eₖ := by nlinarith
    exact this
  have hell_sum_ne : r + s ≠ 0 := by
    simpa [ell] using hell_ne
  have hy_ne : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (mul_ne_zero hr_ne hs_ne) hell_sum_ne
  have hcurve : y ^ 2 = shortCubicQ A B x := by
    rw [hfactor x]
    dsimp [x, y]
    rw [hej, hek]
    ring
  have hPns : WeierstrassCurve.Affine.Nonsingular W x y := by
    refine ⟨?_, ?_⟩
    · exact shortWQ_equation_iff.mpr hcurve
    · right
      have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero (by norm_num) hy_ne
      simpa [W, shortWQ, WeierstrassCurve.Affine.evalEval_polynomialY] using h2y
  refine ⟨WeierstrassCurve.Affine.Point.some x y hPns, ?_⟩
  have hy_ne_neg : y ≠ WeierstrassCurve.Affine.negY W x y := by
    intro hyneg
    apply hy_ne
    dsimp [W] at hyneg
    simp [shortWQ] at hyneg
    linarith
  have hnotVertical : ¬(x = x ∧ y = WeierstrassCurve.Affine.negY W x y) := by
    exact fun h => hy_ne_neg h.2
  have hslope : WeierstrassCurve.Affine.slope W x x y y = ell := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne (W := W) (x₁ := x) (x₂ := x)
      (y₁ := y) (y₂ := y) rfl hy_ne_neg]
    dsimp [W, x, y, ell]
    simp [shortWQ]
    rw [hA, hB, hej, hek]
    field_simp [hr_ne, hs_ne, hell_sum_ne]
    ring
  have hxadd : WeierstrassCurve.Affine.addX W x x
      (WeierstrassCurve.Affine.slope W x x y y) = eᵢ := by
    rw [hslope]
    dsimp [W, x, ell]
    simp [shortWQ]
    rw [hA, hej, hek]
    ring
  have hyadd : WeierstrassCurve.Affine.addY W x x y
      (WeierstrassCurve.Affine.slope W x x y y) = 0 := by
    rw [hslope]
    have hxadd' : WeierstrassCurve.Affine.addX W x x ell = eᵢ := by
      simpa [hslope] using hxadd
    dsimp [W, x, y, ell]
    simp [shortWQ, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    rw [hA, hej, hek]
    ring
  have hadd :=
    WeierstrassCurve.Affine.Point.add_some (W := W) (h₁ := hPns) (h₂ := hPns)
      hnotVertical
  calc
    (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hPns =
        WeierstrassCurve.Affine.Point.some x y hPns +
          WeierstrassCurve.Affine.Point.some x y hPns := by simp [two_nsmul]
    _ = WeierstrassCurve.Affine.Point.some eᵢ 0 hns := by
      rw [hadd]
      exact point_some_ext hxadd hyadd

/--
Classical halving criterion for a branch point.

This is Knapp Theorem 4.2 / Silverman's standard criterion, proved here from
the explicit affine addition formulas.
-/
theorem shortW_halving_criterion
    {A B eᵢ eⱼ eₖ : ℚ}
    (hfactor : ∀ x : ℚ,
      shortCubicQ A B x = (x - eᵢ) * (x - eⱼ) * (x - eₖ))
    (hij : eᵢ ≠ eⱼ) (hik : eᵢ ≠ eₖ) (hjk : eⱼ ≠ eₖ)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortWQ A B) eᵢ 0) :
    BranchPointIsDouble A B eᵢ hns ↔
      IsRatSquare (eᵢ - eⱼ) ∧ IsRatSquare (eᵢ - eₖ) := by
  constructor
  · rintro ⟨P, hdouble⟩
    cases P with
    | zero =>
        exfalso
        have hzero :
            (0 : WeierstrassCurve.Affine.Point (shortWQ A B)) =
              WeierstrassCurve.Affine.Point.some eᵢ 0 hns := by
          rw [← hdouble]
          exact (nsmul_zero (2 : ℕ)).symm
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns hzero.symm
    | some x y hPns =>
        exact square_conditions_of_halving hfactor hjk hdouble
  · exact double_of_square_conditions hfactor hij hik hjk hns

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
