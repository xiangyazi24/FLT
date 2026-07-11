import FLT.Assumptions.MazurProof.CyclicExclusion15

/-!
# The elementary map from the order-15 Tate equations to `C₀`

This file isolates the rational algebra behind the `X₁(15)` computation.  If
`x` is a root of the third division polynomial on the order-five Tate normal
form, set

* `s = b / x - 1`, and
* `v = (2 (s + 1)² x + 3 s²) / s`.

The division-polynomial equation then gives

`v² = 4s³ + 17s² + 4s = s(4s+1)(s+4)`.

We also check, without using a rational-point classification theorem, that all
seven standard affine rational points on this curve are cuspidal: none can be
the image of a nonsingular Tate solution satisfying the curve equation.
The rank-zero/exhaustion statement for `C₀(ℚ)` is deliberately not asserted
here.
-/

namespace MazurProof.RationalPointsN15C0

open CyclicExclusion15

/-! ## The target curve and the explicit rational map -/

/-- The affine equation of the genus-one curve used in the order-15 descent. -/
def C0Equation (s v : ℚ) : Prop :=
  v ^ 2 = 4 * s ^ 3 + 17 * s ^ 2 + 4 * s

/-- The first coordinate of the rational map from the Tate equations. -/
def sCoord (b x : ℚ) : ℚ :=
  b / x - 1

/-- The second coordinate of the rational map, written in terms of `s` and `x`. -/
def vCoord (s x : ℚ) : ℚ :=
  (2 * (s + 1) ^ 2 * x + 3 * s ^ 2) / s

theorem C0Equation_factor (s v : ℚ) :
    C0Equation s v ↔ v ^ 2 = s * (4 * s + 1) * (s + 4) := by
  unfold C0Equation
  constructor <;> intro h
  · rw [h]
    ring
  · rw [h]
    ring

/-- Dividing `ψ₃(b,x)=0` by `x³` gives a quadratic equation in `x`. -/
theorem psi3_normalized {b x : ℚ} (hx : x ≠ 0)
    (hpsi : tateOrder5Psi3 b x = 0) :
    (sCoord b x + 1) ^ 2 * x ^ 2 +
        3 * (sCoord b x) ^ 2 * x - (sCoord b x) ^ 3 = 0 := by
  calc
    (sCoord b x + 1) ^ 2 * x ^ 2 +
          3 * (sCoord b x) ^ 2 * x - (sCoord b x) ^ 3 =
        tateOrder5Psi3 b x / x ^ 3 := by
      unfold sCoord tateOrder5Psi3
      field_simp [hx]
      ring
    _ = 0 := by rw [hpsi]; simp

theorem b_ne_zero_of_nonsingular {b : ℚ}
    (hΔ : TateOrder5NonsingularParameter b) : b ≠ 0 := by
  intro hb
  apply hΔ
  simp [hb]

theorem x_ne_zero_of_psi3 {b x : ℚ}
    (hΔ : TateOrder5NonsingularParameter b)
    (hpsi : tateOrder5Psi3 b x = 0) : x ≠ 0 := by
  have hb := b_ne_zero_of_nonsingular hΔ
  intro hx
  subst x
  have hb3 : b ^ 3 = 0 := by
    simpa [tateOrder5Psi3] using hpsi.symm
  exact (pow_ne_zero 3 hb) hb3

theorem sCoord_ne_zero_of_psi3 {b x : ℚ}
    (hx : x ≠ 0) (hpsi : tateOrder5Psi3 b x = 0) :
    sCoord b x ≠ 0 := by
  intro hs
  have hb_eq_x : b = x := by
    unfold sCoord at hs
    field_simp [hx] at hs
    linarith
  subst b
  have hx5 : x ^ 5 = 0 := by
    rw [show tateOrder5Psi3 x x = x ^ 5 by
      unfold tateOrder5Psi3
      ring] at hpsi
    exact hpsi
  exact (pow_ne_zero 5 hx) hx5

/-- The quadratic identity in `x` implies the equation of `C₀`. -/
theorem normalized_to_C0 {s x : ℚ} (hs : s ≠ 0)
    (hquad : (s + 1) ^ 2 * x ^ 2 + 3 * s ^ 2 * x - s ^ 3 = 0) :
    C0Equation s (vCoord s x) := by
  unfold C0Equation vCoord
  field_simp [hs]
  linear_combination 4 * (s + 1) ^ 2 * hquad

/-- A nonsingular Tate `ψ₃` root maps to a rational point of `C₀`. -/
theorem tate_psi3_root_to_C0 {b x : ℚ}
    (hΔ : TateOrder5NonsingularParameter b)
    (hpsi : tateOrder5Psi3 b x = 0) :
    C0Equation (sCoord b x) (vCoord (sCoord b x) x) := by
  have hx := x_ne_zero_of_psi3 hΔ hpsi
  exact normalized_to_C0 (sCoord_ne_zero_of_psi3 hx hpsi)
    (psi3_normalized hx hpsi)

/-! ## The seven known affine points -/

/-- The five first coordinates occurring among the standard affine points. -/
def KnownSCandidate (s : ℚ) : Prop :=
  s = -4 ∨ s = -1 ∨ s = -(1 / 4) ∨ s = 0 ∨ s = 1

theorem C0_neg_four_zero : C0Equation (-4) 0 := by
  norm_num [C0Equation]

theorem C0_neg_one_pos_three : C0Equation (-1) 3 := by
  norm_num [C0Equation]

theorem C0_neg_one_neg_three : C0Equation (-1) (-3) := by
  norm_num [C0Equation]

theorem C0_neg_quarter_zero : C0Equation (-(1 / 4)) 0 := by
  norm_num [C0Equation]

theorem C0_zero_zero : C0Equation 0 0 := by
  norm_num [C0Equation]

theorem C0_one_pos_five : C0Equation 1 5 := by
  norm_num [C0Equation]

theorem C0_one_neg_five : C0Equation 1 (-5) := by
  norm_num [C0Equation]

/-- For a known first coordinate, the curve equation forces the listed ordinate. -/
theorem ordinate_of_known_s {s v : ℚ}
    (hs : KnownSCandidate s) (hC0 : C0Equation s v) :
    (s = -4 ∧ v = 0) ∨
      (s = -1 ∧ (v = 3 ∨ v = -3)) ∨
      (s = -(1 / 4) ∧ v = 0) ∨
      (s = 0 ∧ v = 0) ∨
      (s = 1 ∧ (v = 5 ∨ v = -5)) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    norm_num [C0Equation] at hC0
    nlinarith
  · right; left
    refine ⟨rfl, ?_⟩
    have hfac : (v - 3) * (v + 3) = 0 := by
      norm_num [C0Equation] at hC0
      nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith
  · right; right; left
    refine ⟨rfl, ?_⟩
    norm_num [C0Equation] at hC0
    nlinarith
  · right; right; right; left
    refine ⟨rfl, ?_⟩
    norm_num [C0Equation] at hC0
    nlinarith
  · right; right; right; right
    refine ⟨rfl, ?_⟩
    have hfac : (v - 5) * (v + 5) = 0 := by
      norm_num [C0Equation] at hC0
      nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith

/-! ## Every known point is cuspidal for the Tate problem -/

private theorem rat_sq_ne_five (r : ℚ) : r ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨r, by simpa [pow_two] using h.symm⟩
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot hsq

theorem b_eq_succ_mul_x {b x s : ℚ} (hx : x ≠ 0)
    (hs : sCoord b x = s) : b = (s + 1) * x := by
  unfold sCoord at hs
  field_simp [hx] at hs
  linarith

private theorem no_tate_solution_at_neg_four {b x y : ℚ}
    (hcurve : TateOrder5CurveEq b x y)
    (hquad : (sCoord b x + 1) ^ 2 * x ^ 2 +
      3 * (sCoord b x) ^ 2 * x - (sCoord b x) ^ 3 = 0)
    (hx : x ≠ 0) (hs : sCoord b x = -4) : False := by
  have hb := b_eq_succ_mul_x hx hs
  have hxval : x = -(8 / 3) := by
    rw [hs] at hquad
    norm_num at hquad
    nlinarith [sq_nonneg (3 * x + 8)]
  have hbval : b = 8 := by rw [hb, hxval]; norm_num
  rw [hbval, hxval] at hcurve
  norm_num [TateOrder5CurveEq] at hcurve
  nlinarith [sq_nonneg (y + 16 / 3)]

private theorem no_tate_solution_at_neg_quarter {b x y : ℚ}
    (hcurve : TateOrder5CurveEq b x y)
    (hquad : (sCoord b x + 1) ^ 2 * x ^ 2 +
      3 * (sCoord b x) ^ 2 * x - (sCoord b x) ^ 3 = 0)
    (hx : x ≠ 0) (hs : sCoord b x = -(1 / 4)) : False := by
  have hb := b_eq_succ_mul_x hx hs
  have hxval : x = -(1 / 6) := by
    rw [hs] at hquad
    norm_num at hquad
    nlinarith [sq_nonneg (6 * x + 1)]
  have hbval : b = -(1 / 8) := by rw [hb, hxval]; norm_num
  rw [hbval, hxval] at hcurve
  norm_num [TateOrder5CurveEq] at hcurve
  nlinarith [sq_nonneg (y - 1 / 32)]

private theorem no_tate_solution_at_one {b x y : ℚ}
    (hcurve : TateOrder5CurveEq b x y)
    (hquad : (sCoord b x + 1) ^ 2 * x ^ 2 +
      3 * (sCoord b x) ^ 2 * x - (sCoord b x) ^ 3 = 0)
    (hx : x ≠ 0) (hs : sCoord b x = 1) : False := by
  have hb := b_eq_succ_mul_x hx hs
  have hfac : (4 * x - 1) * (x + 1) = 0 := by
    rw [hs] at hquad
    norm_num at hquad
    nlinarith
  rcases mul_eq_zero.mp hfac with hxquarter | hxnegone
  · have hxval : x = 1 / 4 := by linarith
    have hbval : b = 1 / 2 := by rw [hb, hxval]; norm_num
    rw [hbval, hxval] at hcurve
    norm_num [TateOrder5CurveEq] at hcurve
    exact rat_sq_ne_five (16 * y - 3) (by nlinarith)
  · have hxval : x = -1 := by linarith
    have hbval : b = -2 := by rw [hb, hxval]; norm_num
    rw [hbval, hxval] at hcurve
    norm_num [TateOrder5CurveEq] at hcurve
    exact rat_sq_ne_five (2 * y - 1) (by nlinarith)

/-- None of the five known `s`-coordinates can come from a nonsingular Tate
solution.  This is the complete cusp check, independent of rational-point
exhaustion on `C₀`. -/
theorem known_s_is_cuspidal {b x y : ℚ}
    (hsol : TateOrder5Psi3RootSolution b x y) :
    ¬ KnownSCandidate (sCoord b x) := by
  rcases hsol with ⟨hΔ, hcurve, hpsi⟩
  have hx := x_ne_zero_of_psi3 hΔ hpsi
  have hs0 := sCoord_ne_zero_of_psi3 hx hpsi
  have hquad := psi3_normalized hx hpsi
  rintro (hs | hs | hs | hs | hs)
  · exact no_tate_solution_at_neg_four hcurve hquad hx hs
  · have hb := b_eq_succ_mul_x hx hs
    have hb0 : b = 0 := by simpa using hb
    exact (b_ne_zero_of_nonsingular hΔ) hb0
  · exact no_tate_solution_at_neg_quarter hcurve hquad hx hs
  · exact hs0 hs
  · exact no_tate_solution_at_one hcurve hquad hx hs

end MazurProof.RationalPointsN15C0
