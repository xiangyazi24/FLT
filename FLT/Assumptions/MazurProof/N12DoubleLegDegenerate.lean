import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-!
# Non-circular double-leg reduction for the N=12 degenerate covers

This file keeps the double-leg obstruction separate from the E1 finite-point
route.  The only arithmetic input is the independent rational Eisenstein
quartic classification `RatQuarticEisensteinDegenerate`.
-/

namespace MazurProof.RationalPointsN12

private theorem doubleLeg_u_sq_sub_y_sq {x y h u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hu : u = h + x) :
    u ^ 2 - y ^ 2 = 2 * u * x := by
  rw [hu]
  nlinarith [hh]

private theorem doubleLeg_quartic_num {x y h k u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2)
    (hu : u = h + x) :
    (k * u) ^ 2 = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
  have hrel : u ^ 2 - y ^ 2 = 2 * u * x :=
    doubleLeg_u_sq_sub_y_sq hh hu
  calc
    (k * u) ^ 2 = k ^ 2 * u ^ 2 := by ring
    _ = ((2 * x) ^ 2 + y ^ 2) * u ^ 2 := by rw [hk]
    _ = (2 * u * x) ^ 2 + u ^ 2 * y ^ 2 := by ring
    _ = (u ^ 2 - y ^ 2) ^ 2 + u ^ 2 * y ^ 2 := by rw [← hrel]
    _ = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by ring

private theorem doubleLeg_ratQuarticEisenstein_point {x y h k u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2)
    (hu : u = h + x)
    (hy : y ≠ 0) :
    RatQuarticEisensteinLocal (u / y) (k * u / y ^ 2) := by
  unfold RatQuarticEisensteinLocal
  have hnum : (k * u) ^ 2 = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 :=
    doubleLeg_quartic_num hh hk hu
  have hy2_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hy4_ne : y ^ 4 ≠ 0 := pow_ne_zero 4 hy
  have hleft : ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := by
    field_simp [hy, hy2_ne, hy4_ne]
  have hright :
      ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 =
        u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
    field_simp [hy, hy2_ne, hy4_ne]
  have hmul :
      ((k * u / y ^ 2) ^ 2) * y ^ 4 =
        ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 := by
    calc
      ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := hleft
      _ = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := hnum
      _ = ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 := hright.symm
  exact mul_right_cancel₀ hy4_ne hmul

/-- The independent rational Eisenstein quartic classification proves the
double-leg cover residual. -/
theorem doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate
    (hRat : RatQuarticEisensteinDegenerate) :
    DoubleLegCoverDegenerate := by
  intro x y h k hh hk
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  let u : ℚ := h + x
  have hu : u = h + x := rfl
  by_cases hu0 : u = 0
  · have hh_neg : h = -x := by
      calc
        h = u - x := by rw [hu]; ring
        _ = -x := by rw [hu0]; ring
    have hhx2 : h ^ 2 = x ^ 2 := by
      rw [hh_neg]
      ring
    have hy_sq : y ^ 2 = 0 := by
      nlinarith [hh, hhx2]
    exact Or.inr (sq_eq_zero_iff.mp hy_sq)
  · have hC : RatQuarticEisensteinLocal (u / y) (k * u / y ^ 2) :=
      doubleLeg_ratQuarticEisenstein_point hh hk hu hy
    rcases hRat hC with hr_zero | hr_sq
    · have hu_eq : u = (u / y) * y :=
        (div_mul_cancel₀ u hy).symm
      have hu_zero : u = 0 := by
        calc
          u = (u / y) * y := hu_eq
          _ = 0 := by rw [hr_zero]; ring
      exact False.elim (hu0 hu_zero)
    · have hu2_eq_y2 : u ^ 2 = y ^ 2 := by
        calc
          u ^ 2 = (u / y) ^ 2 * y ^ 2 := by
            symm
            rw [div_pow]
            exact div_mul_cancel₀ (u ^ 2) (pow_ne_zero 2 hy)
          _ = 1 * y ^ 2 := by rw [hr_sq]
          _ = y ^ 2 := by ring
      have hrel : u ^ 2 - y ^ 2 = 2 * u * x :=
        doubleLeg_u_sq_sub_y_sq hh hu
      have hprod : (2 * u) * x = 0 := by
        nlinarith [hrel, hu2_eq_y2]
      have h2u_ne : (2 * u : ℚ) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hu0
      rcases mul_eq_zero.mp hprod with h2u | hx0
      · exact False.elim (h2u_ne h2u)
      · exact Or.inl hx0

/-- Conditional no-solution wrapper for the `(1,1,1)` degenerate cover using
only the independent Eisenstein quartic residual. -/
theorem coverQ_1_1_1_no_nonzero_of_ratQuarticEisensteinDegenerate
    (hRat : RatQuarticEisensteinDegenerate)
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    False :=
  coverQ_1_1_1_no_nonzero_of_doubleLeg
    (doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate hRat)
    hA hB hC hT h

/-- Conditional no-solution wrapper for the `(-3,-1,3)` degenerate cover using
only the independent Eisenstein quartic residual. -/
theorem coverQ_neg3_neg1_3_no_nonzero_of_ratQuarticEisensteinDegenerate
    (hRat : RatQuarticEisensteinDegenerate)
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ (-3) (-1) 3 A B C T) :
    False :=
  coverQ_neg3_neg1_3_no_nonzero_of_doubleLeg
    (doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate hRat)
    hA hB hC hT h

end MazurProof.RationalPointsN12
