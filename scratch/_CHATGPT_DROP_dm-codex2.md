```lean
namespace MazurProof.RationalPointsN12

/-- With `u = h + x`, the first right-triangle equation gives
`u^2 - y^2 = 2*u*x`.  The hypothesis orientation is chosen to avoid
`subst u`. -/
theorem doubleLeg_u_sq_sub_y_sq {x y h u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hu : u = h + x) :
    u ^ 2 - y ^ 2 = 2 * u * x := by
  rw [hu]
  nlinarith [hh]

/-- Numerator identity for the C12 point constructed from two right triangles. -/
theorem doubleLeg_quartic_num {x y h k u : ℚ}
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

/-- The nonzero-`y` branch of the double-leg construction gives a rational point
on `C12`: `r = u/y`, `s = k*u/y^2`. -/
theorem doubleLeg_ratQuarticEisenstein_point {x y h k u : ℚ}
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2)
    (hu : u = h + x)
    (hy : y ≠ 0) :
    RatQuarticEisenstein (u / y) (k * u / y ^ 2) := by
  unfold RatQuarticEisenstein
  have hnum : (k * u) ^ 2 = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 :=
    doubleLeg_quartic_num hh hk hu
  have hy2_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hy4_ne : y ^ 4 ≠ 0 := pow_ne_zero 4 hy
  have hleft : ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := by
    field_simp [hy, hy2_ne, hy4_ne]
    ring
  have hright :
      ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 =
        u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := by
    field_simp [hy, hy2_ne, hy4_ne]
    ring
  apply (mul_right_inj' hy4_ne).mp
  calc
    ((k * u / y ^ 2) ^ 2) * y ^ 4 = (k * u) ^ 2 := hleft
    _ = u ^ 4 - u ^ 2 * y ^ 2 + y ^ 4 := hnum
    _ = ((u / y) ^ 4 - (u / y) ^ 2 + 1) * y ^ 4 := hright.symm

/-- The C12 `x`-coordinate classification rules out a nondegenerate pair of
right triangles sharing the leg `y` and with other legs `x` and `2*x`. -/
theorem doubleLeg_of_ratQuarticEisenstein
    (HE : RatQuarticEisensteinXClassification) :
    DoubleLegRightTrianglesDegenerate := by
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
    have hy_sq : y ^ 2 = 0 := by
      nlinarith [hh, hh_neg]
    exact Or.inr (sq_eq_zero_iff.mp hy_sq)
  · have hC : RatQuarticEisenstein (u / y) (k * u / y ^ 2) :=
      doubleLeg_ratQuarticEisenstein_point hh hk hu hy
    rcases HE hC with hr_zero | hr_sq
    · have hu_eq : u = (u / y) * y :=
        (div_mul_cancel₀ u hy).symm
      have hu_zero : u = 0 := by
        calc
          u = (u / y) * y := hu_eq
          _ = 0 := by rw [hr_zero]; ring
      exact False.elim (hu0 hu_zero)
    · have hu_eq : u = (u / y) * y :=
        (div_mul_cancel₀ u hy).symm
      have hu2_eq_y2 : u ^ 2 = y ^ 2 := by
        calc
          u ^ 2 = ((u / y) * y) ^ 2 := by rw [hu_eq]
          _ = (u / y) ^ 2 * y ^ 2 := by ring
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

end MazurProof.RationalPointsN12
```