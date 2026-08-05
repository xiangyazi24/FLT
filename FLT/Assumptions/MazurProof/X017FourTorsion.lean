import FLT.Assumptions.MazurProof.X017RankZero

/-!
# Four-torsion on the standard X₀(17) model

Once a separate arithmetic argument proves that every rational point is
killed by four, the remaining point classification is elementary.  A point
killed by two is either infinity or `(0,0)`.  If instead its double is
`(0,0)`, the duplication formula forces `x² = 289`; the curve equation then
leaves exactly `(17,136)` and `(17,-136)`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FourTorsion

open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.X017TwoTorsion

noncomputable section

/-- On a standard two-isogeny curve, the horizontal coordinate of a doubled
affine point is `(x²-b)²/(4y²)`. -/
private theorem tangent_x_eq_square_div
    {a b x y : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    StandardTwoIsogeny.tx a x
        (StandardTwoIsogeny.tangent a b x y) =
      (x ^ 2 - b) ^ 2 / (4 * y ^ 2) := by
  unfold StandardTwoIsogeny.tx StandardTwoIsogeny.tangent
  field_simp [hy]
  rw [hcurve]
  ring

/-- A rational point whose double is the visible kernel point has horizontal
coordinate `17`. -/
theorem x_eq_seventeen_of_two_nsmul_eq_K
    {x y : ℚ} (h : Nonsingular standard x y)
    (hdouble :
      2 • (Point.some x y h : Point standard) = K) :
    x = 17 := by
  have hy : y ≠ 0 := by
    intro hy
    have hzero :
        2 • (Point.some x y h : Point standard) = 0 :=
      StandardTwoIsogeny.double_eq_zero_of_y_zero h hy
    apply K_ne_zero
    calc
      K = 2 • (Point.some x y h : Point standard) := hdouble.symm
      _ = 0 := hzero
  have hx : x ≠ 0 := by
    intro hx
    have hy0 := StandardTwoIsogeny.y_zero_of_x_zero h hx
    exact hy hy0
  have hcurve :
      y ^ 2 = x * (x ^ 2 + a17 * x + b17) :=
    StandardTwoIsogeny.curve_equation.mp h.left
  have hfx : StandardTwoIsogeny.fx x y ≠ 0 := by
    unfold StandardTwoIsogeny.fx
    exact div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
  have hcomp :=
    StandardTwoIsogeny.dual_comp_pointMap
      (Point.some x y h : Point standard)
  rw [hdouble, StandardTwoIsogeny.pointMap_some h hx,
    StandardTwoIsogeny.dualPoint_some _ hfx] at hcomp
  have hxcoord :
      StandardTwoIsogeny.dx
          (StandardTwoIsogeny.fx x y)
          (StandardTwoIsogeny.fy b17 x y) = 0 := by
    unfold K StandardTwoIsogeny.kernelPoint at hcomp
    rw [Point.some.injEq] at hcomp
    exact hcomp.1
  rw [StandardTwoIsogeny.dual_forward_x hx hy hcurve] at hxcoord
  rw [tangent_x_eq_square_div hy hcurve] at hxcoord
  have hsq : (x ^ 2 - b17) ^ 2 = 0 := by
    field_simp [hy] at hxcoord
    simpa using hxcoord
  have hxb : x ^ 2 = b17 := by
    nlinarith [sq_nonneg (x ^ 2 - b17)]
  have hxcases : x = 17 ∨ x = -17 := by
    apply eq_or_eq_neg_of_sq_eq_sq x 17
    norm_num [b17, veluT] at hxb ⊢
    exact hxb
  rcases hxcases with hx | hx
  · exact hx
  · exfalso
    rw [hx] at hcurve
    norm_num [a17, b17, veluT] at hcurve
    nlinarith [sq_nonneg y]

/-- The two rational halves of `(0,0)` are precisely `T` and `-T`. -/
theorem eq_T_or_neg_T_of_two_nsmul_eq_K
    (P : Point standard) (hdouble : 2 • P = K) :
    P = T ∨ P = -T := by
  cases P with
  | zero =>
      exfalso
      simpa using K_ne_zero hdouble.symm
  | some x y h =>
      have hx : x = 17 :=
        x_eq_seventeen_of_two_nsmul_eq_K h hdouble
      have hcurve :
          y ^ 2 = x * (x ^ 2 + a17 * x + b17) :=
        StandardTwoIsogeny.curve_equation.mp h.left
      rw [hx] at hcurve
      have hycases : y = 136 ∨ y = -136 := by
        apply eq_or_eq_neg_of_sq_eq_sq y 136
        norm_num [a17, b17, veluT] at hcurve ⊢
        exact hcurve
      rcases hycases with hy | hy
      · left
        unfold T
        rw [Point.some.injEq]
        exact ⟨hx, hy⟩
      · right
        unfold T
        rw [Point.neg_some, Point.some.injEq]
        exact ⟨hx, by
          rw [StandardTwoIsogeny.curve_negY]
          exact hy⟩

/-- Every rational point killed by four is one of the four visible points. -/
theorem eq_zero_or_K_or_T_or_neg_T_of_four_nsmul_eq_zero
    (P : Point standard) (hfour : 4 • P = 0) :
    P = 0 ∨ P = K ∨ P = T ∨ P = -T := by
  have htwo : 2 • (2 • P) = 0 := by
    simpa [← mul_nsmul] using hfour
  let Q : MazurProof.RationalPointsN15ExactSequence.TwoTorsion
      (Point standard) :=
    ⟨2 • P, htwo⟩
  rcases twoTorsion_value_eq_zero_or_K Q with hQ | hQ
  · have hPtwo : 2 • P = 0 := hQ
    let R : MazurProof.RationalPointsN15ExactSequence.TwoTorsion
        (Point standard) :=
      ⟨P, hPtwo⟩
    rcases twoTorsion_value_eq_zero_or_K R with hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inl hP)
  · rcases eq_T_or_neg_T_of_two_nsmul_eq_K P hQ with hP | hP
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr hP))

end

end MazurProof.X017FourTorsion
