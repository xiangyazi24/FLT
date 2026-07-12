import FLT.Assumptions.MazurProof.N18RouteC_GlobalCubes

/-!
# Global dual Kummer candidates for actual points

The translated curve equation supplies the valuation support needed by the
global `S`-unit normal form.  This is the semantic bridge from an arbitrary
point of `E₀(L)` to one of the 81 executable dual candidates.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.DualGlobal

open Isogeny KummerGeometry ValuationSupport GlobalCubes

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

theorem kappa_order_supported (P : E0Point)
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    (hq2 : q ≠ TwoAdic.p2) (hq3 : q ≠ ThreeAdic.p3) :
    (3 : ℤ) ∣ ordAt q (kappa P) := by
  have hTwo : ordAt q (2 : L) = 0 := ordAt_two_of_ne_p2 q hq2
  have hThree : ordAt q (3 : L) = 0 := ordAt_three_of_ne_p3 q hq3
  cases P with
  | zero => simp [kappa]
  | some x y h =>
      by_cases hT : x = 1 ∧ y = 0
      · rw [show kappa (.some x y h) = (1 / 2 : L) by simp [kappa, hT]]
        have hdiv := ordAt_div q (one_ne_zero : (1 : L) ≠ 0)
          (by norm_num : (2 : L) ≠ 0)
        rw [hdiv, ordAt_one, hTwo]
        simp
      · rw [kappa_some_of_ne_T h hT]
        have hw : tateW x y ≠ 0 := by
          simpa [kappa_some_of_ne_T h hT] using kappa_ne_zero (.some x y h)
        have hcurve := translated_curve_equation h
        by_cases hu : tateU x = 0
        · have hwplus : tateW x y + 2 = 0 := by
            have hprod : tateW x y * (tateW x y + 2) = 0 := by
              simpa [hu] using hcurve
            exact (mul_eq_zero.mp hprod).resolve_left hw
          have hwEq : tateW x y = -2 := by linear_combination hwplus
          rw [hwEq, ordAt_neg, hTwo]
          simp
        · exact tateW_order_mod_three q hu hw hcurve hTwo hThree

theorem kappa_global_normal_form (P : E0Point) :
    ∃ i j k l : Fin 3, ∃ c : L,
      kappa P = a ^ i.val * (a + 1) ^ j.val *
        (2 : L) ^ k.val * pi ^ l.val * c ^ 3 := by
  apply s_unit_normal_form (kappa_ne_zero P)
  intro q hq2 hq3
  exact kappa_order_supported P q hq2 hq3

end

end MazurProof.N18RouteC.DualGlobal
