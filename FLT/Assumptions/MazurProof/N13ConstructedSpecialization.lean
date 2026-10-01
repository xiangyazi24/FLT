import FLT.Assumptions.MazurProof.N13CalibratedChooser
import FLT.Assumptions.MazurProof.N13SpecialDegreeFourCode
import FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient
import FLT.Assumptions.MazurProof.N13TwoChartTensorCompatibility

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The recentered code of the CONSTRUCTED calibrated chooser is an additive
map to ZMod19 and agrees with proper point reduction. This uses the actual
two-chart comparisons and the proved degree-four bridge. It does not use
the previously flagged exactSpreadLine or bad-characteristic sextic route.
-/

namespace MazurProof.N13ConstructedSpecialization

noncomputable section
open N13SpecialDivisorCharts N13SpecialAbelCode N13CoherentChartComparison
open N13SpecialDegreeFourCode

abbrev G := N13RationalPointEndgame.G

def tensor_comparison_right
    (L M U : N13TwoChartSpecialRestriction.ChartPair) (h : SpecialComparison L M) :
    SpecialComparison (tensor L U) (tensor M U) where
  aNum := h.aNum
  aDen := h.aDen
  iNum := h.iNum
  iDen := h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := by
    change Ideal.span ({h.aNum} : Set As) * (L.affineIdeal * U.affineIdeal) =
      Ideal.span ({h.aDen} : Set As) * (M.affineIdeal * U.affineIdeal)
    rw [← mul_assoc, h.affine_eq, mul_assoc]
  infinity_eq := by
    change Ideal.span ({h.iNum} : Set Bs) * (L.infinityIdeal * U.infinityIdeal) =
      Ideal.span ({h.iDen} : Set Bs) * (M.infinityIdeal * U.infinityIdeal)
    rw [← mul_assoc, h.infinity_eq, mul_assoc]
  overlap_eq := h.overlap_eq

theorem divisorCode_eq_of_comparison (D E : EffectiveDivisorTwo)
    (h : SpecialComparison (ofDivisor D) (ofDivisor E)) : divisorCode D = divisorCode E := by
  have he := degreeFourCode_eq_of_comparison D D E D
    (tensor_comparison_right _ _ (ofDivisor D) h)
  exact add_right_cancel he

def chosenDivisor (P : G) : EffectiveDivisorTwo := (N13CalibratedChooser.choose P).specialDivisor

theorem chosen_code_balance (P Q : G) :
    divisorCode (chosenDivisor P) + divisorCode (chosenDivisor Q) =
      divisorCode (chosenDivisor (P + Q)) + divisorCode (chosenDivisor 0) := by
  obtain ⟨h⟩ := N13CalibratedChooser.chooser_tensor_comparisons P Q
  have hred := h.reduce
  rw [N13.TwoChartTensorCompatibility.restrict_tensor_data,
    N13.TwoChartTensorCompatibility.restrict_tensor_data] at hred
  exact degreeFourCode_eq_of_comparison _ _ _ _ hred

def specialCode (P : G) : ZMod 19 := divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0)

@[simp] theorem specialCode_zero : specialCode 0 = 0 := by simp [specialCode]

theorem specialCode_add (P Q : G) : specialCode (P + Q) = specialCode P + specialCode Q := by
  have h := chosen_code_balance P Q
  unfold specialCode
  linear_combination -h

/-- The additive specialization code, built without an additivity input. -/
def specialization : G →+ ZMod 19 where
  toFun := specialCode
  map_zero' := specialCode_zero
  map_add' := specialCode_add

theorem chosen_point_specialClass (P : N13RationalPointEndgame.RationalCurvePoint) :
    (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      N13RationalPointEndgame.specialPointClass (N13ProperCurveReduction.reduceCurve P) := by
  obtain ⟨h⟩ := N13CalibratedChooser.chooser.point_compatible P
  have hred := h.reduce
  rw [N13.TwoChartTensorCompatibility.restrict_data,
    N13.TwoChartTensorCompatibility.restrict_data] at hred
  have he := divisorCode_eq_of_comparison _ _ hred
  have hs : (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      (N13RationalCurvePointPicardRealization.data P).realization.toSpecialPic := by
    apply picCode_injective
    exact he
  exact hs.trans (N13RationalCurvePointPicardRealization.data P).special_eq

theorem chosen_zero_specialClass : (N13CalibratedChooser.choose 0).toSpecialPic =
    N13RationalPointEndgame.specialPointClass N13RationalPointEndgame.specialAnchor := by
  rw [N13CalibratedChooser.choose_zero, N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]

/-- Pointwise compatibility with the actual proper reduction, recentered at
the same positive infinity anchor used by the rational Abel map. -/
theorem specialization_rationalAbel (P : N13RationalPointEndgame.RationalCurvePoint) :
    specialization (N13RationalPointEndgame.rationalAbel P) =
      pointCode (N13ProperCurveReduction.reduceCurve P) - pointCode N13RationalPointEndgame.specialAnchor := by
  change divisorCode (chosenDivisor (N13RationalPointEndgame.rationalAbel P)) -
      divisorCode (chosenDivisor 0) = _
  change picCode (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic -
      picCode (N13CalibratedChooser.choose 0).toSpecialPic = _
  rw [chosen_point_specialClass, chosen_zero_specialClass]
  change divisorCode _ - divisorCode _ = _
  simp only [N13RationalPointEndgame.specialPointClass, picCode_abel, divisorCode_mk]
  ring

end
end MazurProof.N13ConstructedSpecialization
