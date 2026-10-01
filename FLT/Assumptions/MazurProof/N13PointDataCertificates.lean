import FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The named point realizations carry the same effective raw/branch certificate
as the new arbitrary-class choices. This discharges point compatibility by
the proved integral comparison theorem, without changing any named point
data or its special divisor.
-/

namespace MazurProof.N13PointDataCertificates

noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem infinityPlus_certified : Certified N13InfinityPointPicardRealization.infinityPlusData := by
  refine ⟨(SexticMumford.zero Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityPlusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.zero]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityPlusLine_affineIdeal
  · simpa [positiveMultiplicity, negativeMultiplicity, SexticMumford.zero] using
      hasInfinityMultiplicities_tensor _ _ 1 0 1 0 infinityPlusLine_marked infinityPlusLine_marked

theorem infinityMinus_certified : Certified N13InfinityPointPicardRealization.infinityMinusData := by
  refine ⟨(SexticMumford.infinityMinusMumford Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityMinusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.infinityMinusMumford]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityMinusLine_affineIdeal
  · simpa [positiveMultiplicity, negativeMultiplicity, SexticMumford.infinityMinusMumford] using
      hasInfinityMultiplicities_tensor _ _ 0 1 1 0 infinityMinusLine_marked infinityPlusLine_marked

private theorem with_positive_anchor_marked (L : Line) (hL : HasInfinityMultiplicities L 0 0) :
    HasInfinityMultiplicities (N13TwoChartLineTensor.withPositiveInfinityMultiplicity L 1) 1 0 := by
  simpa [HasInfinityMultiplicities, N13TwoChartLineTensor.withPositiveInfinityMultiplicity,
    N13TwoChartLineTensor.positiveInfinityPowerLine, N13TwoChartLineTensor.tensorPow,
    N13TwoChartLineTensor.tensor, N13TwoChartLineTensor.one] using
    hasInfinityMultiplicities_tensor L _ 0 0 1 0 hL infinityPlusLine_marked

theorem integralPoint_certified (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Certified (N13IntegralPointPicardRealization.data P) := by
  let E := (N13IntegralPointPicardRealization.degreeOneMumford P).toSemi
  have hd : E.u.natDegree = 1 := by
    simp [E, N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
  have hn : E.nInf = 0 := rfl
  refine ⟨E, ?_, N13IntegralPointPicardRealization.data_genericRaw_eq_mumfordRaw P,
    N13IntegralPointPicardRealization.anchoredPointLine_affineVerticallySaturated P, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · change HasInfinityMultiplicities
      (N13TwoChartLineTensor.withPositiveInfinityMultiplicity
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P) 1)
      (positiveMultiplicity E) (negativeMultiplicity E)
    simpa [positiveMultiplicity, negativeMultiplicity, hd, hn] using
      with_positive_anchor_marked _ (integralPointLine_marked P)

theorem escapingPoint_certified (x y : Q₂) (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Certified (N13EscapingPointPicardRealization.data x y hx hxy) := by
  let E := (N13EscapingPointPicardRealization.degreeOneMumford x y hxy).toSemi
  have hd : E.u.natDegree = 1 := by
    simp [E, N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
  have hn : E.nInf = 0 := rfl
  refine ⟨E, ?_, N13EscapingPointPicardRealization.data_genericRaw_eq_mumfordRaw x y hx hxy,
    N13EscapingPointPicardRealization.anchoredPointLine_affineVerticallySaturated x y hx hxy, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · have hm : HasInfinityMultiplicities
        (N13IntegralInfinityPointSpread.nonintegralPointLine x y hx hxy) 0 0 := by
      apply infinityChartPointLine_marked
      exact N13LocalDlogRegimes.inverseIntegralPart_ne_zero x _
    change HasInfinityMultiplicities
      (N13TwoChartLineTensor.withPositiveInfinityMultiplicity
        (N13IntegralInfinityPointSpread.nonintegralPointLine x y hx hxy) 1)
      (positiveMultiplicity E) (negativeMultiplicity E)
    simpa [positiveMultiplicity, negativeMultiplicity, hd, hn] using with_positive_anchor_marked _ hm

theorem rationalPoint_certified (P : N13RationalPointEndgame.RationalCurvePoint) :
    Certified (N13RationalCurvePointPicardRealization.data P).realization := by
  cases P with
  | infinityPlus => exact infinityPlus_certified
  | infinityMinus => exact infinityMinus_certified
  | affine X Y hcurve =>
    have hC13 : N13CurveModel.C13SexticEq X Y := by
      rw [N13CurveModel.C13SexticEq, ← N13Mumford.f_eval_eq_sexticF13]
      exact hcurve
    let x₂ : Q₂ := N13ProperCurveReduction.ratToQ₂ X
    let y₂ : Q₂ := N13ProperCurveReduction.ratToQ₂ (N13GoodModelTwo.sexticToGoodY X Y)
    have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
      N13ProperCurveReduction.map_good_equation hC13
    by_cases hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1
    · rw [N13RationalCurvePointPicardRealization.data, dif_pos hx]
      change Certified (N13IntegralPointPicardRealization.data
        (N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood))
      exact integralPoint_certified _
    · rw [N13RationalCurvePointPicardRealization.data, dif_neg hx]
      have hxval : x₂.valuation < 0 :=
        lt_of_not_ge ((Padic.norm_le_one_iff_val_nonneg x₂).not.mp hx)
      change Certified (N13EscapingPointPicardRealization.data x₂ y₂ hxval hgood)
      exact escapingPoint_certified x₂ y₂ hxval hgood

theorem chooseUncalibrated_point_compatible (P : N13RationalPointEndgame.RationalCurvePoint) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (chooseUncalibrated (N13RationalPointEndgame.rationalAbel P)).charts
      (N13RationalCurvePointPicardRealization.data P).realization.charts) := by
  apply comparison_of_generic_eq _ _ (chooseUncalibrated_certified _) (rationalPoint_certified P)
  rw [chooseUncalibrated_generic, (N13RationalCurvePointPicardRealization.data P).generic_eq]

end
end MazurProof.N13PointDataCertificates
