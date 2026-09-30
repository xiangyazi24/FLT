import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence
import FLT.Assumptions.MazurProof.N13InfinitySpecialPointClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N13CoherentPointReduction

/-- Corrected R09.

The point-specific spread is genuinely coherent on both fibres by
construction, so its special class is exactly the anchored Abel class of
proper reduction. -/
theorem pointSpreadLine_specialClass_rationalAbel
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    N13RationalCurvePointPicardRealization.specialClass
        (N13RationalCurvePointPicardRealization.pointSpreadLine P) =
      N13RationalPointEndgame.specialPointClass
        (N13ProperCurveReduction.reduceCurve P) := by
  exact
    (N13RationalCurvePointPicardRealization.data P).special_eq

/-- Counterexample to the uniqueness premise proposed for the old R09.

The negative-infinity Mumford raw datum can be put on the vertically
saturated positive-infinity integral line simply by reorienting its generic
infinity integer.  Reorientation leaves its special divisor unchanged.
Consequently the resulting datum has the exact negative-infinity generic
Mumford raw value but specializes to the positive-anchor class, not to the
proper reduction of the rational negative-infinity point. -/
theorem exactRaw_saturated_does_not_determine_specialClass :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13TwoChartPicardRealization.Model
          (SexticMumford.infinityMinusMumford
            N13TwoChartPicardRealization.Model) ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated
        R.charts ∧
      R.toSpecialPic ≠
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve
            (.infinityMinus :
              N13RationalPointEndgame.RationalCurvePoint)) := by
  let D :
      SexticMumford.Mumford
        N13TwoChartPicardRealization.Model :=
    SexticMumford.infinityMinusMumford
      N13TwoChartPicardRealization.Model

  let R₀ : N13TwoChartPicardRealization.Data :=
    N13InfinityPointPicardRealization.infinityPlusData

  let R : N13TwoChartPicardRealization.Data :=
    N13RationalPicardSpreadExistence.reorientData D R₀

  have hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          R₀.charts.affineIdeal =
        SexticMumford.mumfordIdeal
          N13TwoChartPicardRealization.Model D.u D.v := by
    change
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          N13InfinityPointPicardRealization.infinityPlusLine.affineIdeal =
        SexticMumford.mumfordIdeal
          N13TwoChartPicardRealization.Model D.u D.v
    dsimp only [D]
    simpa [SexticMumford.zero,
      SexticMumford.infinityMinusMumford] using
      N13InfinityPointPicardRealization.map_infinityPlusLine_affineIdeal

  have hraw :
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13TwoChartPicardRealization.Model D := by
    exact
      N13RationalPicardSpreadExistence.reorientData_genericRaw
        D R₀ hmap

  have hsat :
      N13TwoChartPicardRealization.AffineVerticallySaturated
        R.charts := by
    apply
      N13RationalPicardSpreadExistence.reorientData_affineVerticallySaturated
    change
      N13TwoChartPicardRealization.AffineVerticallySaturated
        N13InfinityPointPicardRealization.infinityPlusLine
    exact
      N13InfinityPointPicardRealization.infinityPlusLine_affineVerticallySaturated

  have hplus_ne_minus :
      N13InfinityPointPicardRealization.infinityPlusData.toSpecialPic ≠
        N13InfinityPointPicardRealization.infinityMinusData.toSpecialPic := by
    rw [
      N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic,
      N13InfinityPointPicardRealization.infinityMinusData_toSpecialPic,
      N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor,
      N13InfinityLineSpecialRestriction.specialInfinityMinusPoint_eq_specialCusp,
      N13InfinitySpecialPointClass.specialPointClass_infinityMinus_eq_canonicalClass
    ]
    exact
      N13InfinitySpecialPointClass.specialPointClass_specialAnchor_ne_canonicalClass

  have hminusProper :
      N13InfinityPointPicardRealization.infinityMinusData.toSpecialPic =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve
            (.infinityMinus :
              N13RationalPointEndgame.RationalCurvePoint)) := by
    exact
      N13RationalCurvePointPicardRealization.infinityMinusData.special_eq

  have hbad :
      R.toSpecialPic ≠
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve
            (.infinityMinus :
              N13RationalPointEndgame.RationalCurvePoint)) := by
    intro h
    apply hplus_ne_minus
    calc
      N13InfinityPointPicardRealization.infinityPlusData.toSpecialPic =
          R.toSpecialPic := by
        rfl
      _ =
          N13RationalPointEndgame.specialPointClass
            (N13ProperCurveReduction.reduceCurve
              (.infinityMinus :
                N13RationalPointEndgame.RationalCurvePoint)) :=
        h
      _ =
          N13InfinityPointPicardRealization.infinityMinusData.toSpecialPic :=
        hminusProper.symm

  refine ⟨R, ?_, hsat, hbad⟩
  simpa only [D] using hraw

end MazurProof.N13CoherentPointReduction

