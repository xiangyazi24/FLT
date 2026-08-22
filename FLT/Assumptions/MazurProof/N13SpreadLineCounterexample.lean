import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence
import FLT.Assumptions.MazurProof.N13InfinitySpecialPointClass

/-!
# Counterexample to specialization on arbitrary N13 spread lines

`SpreadLine` stores its generic infinity orientation independently of the
two-chart line and its special divisor.  Reorienting the negative-infinity
line to the generic zero class therefore produces the same stored rational
class as the positive-infinity line but a different special class.
-/

namespace MazurProof.N13SpreadLineCounterexample

noncomputable section

open N13RationalCurvePointPicardRealization

/-- The negative-infinity geometry with its independent generic orientation
reset to the identity Mumford representative. -/
def negativeZeroData : N13TwoChartPicardRealization.Data :=
  N13RationalPicardSpreadExistence.reorientData
    (SexticMumford.zero N13TwoChartPicardRealization.Model)
    N13InfinityPointPicardRealization.infinityMinusData

/-- The negative-infinity line and the identity representative have the same
affine Mumford ideal; their distinction is entirely at infinity. -/
theorem negativeZeroData_affineIdeal :
    Ideal.map N13IntegralFractionalHull.integralToRational
        N13InfinityPointPicardRealization.infinityMinusData.charts.affineIdeal =
      SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model
        (SexticMumford.zero N13TwoChartPicardRealization.Model).u
        (SexticMumford.zero N13TwoChartPicardRealization.Model).v := by
  change Ideal.map N13IntegralFractionalHull.integralToRational
      N13InfinityPointPicardRealization.infinityMinusLine.affineIdeal = _
  simpa [SexticMumford.infinityMinusMumford, SexticMumford.zero] using
    N13InfinityPointPicardRealization.map_infinityMinusLine_affineIdeal

theorem negativeZeroData_toGenericPic : negativeZeroData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂
      (0 : N13RationalPointEndgame.G) := by
  rw [negativeZeroData,
    N13RationalPicardSpreadExistence.reorientData_toGenericPic
      (SexticMumford.zero N13TwoChartPicardRealization.Model)
      N13InfinityPointPicardRealization.infinityMinusData
      negativeZeroData_affineIdeal,
    SexticMumford.classOf_zero, map_zero]

/-- The coherent positive-infinity realization of the rational identity. -/
def positiveZeroLine : SpreadLine where
  rationalClass := 0
  realization := N13InfinityPointPicardRealization.infinityPlusData
  generic_eq := by
    rw [N13InfinityPointPicardRealization.infinityPlusData_toGenericPic,
      SexticMumford.classOf_zero, map_zero]

/-- An incoherent realization allowed by `SpreadLine`: its stored rational
class is zero while its special geometry remains the negative-infinity line. -/
def negativeZeroLine : SpreadLine where
  rationalClass := 0
  realization := negativeZeroData
  generic_eq := negativeZeroData_toGenericPic

@[simp] theorem positiveZeroLine_rationalClass :
    positiveZeroLine.rationalClass = 0 := rfl

@[simp] theorem negativeZeroLine_rationalClass :
    negativeZeroLine.rationalClass = 0 := rfl

theorem positiveZeroLine_specialClass_ne_negativeZeroLine :
    specialClass positiveZeroLine ≠ specialClass negativeZeroLine := by
  change N13InfinityPointPicardRealization.infinityPlusData.toSpecialPic ≠
    negativeZeroData.toSpecialPic
  change N13InfinityPointPicardRealization.infinityPlusData.toSpecialPic ≠
    N13InfinityPointPicardRealization.infinityMinusData.toSpecialPic
  rw [N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic,
    N13InfinityPointPicardRealization.infinityMinusData_toSpecialPic,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor,
    N13InfinityLineSpecialRestriction.specialInfinityMinusPoint_eq_specialCusp,
    N13InfinitySpecialPointClass.specialPointClass_infinityMinus_eq_canonicalClass]
  exact
    N13InfinitySpecialPointClass.specialPointClass_specialAnchor_ne_canonicalClass

theorem positiveZeroLine_genericClass_eq_negativeZeroLine :
    genericClass (⊥ : AddSubgroup N13RationalPointEndgame.G) positiveZeroLine =
      genericClass (⊥ : AddSubgroup N13RationalPointEndgame.G) negativeZeroLine := by
  unfold genericClass
  rw [positiveZeroLine_rationalClass, negativeZeroLine_rationalClass]

set_option maxHeartbeats 800000 in
-- Packaging the dependent spread witnesses requires expanding both records.
/-- The all-spread specialization reflection statement at the trivial kernel
is false for the current `SpreadLine` carrier. -/
theorem exists_same_generic_bottom_distinct_special :
    ∃ L M : SpreadLine,
      genericClass (⊥ : AddSubgroup N13RationalPointEndgame.G) L =
          genericClass (⊥ : AddSubgroup N13RationalPointEndgame.G) M ∧
        specialClass L ≠ specialClass M := by
  exact ⟨positiveZeroLine, negativeZeroLine,
    positiveZeroLine_genericClass_eq_negativeZeroLine,
    positiveZeroLine_specialClass_ne_negativeZeroLine⟩

end


end MazurProof.N13SpreadLineCounterexample
