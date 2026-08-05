import FLT.Assumptions.MazurProof.N13EscapingPointSpecialRestriction
import FLT.Assumptions.MazurProof.N13TwoChartPicardRealization

/-!
# Picard realization of escaping degree-one N13 points

An escaping affine point is integral on the ordinary infinity chart.  Its
proper point line reduces to the canonical reduced infinity point.  Tensoring
once with the positive-infinity point line supplies the second special point
required by the degree-two Abel model, while preserving the generic affine
ideal exactly.

The explicit oriented integer is `-1`: a degree-one affine Mumford point has
`nInf = 0`, and `SexticMumford.mumfordRaw` records `nInf - 1`.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13EscapingPointPicardRealization

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The two-adic coefficient field used by the proper reduction and the
oriented generic Picard model. -/
abbrev Q₂ : Type :=
  N13EscapingPointSpecialRestriction.Q₂

/-- The good completed-square sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13TwoChartPicardRealization.Model

/-- Proper two-chart lines on the integral good model. -/
abbrev Line : Type :=
  N13TwoChartPicardRealization.Line

/-- Algebra structure used to extend an integral fractional ideal to the
generic sextic coordinate ring. -/
local instance integralRationalAlgebra :
    Algebra N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

/-- The common function field is the fraction field of the integral affine
coordinate ring. -/
local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- The balanced degree-one Mumford representative of the original affine
point.  Its infinity multiplicity is zero because the point is affine. -/
abbrev degreeOneMumford
    (x y : Q₂)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.Mumford Model :=
  SexticMumford.pointMumford Model
    (N13EscapingDegreeOneSpread.curvePoint x y hxy)

/-- The two chart-field equalities assemble into literal equality between
the unanchored special restriction and the canonical reduced point pair. -/
theorem restrict_nonintegralPointLine_eq_point
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityPointSpread.nonintegralPointLine
          x y hx hxy) =
      N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_affineIdeal
        x y hx hxy
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_infinityIdeal
        x y hx hxy

/-- The anchored line restricts to the canonical chart pair of the literal
degree-two divisor formed by the reduced point and the positive anchor. -/
theorem restrict_anchoredPointLine_eq_ofDivisor
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartSpecialRestriction.restrict
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy) =
      N13SpecialDivisorCharts.ofDivisor
        (N13EscapingPointSpecialRestriction.anchoredDivisor
          x y hx hxy) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact
      N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_affineIdeal
        x y hx hxy
  · exact
      N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_infinityIdeal
        x y hx hxy

/-- Full two-fibre realization data for an escaping degree-one Mumford point.

The positive-infinity tensor factor supplies special degree two.  The marked
generic order remains `-1`, which is the oriented exponent of an affine
degree-one Mumford representative. -/
def data
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.Data where
  charts :=
    N13EscapingPointSpecialRestriction.anchoredPointLine
      x y hx hxy
  infinityOrder := -1
  specialDivisor :=
    N13EscapingPointSpecialRestriction.anchoredDivisor
      x y hx hxy
  special_affine :=
    N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_affineIdeal
      x y hx hxy
  special_infinity :=
    N13EscapingPointSpecialRestriction.restrict_anchoredPointLine_infinityIdeal
      x y hx hxy

/-- Adding the positive-infinity anchor leaves the generic affine ideal
unchanged, so it remains the standard Mumford ideal of the original point. -/
theorem map_anchoredPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (degreeOneMumford x y hxy).u
        (degreeOneMumford x y hxy).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy).affineIdeal =
      _
  rw [N13EscapingPointSpecialRestriction.anchoredPointLine,
    N13TwoChartLineTensor.map_withPositiveInfinityMultiplicity_affineIdeal]
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (N13EscapingDegreeOneSpread.lift x y hx hxy)) =
      _
  exact
    N13EscapingDegreeOneSpread.genericIdeal_eq_pointMumford
      x y hx hxy

/-- The generic fractional-ideal unit of the anchored proper line is exactly
the unit packaged by the degree-one Mumford representative. -/
theorem genericIdealUnit_anchoredPointLine_eq_pointMumford
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericIdealUnit
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy) =
      SexticMumford.mumfordIdealUnit Model
        (degreeOneMumford x y hxy).toSemi := by
  apply Units.ext
  rw [N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      (map_anchoredPointLine_affineIdeal x y hx hxy)

/-- The oriented raw datum of the anchored line is literally the Mumford raw
datum; the ideal units agree and both oriented exponents are `-1`. -/
theorem genericRaw_anchoredPointLine_eq_mumfordRaw
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericRaw
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford x y hxy) := by
  apply Prod.ext
  · change
      N13TwoChartPicardRealization.genericIdealUnit
          (N13EscapingPointSpecialRestriction.anchoredPointLine
            x y hx hxy) =
        SexticMumford.mumfordIdealUnit Model
          (degreeOneMumford x y hxy).toSemi
    exact
      genericIdealUnit_anchoredPointLine_eq_pointMumford
        x y hx hxy
  · change
      Multiplicative.ofAdd (-1 : ℤ) =
        Multiplicative.ofAdd
          (((degreeOneMumford x y hxy).nInf : ℤ) - 1)
    simp [degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]

/-- The generic raw datum stored by `data` is the literal Mumford raw datum,
not merely the same class modulo principal oriented ideals. -/
theorem data_genericRaw_eq_mumfordRaw
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.genericRaw
        (data x y hx hxy).charts
        (data x y hx hxy).infinityOrder =
      SexticMumford.mumfordRaw Model
        (degreeOneMumford x y hxy) := by
  change
    N13TwoChartPicardRealization.genericRaw
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      _
  exact
    genericRaw_anchoredPointLine_eq_mumfordRaw
      x y hx hxy

/-- Consequently the generic Picard class carried by the two-fibre data is
the standard oriented class of the original degree-one Mumford point. -/
theorem data_toGenericPic_eq_classOf
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (data x y hx hxy).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        (degreeOneMumford x y hxy) := by
  change
    N13TwoChartPicardRealization.genericClass
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x y hx hxy)
        (-1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        (degreeOneMumford x y hxy)
  unfold N13TwoChartPicardRealization.genericClass
    SexticMumford.classOf
  rw [genericRaw_anchoredPointLine_eq_mumfordRaw]

end

end MazurProof.N13EscapingPointPicardRealization
