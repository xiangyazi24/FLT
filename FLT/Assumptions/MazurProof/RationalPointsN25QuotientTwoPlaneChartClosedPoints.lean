import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartDimension
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDivisor
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenResidueDegree
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointKernelNonzero

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartClosedPoints

open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoClosedPointChart
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoPlaneChartDimension
open RationalPointsN25QuotientTwoPlaneChartDomain
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenResidueDegree
open RationalPointsN25QuotientTwoClosedPointKernelNonzero
open RationalPointsN25QuotientTwoAffineCanonicalDifferentials
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBinaryFieldSemantics

private abbrev k := ZMod 2
private abbrev W :=
  RationalPointsN25QuotientTwoAffineChartsSmooth.ChartQuotient 3

def hyperplanePointWOnChart : CurvePointOnChart 3 k :=
  ⟨hyperplanePointW, rfl⟩

@[simp]
theorem hyperplanePointW_chartEval_denominator :
    chartQuotientEval 3 hyperplanePointWOnChart
        canonicalWChartProjectionDenominator = 0 := by
  simp [canonicalWChartProjectionDenominator, projectionDenominator,
    canonicalWChartX, canonicalWChartZ, canonicalWChartPoint,
    chartQuotientPoint, mappedAmbientPoint, chartMap,
    hyperplanePointWOnChart, chartQuotientEval_mk,
    chartPointAffineEval, normalizedCoordinates25,
    NormalizedProjective4.coordinates, fieldBinaryOperations,
    ambientDehomogenize, dehomogenizedVariable, hyperplanePointW,
    coordinates4ToFun]

theorem canonicalWChartProjectionDenominator_not_isUnit :
    ¬ IsUnit canonicalWChartProjectionDenominator := by
  intro h
  have hmapped := h.map (chartQuotientEval 3 hyperplanePointWOnChart)
  rw [hyperplanePointW_chartEval_denominator] at hmapped
  exact not_isUnit_zero hmapped

theorem canonicalWChart_not_isField : ¬ IsField W := by
  intro h
  obtain ⟨b, hb⟩ := h.mul_inv_cancel
    canonicalWChartProjectionDenominator_isRegular.ne_zero
  have hbmap := congrArg
    (chartQuotientEval 3 hyperplanePointWOnChart) hb
  rw [map_mul, hyperplanePointW_chartEval_denominator, zero_mul,
    map_one] at hbmap
  exact zero_ne_one hbmap

/-- Every maximal ideal of the canonical plane chart is nonzero. -/
theorem canonicalWChart_maximal_ne_bot
    (m : Ideal W) (hm : m.IsMaximal) : m ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hm canonicalWChart_not_isField

/-- Every maximal ideal of the canonical plane chart has height one. -/
theorem canonicalWChart_maximal_height_eq_one
    (m : Ideal W) (hm : m.IsMaximal) : m.height = 1 :=
  canonicalWChart_prime_height_eq_one m hm.isPrime
    (canonicalWChart_maximal_ne_bot m hm)

/-- Every finite-field point evaluated on the canonical `w = 1` chart
defines a height-one maximal ideal. -/
theorem wChartPointPrime_height_eq_one
    {K : Type} [Field K] [Algebra k K] [Finite K]
    (P : CurvePointOnChart 3 K) :
    (chartPointPrime 3 P).asIdeal.height = 1 :=
  canonicalWChart_maximal_height_eq_one _
    (chartPointPrime_isMaximal 3 P)

/-! ## Arbitrary points of the projective `W != 0` open -/

/-- The residue ring cut out by evaluation on the fixed `w = 1` chart. -/
abbrev WOpenPointResidue
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :=
  WChartQuotient ⧸ RingHom.ker (wOpenChartQuotientEval P)

/-- A finite coefficient field makes the `W`-open point residue finite. -/
noncomputable instance wOpenPointResidue_finite
    {K : Type} [Field K] [CharP K 2] [Finite K]
    (P : CurvePointOnWOpen K) : Finite (WOpenPointResidue P) := by
  letI : Finite (wOpenChartQuotientEval P).range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Finite.of_equiv (wOpenChartQuotientEval P).range
    (RingHom.quotientKerEquivRange (wOpenChartQuotientEval P)).symm.toEquiv

/-- The finite residue domain of a `W`-open point is a field. -/
theorem wOpenPointResidue_isField
    {K : Type} [Field K] [CharP K 2] [Finite K]
    (P : CurvePointOnWOpen K) : IsField (WOpenPointResidue P) := by
  letI : (RingHom.ker (wOpenChartQuotientEval P)).IsPrime :=
    RingHom.ker_isPrime (wOpenChartQuotientEval P)
  exact Finite.isField_of_domain (WOpenPointResidue P)

/-- Every finite-field point of the projective `W != 0` open defines a
maximal ideal of the fixed `w = 1` chart. -/
theorem wOpenChartQuotientEval_ker_isMaximal
    {K : Type} [Field K] [CharP K 2] [Finite K]
    (P : CurvePointOnWOpen K) :
    (RingHom.ker (wOpenChartQuotientEval P)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (wOpenPointResidue_isField P)

/-- Every finite-field point of the projective `W != 0` open defines a
height-one maximal ideal of the fixed integral chart. -/
theorem wOpenChartQuotientEval_ker_height_eq_one
    {K : Type} [Field K] [CharP K 2] [Finite K]
    (P : CurvePointOnWOpen K) :
    (RingHom.ker (wOpenChartQuotientEval P)).height = 1 :=
  canonicalWChart_maximal_height_eq_one _
    (wOpenChartQuotientEval_ker_isMaximal P)

/-- The fixed-chart evaluation kernel of every positive exact-period point
on the `W` open is explicitly nonzero. -/
theorem exactPeriodicWOpen_eval_ker_ne_bot
    (d : ℕ) (hd : 0 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hW : (normalizedCoordinates25 Q.1.1).w ≠ 0) :
    RingHom.ker (wOpenChartQuotientEval
      (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d))) ≠ ⊥ := by
  exact ker_ne_bot_of_kaehler_equiv_of_range_natCard
    (wOpenChartQuotientEval
      (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d)))
    (chartKaehlerDifferentialEquiv 3) hd
    (exactPeriodicWOpen_eval_range_card d hd Q hW)

/-- Every positive exact-period point on the `W` open has a residue field of
cardinality `2^d` and a nonzero height-one maximal evaluation kernel. -/
theorem exactPeriodicWOpen_eval_closedPoint_data
    (d : ℕ) (hd : 0 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hW : (normalizedCoordinates25 Q.1.1).w ≠ 0) :
    Nat.card (wOpenChartQuotientEval
        (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d))).range = 2 ^ d ∧
      (RingHom.ker (wOpenChartQuotientEval
        (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d)))).IsMaximal ∧
      (RingHom.ker
        (wOpenChartQuotientEval
          (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d)))).height = 1 := by
  exact ⟨exactPeriodicWOpen_eval_range_card d hd Q hW,
    wOpenChartQuotientEval_ker_isMaximal ⟨Q.1, hW⟩,
    wOpenChartQuotientEval_ker_height_eq_one ⟨Q.1, hW⟩⟩

end MazurProof.RationalPointsN25QuotientTwoPlaneChartClosedPoints
