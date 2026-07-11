import FLT.Assumptions.MazurProof.N12RawBranchEuler
import FLT.Assumptions.MazurProof.N12DividedBranchUnit
import FLT.Assumptions.MazurProof.N12ParamBridge
import FLT.Assumptions.MazurProof.N12DoubleLegDegenerate
import FLT.Assumptions.MazurProof.N12E1FullCoverBridge

/-!
# Downstream checked-descent adapters for N=12

This file intentionally sits downstream of `N12FourSquaresAP` and
`N12QuarticEisenstein` through `N12RawBranchEuler` and
`N12DividedBranchUnit`.  Lower files should not import it.
-/

namespace MazurProof.RationalPointsN12

/-- Checked inhabitant of the rational four-square AP obstruction. -/
theorem checked_FourRatSquaresAPConst : FourRatSquaresAPConst :=
  fourRatSquaresAPConst_checked

/-- Checked inhabitant of the integer four-square AP obstruction. -/
theorem checked_FourIntSquaresAPConst : FourIntSquaresAPConst :=
  fourIntSquaresAPConst_checked

/-- Checked inhabitant of the primitive centered descent theorem. -/
theorem checked_PrimitiveCenteredFourSqAPDescent :
    PrimitiveCenteredFourSqAPDescent :=
  primitiveCenteredFourSqAPDescent_checked

/-- Checked inhabitant of the raw Eisenstein square-branch factor
contradiction. -/
theorem checked_RawSqBranchDescentFromFactorsStatement :
    RawSqBranchDescentFromFactorsStatement :=
  rawSqBranchDescentFromFactorsStatement

/-- Checked inhabitant of the raw square-branch descent interface expected by
the quartic assembly layer. -/
theorem checked_DescentFromBranchUnorderedStatement :
    DescentFromBranchUnorderedStatement :=
  descentFromBranchUnordered_of_rawSqBranchFactorization

/-- Checked nonunit raw square-branch descent interface. -/
theorem checked_RawSqBranchNonunitDescendsStatement :
    RawSqBranchNonunitDescendsStatement :=
  rawSqBranchNonunitDescendsStatement_of_rawSqBranchFactorization

/-- Checked divided-by-`3` branch factorization. -/
theorem checked_DividedSqBranchFactorizationStatement :
    DividedSqBranchFactorizationStatement :=
  dividedSqBranchFactorizationStatement

/-- Checked unit theorem for the divided-by-`3` branch. -/
theorem checked_DividedSquareBranchUnitStatement :
    DividedSquareBranchUnitStatement :=
  dividedSquareBranchUnitStatement

/-- Checked divided-by-`3` branch interface expected by the quartic assembly
layer. -/
theorem checked_DividedSquareBranchUnitOrDescendsStatement :
    DividedSquareBranchUnitOrDescendsStatement :=
  dividedSquareBranchUnitOrDescendsStatement_of_unit

/-- Checked adapter from the primitive Eisenstein-triple parametrization
frontier to the branch parametrization expected by the normalized descent
assembly. -/
theorem checked_NormalizedBadParamStatement_of_tripleParamOrUnit
    (hTriple : EisensteinTriplePrimitiveParamOrUnit) :
    NormalizedBadParamStatement :=
  normalizedBadParamStatement_of_tripleParamOrUnit hTriple

/-- Checked primitive positive Eisenstein-triple full parametrization. -/
theorem checked_EisensteinTriplePrimitiveFullParamStatement :
    EisensteinTriplePrimitiveFullParamStatement :=
  eisensteinTriplePrimitiveFullParamStatement_checked

/-- Checked adapter from the stronger primitive Eisenstein-triple full
parametrization frontier to the branch parametrization expected by descent. -/
theorem checked_NormalizedBadParamStatement_of_tripleFullParam
    (hFull : EisensteinTriplePrimitiveFullParamStatement) :
    NormalizedBadParamStatement :=
  normalizedBadParamStatement_of_tripleFullParam hFull

/-- Checked branch parametrization statement for the normalized quartic
descent assembly. -/
theorem checked_NormalizedBadParamStatement :
    NormalizedBadParamStatement :=
  checked_NormalizedBadParamStatement_of_tripleFullParam
    checked_EisensteinTriplePrimitiveFullParamStatement

/-- Checked primitive Eisenstein quartic theorem conditional only on the
primitive Eisenstein-triple parametrization frontier. -/
theorem checked_IntQuarticEisensteinPrimitive_of_tripleParamOrUnit
    (hTriple : EisensteinTriplePrimitiveParamOrUnit) :
    IntQuarticEisensteinPrimitive :=
  intQuarticEisensteinPrimitiveFromDescentStatement
    normalizedOfBadStatement
    (normalizedBadParamStatement_of_tripleParamOrUnit hTriple)
    checked_DescentFromBranchUnorderedStatement
    checked_DividedSquareBranchUnitOrDescendsStatement

/-- Checked primitive Eisenstein quartic theorem conditional on the stronger
full-parametrization frontier. -/
theorem checked_IntQuarticEisensteinPrimitive_of_tripleFullParam
    (hFull : EisensteinTriplePrimitiveFullParamStatement) :
    IntQuarticEisensteinPrimitive :=
  checked_IntQuarticEisensteinPrimitive_of_tripleParamOrUnit
    (tripleParamOrUnit_of_fullParam hFull)

/-- Checked primitive integer Eisenstein quartic theorem. -/
theorem checked_IntQuarticEisensteinPrimitive :
    IntQuarticEisensteinPrimitive :=
  checked_IntQuarticEisensteinPrimitive_of_tripleFullParam
    checked_EisensteinTriplePrimitiveFullParamStatement

/-- Checked rational Eisenstein quartic degeneration, obtained by clearing
denominators to the checked primitive integer theorem. -/
theorem checked_RatQuarticEisensteinDegenerate :
    RatQuarticEisensteinDegenerate :=
  ratQuarticEisensteinDegenerate_of_primitive
    checked_IntQuarticEisensteinPrimitive

/-- Checked double-leg obstruction for the degenerate full-cover residuals. -/
theorem checked_DoubleLegCoverDegenerate :
    DoubleLegCoverDegenerate :=
  doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate
    checked_RatQuarticEisensteinDegenerate

/-- Checked concrete common-denominator clearing for selected squareclass
representatives on the full `E1` cover. -/
theorem checked_CommonDenomSquareclassRepsToPrimitiveCoverIntStatement :
    CommonDenomSquareclassRepsToPrimitiveCoverIntStatement :=
  commonDenomSquareclassRepsToPrimitiveCoverInt_checked

/-- Checked denominator-clearing layer from supported squareclasses to
primitive integer full-cover data. -/
theorem checked_E1FullCoverIntDataOfFactorSquareclassesStatement :
    E1FullCoverIntDataOfFactorSquareclassesStatement :=
  e1FullCoverIntDataOfFactorSquareclasses_checked

/-- Checked p-adic valuation parity layer for the three full-cover factors on
`E1`, away from the primes `2` and `3`. -/
theorem checked_E1FactorEvenPadicOutside23Statement :
    E1FactorEvenPadicOutside23Statement :=
  e1FactorEvenPadicOutside23_checked

/-- Checked squareclass-support extraction from even valuation outside
`{2,3}`. -/
theorem checked_SquareclassSupportedOn23OfEvenPadicOutside23Statement :
    SquareclassSupportedOn23OfEvenPadicOutside23Statement :=
  squareclassSupportedOn23_of_evenPadicOutside23_checked

/-- Compatibility wrapper for the split extraction assembly from explicit
front-end inputs. -/
theorem checked_E1FullCoverSquareclassExtractionIntStatement_from_residuals
    (hval : E1FactorEvenPadicOutside23Statement)
    (hsq : SquareclassSupportedOn23OfEvenPadicOutside23Statement) :
    E1FullCoverSquareclassExtractionIntStatement :=
  e1_full_cover_extraction_from_split_residuals
    hval hsq checked_E1FullCoverIntDataOfFactorSquareclassesStatement

/-- Compatibility wrapper when only the squareclass-support input is supplied. -/
theorem checked_E1FullCoverSquareclassExtractionIntStatement_of_squareclass
    (hsq : SquareclassSupportedOn23OfEvenPadicOutside23Statement) :
    E1FullCoverSquareclassExtractionIntStatement :=
  e1_full_cover_extraction_from_split_residuals
    checked_E1FactorEvenPadicOutside23Statement
    hsq
    checked_E1FullCoverIntDataOfFactorSquareclassesStatement

/-- Fully checked full-cover extraction for the shifted `N = 12` curve. -/
theorem checked_E1FullCoverSquareclassExtractionIntStatement :
    E1FullCoverSquareclassExtractionIntStatement :=
  e1_full_cover_extraction_from_split_residuals
    checked_E1FactorEvenPadicOutside23Statement
    checked_SquareclassSupportedOn23OfEvenPadicOutside23Statement
    checked_E1FullCoverIntDataOfFactorSquareclassesStatement

/-- Checked finite `2`-adic full-cover survivor enumeration. -/
theorem checked_E1CoverIntTwoAdicSurvivorsStatement :
    E1CoverIntTwoAdicSurvivorsStatement :=
  e1CoverIntTwoAdicSurvivorsStatement_checked

/-- Checked finite squareclass/local-obstruction survivor enumeration. -/
theorem checked_E1CoverIntSurvivingTriplesStatement :
    E1CoverIntSurvivingTriplesStatement :=
  e1CoverIntSurvivingTriples_checked

/-- Checked core elimination for primitive integer full-cover data. -/
theorem checked_E1CoverIntDataEliminationCoreStatement :
    E1CoverIntDataEliminationCoreStatement :=
  e1CoverIntDataEliminationCore_of_survivingTriples
    checked_FourRatSquaresAPConst
    checked_DoubleLegCoverDegenerate
    checked_E1CoverIntSurvivingTriplesStatement

/-- Checked elimination of nonzero-`Y` full-cover integer data. -/
theorem checked_E1FullCoverIntDataEliminationStatement :
    E1FullCoverIntDataEliminationStatement :=
  e1FullCoverIntDataElimination_of_core
    checked_E1CoverIntDataEliminationCoreStatement

/-- Checked finite `X`-coordinate classification on `E1`. -/
theorem checked_E1XCoordinateClassification :
    E1XCoordinateClassification :=
  e1XCoordinateClassification_of_fullCover
    checked_E1FullCoverSquareclassExtractionIntStatement
    checked_E1FullCoverIntDataEliminationStatement

/-- Checked `F_N12` boundary from the full-cover pipeline. -/
theorem checked_F_N12_boundary_of_fullCover
    {X Y : ℚ}
    (hF : F_N12_AffineEquation X Y) :
    F_N12_XBoundary X :=
  F_N12_boundary_of_fullCover
    checked_E1FullCoverSquareclassExtractionIntStatement
    checked_E1FullCoverIntDataEliminationStatement
    hF

/-- Checked original `E_N12` degenerate boundary from the full-cover pipeline. -/
theorem checked_E_N12_degenerate_boundary_of_fullCover
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    MazurProof.E_N12_DegenerateParameter u :=
  E_N12_degenerate_boundary_of_fullCover
    checked_E1FullCoverSquareclassExtractionIntStatement
    checked_E1FullCoverIntDataEliminationStatement
    u w h

/-- Checked square-denominator obstruction from the full-cover pipeline. -/
theorem checked_N12NoNontrivialSquareDenominatorResidual_of_fullCover :
    N12NoNontrivialSquareDenominatorResidual :=
  N12NoNontrivialSquareDenominatorResidual_of_fullCover
    checked_E1FullCoverSquareclassExtractionIntStatement
    checked_E1FullCoverIntDataEliminationStatement

/-- Checked rational Eisenstein quartic `X`-classification from the full-cover
pipeline. -/
theorem checked_RatQuarticEisensteinXClassification_of_fullCover :
    RatQuarticEisensteinXClassification :=
  ratQuarticEisensteinXClassification_of_fullCover
    checked_E1FullCoverSquareclassExtractionIntStatement
    checked_E1FullCoverIntDataEliminationStatement

/-- Generic adapter: any theorem consuming the rational four-square AP residual
can instead consume the primitive centered AP descent frontier. -/
theorem of_primitiveCenteredFourSqAPDescent_via_FourRatSquaresAPConst
    {P : Prop}
    (hdesc : PrimitiveCenteredFourSqAPDescent)
    (h : FourRatSquaresAPConst → P) :
    P :=
  h (fourRatSquaresAPConst_of_checked_descent hdesc)

/-- Checked adapter: any theorem still stated with the rational four-square AP
residual can now consume the proved N=12 four-square AP theorem directly. -/
theorem of_checked_FourRatSquaresAPConst
    {P : Prop}
    (h : FourRatSquaresAPConst → P) :
    P :=
  h checked_FourRatSquaresAPConst

/-- Checked no-argument form of the `(3,2,6)` AP cover collapse. -/
theorem coverQ_3_2_6_AP_const_checked
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    T ^ 2 = C ^ 2 ∧ C ^ 2 = A ^ 2 ∧ A ^ 2 = B ^ 2 :=
  coverQ_3_2_6_AP_const checked_FourRatSquaresAPConst h

/-- Checked no-argument form of the `(-1,-2,2)` AP cover collapse. -/
theorem coverQ_neg1_neg2_2_AP_const_checked
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A ^ 2 = B ^ 2 ∧ B ^ 2 = T ^ 2 ∧ T ^ 2 = C ^ 2 :=
  coverQ_neg1_neg2_2_AP_const checked_FourRatSquaresAPConst h

/-- Checked no-argument form of the `(3,2,6)` cover forcing `X = 3`. -/
theorem coverQ_3_2_6_forces_X_eq_three_checked
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (3 : ℚ) * (A / T) ^ 2)
    (hcover : CoverQ 3 2 6 A B C T) :
    X = 3 :=
  coverQ_3_2_6_forces_X_eq_three
    checked_FourRatSquaresAPConst hT hX hcover

/-- Checked no-argument form of the `(-1,-2,2)` cover forcing `X = -1`. -/
theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one_checked
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (-1 : ℚ) * (A / T) ^ 2)
    (hcover : CoverQ (-1) (-2) 2 A B C T) :
    X = -1 :=
  coverQ_neg1_neg2_2_forces_X_eq_neg_one
    checked_FourRatSquaresAPConst hT hX hcover

/-- Checked no-argument form of the `(1,1,1)` degenerate cover obstruction. -/
theorem coverQ_1_1_1_no_nonzero_checked
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    False :=
  coverQ_1_1_1_no_nonzero_of_ratQuarticEisensteinDegenerate
    checked_RatQuarticEisensteinDegenerate hA hB hC hT h

/-- Checked no-argument form of the `(-3,-1,3)` degenerate cover
obstruction. -/
theorem coverQ_neg3_neg1_3_no_nonzero_checked
    {A B C T : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ (-3) (-1) 3 A B C T) :
    False :=
  coverQ_neg3_neg1_3_no_nonzero_of_ratQuarticEisensteinDegenerate
    checked_RatQuarticEisensteinDegenerate hA hB hC hT h

end MazurProof.RationalPointsN12
