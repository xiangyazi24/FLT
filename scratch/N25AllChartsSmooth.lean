import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoSmooth

/-!
# N25 all-chart smoothness regression entry

The completed proof now lives in the formal library module imported above.
This scratch entry keeps the former checkpoint path usable without duplicating
the full structural proof.
-/

open MazurProof.RationalPointsN25QuotientTwoSmooth

#check @MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth.chartCoordinateRing_smooth

#print axioms MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth.chartCoordinateRing_smooth

#check @MazurProof.RationalPointsN25QuotientTwoSmooth.canonicalProjectiveCurveToSpec_smooth

#print axioms MazurProof.RationalPointsN25QuotientTwoSmooth.canonicalProjectiveCurveToSpec_smooth

#check
  @canonicalProjectiveCurveToSpec_smoothOfRelativeDimension

#print axioms
  canonicalProjectiveCurveToSpec_smoothOfRelativeDimension
