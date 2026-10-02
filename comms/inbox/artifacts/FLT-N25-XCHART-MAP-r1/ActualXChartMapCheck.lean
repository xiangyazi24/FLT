import FLT.Assumptions.MazurProof.N25F_XChartFractionMap

noncomputable section

open MazurProof.N25F_XChartFractionMap
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

local notation "W" => MazurProof.N25F_NonBoundaryPrincipalDivisor.W

#synth IsDomain W

example : (qx : W) ≠ 0 := qx_ne_zero

example : XChartRing →ₐ[ZMod 2] FractionRing W := xChartToFraction

example : xChartToFraction xY =
    algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qx :=
  xChartToFraction_xY

example : xChartToFraction xZ =
    algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qx :=
  xChartToFraction_xZ

example : xChartToFraction xW = 1 / algebraMap W (FractionRing W) qx :=
  xChartToFraction_xW

#print axioms MazurProof.N25F_XChartFractionMap.qx_ne_zero
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xY
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xZ
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xW
