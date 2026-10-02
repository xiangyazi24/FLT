import FLT.Assumptions.MazurProof.N25F_ZChartFractionMap

noncomputable section

open MazurProof
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv
open N25F_ZChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

#synth Module.IsTorsionFree (Polynomial (ZMod 2)) W
#synth IsDomain W
#check (algebraMap_Rz_X : algebraMap (Polynomial (ZMod 2)) W Polynomial.X = qz)
#check (qz_ne_zero : (qz : W) ≠ 0)
#check (zChartToFraction : ZChartRing →ₐ[ZMod 2] FractionRing W)
#check (zChartToFraction_zX : zChartToFraction zX =
  algebraMap W (FractionRing W) qx / algebraMap W (FractionRing W) qz)
#check (zChartToFraction_zY : zChartToFraction zY =
  algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qz)
#check (zChartToFraction_zW : zChartToFraction zW =
  1 / algebraMap W (FractionRing W) qz)

#print axioms algebraMap_Rz_X
#print axioms qz_ne_zero
#print axioms fraction_qz_ne_zero
#print axioms zChartToFraction
#print axioms zChartToFraction_zX
#print axioms zChartToFraction_zY
#print axioms zChartToFraction_zW
