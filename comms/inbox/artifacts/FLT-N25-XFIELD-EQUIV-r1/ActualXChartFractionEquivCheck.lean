import FLT.Assumptions.MazurProof.N25F_XChartFractionEquiv

open MazurProof.N25F_XChartFractionEquiv
open MazurProof.N25F_XChartFractionMap
open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin

example : Function.Surjective xFractionToFraction := xFractionToFraction_surjective
example : FractionRing XChartRing ≃ₐ[ZMod 2]
    FractionRing MazurProof.N25F_NonBoundaryPrincipalDivisor.W := xChartFractionAlgEquiv
example : letI : Algebra XChartRing
      (FractionRing MazurProof.N25F_NonBoundaryPrincipalDivisor.W) :=
        xChartToFraction.toRingHom.toAlgebra
    IsFractionRing XChartRing
      (FractionRing MazurProof.N25F_NonBoundaryPrincipalDivisor.W) :=
  xChartToFraction_isFractionRing

#print axioms xFractionToFraction_surjective
#print axioms xChartFractionAlgEquiv
#print axioms xChartToFraction_isFractionRing
