import FLT.Assumptions.MazurProof.N25F_XLocalDVR

noncomputable section

open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin
open MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
open MazurProof.N25F_XLocalDVR

#synth IsDedekindDomain XChartRing
#synth IsDomain XLocalRing
#synth IsDiscreteValuationRing XLocalRing

example : xW ≠ 0 := xW_ne_zero
example : xPrime ≠ ⊥ := xPrime_ne_bot
example : xWGerm ≠ 0 := xWGerm_ne_zero
example : Ring.ord XLocalRing xWGerm = 3 := xWGerm_ord_eq_three

#print axioms MazurProof.N25F_XLocalDVR.xChartRing_isDedekindDomain
#print axioms MazurProof.N25F_XLocalDVR.xW_ne_zero
#print axioms MazurProof.N25F_XLocalDVR.xPrime_ne_bot
#print axioms MazurProof.N25F_XLocalDVR.xLocalRing_isDiscreteValuationRing
#print axioms MazurProof.N25F_XLocalDVR.xWGerm_ne_zero
#print axioms MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal.xWGerm_ord_eq_three
