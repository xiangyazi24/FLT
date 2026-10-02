import FLT.Assumptions.MazurProof.N25F_WChartQuotientFinite

open MazurProof.N25F_NonBoundaryPrincipalDivisor

example (a : W) (ha : a ≠ 0) :
    Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) :=
  wChart_quotient_finite a ha

#print axioms MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finite
