import FLT.Assumptions.MazurProof.N25F_WChartPrincipalDegree

open MazurProof.N25F_NonBoundaryPrincipalDivisor
open MazurProof.N25F_ProjectiveDivisorSplit
open MazurProof.N25F_ProjectiveDivisorDegree

example (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ) :=
  wChart_principal_degree_eq_quotient_finrank a ha f hf

#print axioms MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank
