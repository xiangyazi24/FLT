import FLT.Assumptions.MazurProof.N25F_WChartNormDimension

#check MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finrank_eq_natDegree_norm
#print axioms MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finrank_eq_natDegree_norm

example (a : MazurProof.N25F_NonBoundaryPrincipalDivisor.W) (ha : a ≠ 0) :
    Module.finrank (ZMod 2)
        (MazurProof.N25F_NonBoundaryPrincipalDivisor.W ⧸ Ideal.span ({a} : Set _)) =
      (Algebra.norm (Polynomial (ZMod 2)) a).natDegree :=
  MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finrank_eq_natDegree_norm a ha
