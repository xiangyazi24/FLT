import FLT.Assumptions.MazurProof.N25F_ZChartWChartEquiv

#check MazurProof.N25F_ZChartWChartEquiv.zChartAlgEquivWChart
#print axioms MazurProof.N25F_ZChartWChartEquiv.zChartAlgEquivWChart
#print axioms MazurProof.N25F_ZChartWChartEquiv.zChartRing_isDomain
#print axioms MazurProof.N25F_ZChartWChartEquiv.zChartRing_isDedekindDomain

example : IsDedekindDomain
    MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal.ZChartRing := inferInstance
