import FLT.Assumptions.MazurProof.N25F_YZLocalDVR

#print axioms MazurProof.N25F_YZLocalDVR.yzWGerm_ne_zero
#print axioms MazurProof.N25F_YZLocalDVR.yzLocalRing_not_isField
#print axioms MazurProof.N25F_YZLocalDVR.yzLocalRing_isDiscreteValuationRing
example : IsDiscreteValuationRing
    MazurProof.RationalPointsN25QuotientTwoWBoundaryYZLocal.YZLocalRing := inferInstance
