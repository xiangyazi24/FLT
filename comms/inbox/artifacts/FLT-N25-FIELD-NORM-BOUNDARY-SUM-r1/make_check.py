from pathlib import Path
r=Path(__file__).parent
s=(r/'N25F_InfinityNormFraction.lean').read_text()
s=s.replace('import FLT.Assumptions.MazurProof.N25F_InfinityCanonicalSeparable','import InfinityNormalizationCheck')
s=s.replace('open N25F_InfinityNormalization N25F_InfinityBoundaryAlgebras','open N25F_InfinityNormalization')
marker='attribute [local instance] infinityPolynomialAlgebra infinityRationalAlgebra'
s=s.replace(marker,'''variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [hWrank : Fact (Module.finrank BasePolynomial N25F_NonBoundaryPrincipalDivisor.W = 4)]
variable [hSep : @Algebra.IsSeparable BaseField CurveField _ _ infinityRationalAlgebra]
variable [Module.IsTorsionFree BasePolynomial InfinityNormalization]
'''+marker)
s=s.replace('infinityRationalBaseToField_finite_finrank.1','(infinityRationalBaseToField_finite_finrank hWrank.out).1')
s=s.replace('end MazurProof.N25F_InfinityNormFraction','''#print axioms infinity_norm_normalization
#print axioms infinity_norm_fraction
#print axioms exists_normalization_fraction
end MazurProof.N25F_InfinityNormFraction''')
(r/'InfinityNormFractionCheck.lean').write_text(s)
