from pathlib import Path
r=Path(__file__).parent
s=(r/'N25F_InfinityCanonicalSeparable.lean').read_text()
c=s.replace('import FLT.Assumptions.MazurProof.N25F_InfinityFiberComplete','import InfinityNormalizationCheck').replace('import FLT.Assumptions.MazurProof.N25F_InfinitySeparable\n','').replace('import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras\n','').replace('open N25F_InfinityNormalization N25F_InfinityBoundaryAlgebras','open N25F_InfinityNormalization')
cut='local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W\n';c=c.replace(cut,cut+'''variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.IsTorsionFree BasePolynomial InfinityNormalization]
variable [IsFractionRing InfinityNormalization CurveField]
variable [hSep : @Algebra.IsSeparable BaseField CurveField _ _ infinityRationalAlgebra]
''')
c=c.replace('''  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra
''','')
c=c.replace('''local instance : Algebra.IsSeparable BaseField CurveField :=
  infinityRationalBaseToField_isSeparable
''','')
c=c.replace('end MazurProof.N25F_InfinityCanonicalSeparable','''#check @infinityCanonicalFraction_isSeparable
#print axioms canonicalFractionRing_isSeparable
#print axioms infinityCanonicalFraction_isSeparable
end MazurProof.N25F_InfinityCanonicalSeparable''')
assert c == (r/'InfinityCanonicalSeparableCheck.lean').read_text(), 'Checked fixture mismatch'
print('Exact checked fixture reproduced')
