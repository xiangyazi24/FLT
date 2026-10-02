from pathlib import Path
r=Path(__file__).parent
twist=(r/'N25F_NormBaseTwist.lean').read_text()
(r/'NormBaseTwistCheck.lean').write_text(twist+'\n#print axioms MazurProof.N25F_NormBaseTwist.norm_twist\n')
s=(r/'N25F_InfinityAffineNormComparison.lean').read_text()
s=s.replace('import FLT.Assumptions.MazurProof.N25F_InfinityNormalization','import InfinityNormalizationCheck\nimport Mathlib.RingTheory.Norm.Basic').replace('import FLT.Assumptions.MazurProof.N25F_NormBaseTwist','')
g=twist[twist.index('set_option'):]
s=s.replace('set_option synthInstance.maxHeartbeats 200000',g+'\nset_option synthInstance.maxHeartbeats 200000',1)
s=s.replace('attribute [local instance] infinityRationalAlgebra','''variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [Module.Finite BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityRationalAlgebra''')
comp=s
s=s.replace('end MazurProof.N25F_InfinityAffineNormComparison','''#print axioms MazurProof.N25F_NormBaseTwist.norm_twist
#print axioms affineFieldNorm
#print axioms infinity_norm_eq_baseInversion_affine_norm
end MazurProof.N25F_InfinityAffineNormComparison''')
(r/'InfinityAffineNormComparisonCheck.lean').write_text(s)
b=(r/'N25F_BaseInversionOrder.lean').read_text()
b=b.replace('import FLT.Assumptions.MazurProof.N25F_RationalBaseInversion','import N25F_RationalBaseInversion').replace('import FLT.Assumptions.MazurProof.N25F_InfinityPrimeContraction','import Mathlib.Algebra.Polynomial.FieldDivision')
marker='set_option synthInstance.maxHeartbeats 200000'
b=b.replace(marker,'''namespace MazurProof.N25F_InfinityPrimeContraction
open N25F_RationalBaseInversion
noncomputable def infinityBasePrime : Ideal BasePolynomial := Ideal.span {Polynomial.X}
instance infinityBasePrime_isMaximal : infinityBasePrime.IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
end MazurProof.N25F_InfinityPrimeContraction

'''+marker,1)
b=b.replace('end MazurProof.N25F_BaseInversionOrder','''#print axioms baseVariable_inverse_fractionOrder
#print axioms baseInversion_polynomial_order
end MazurProof.N25F_BaseInversionOrder''')
(r/'BaseInversionOrderCheck.lean').write_text(b)
a=(r/'N25F_AffineNormPolynomial.lean').read_text()
a=a[a.index('set_option'):]
a=a.replace('local instance : Algebra BaseField CurveField :=','''variable [Module.IsTorsionFree BasePolynomial W]
variable [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable [hWrank : Fact (Module.finrank BasePolynomial W = 4)]
local instance : Algebra BaseField CurveField :=''')
a=a.replace('rw [affineRationalBaseToField_finrank]', 'rw [affineRationalBaseToField_finrank hWrank.out]')
a=a.replace('end MazurProof.N25F_AffineNormPolynomial','''#print axioms affineFieldNorm_algebraMap
end MazurProof.N25F_AffineNormPolynomial''')
(r/'AffineNormPolynomialCheck.lean').write_text('import Mathlib.RingTheory.IntegralClosure.IntegralRestrict\n'+comp+'\n'+a)
