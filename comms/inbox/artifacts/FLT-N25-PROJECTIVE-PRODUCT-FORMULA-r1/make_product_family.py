from pathlib import Path
import re
r=Path(__file__).parent
c=Path('/workspace/shared/flt-n25-norm-base-inversion')
sources=[(c/'AffineNormPolynomialCheck.lean').read_text(),(c/'BaseInversionOrderCheck.lean').read_text()]
imports=[]; bodies=[]
for s in sources:
 lines=s.splitlines()
 imports.extend(x for x in lines if x.startswith('import '))
 bodies.append('\n'.join(x for x in lines if not x.startswith('import ') and not x.startswith('#print axioms')))
imports.append('import Lean.Elab.Tactic.Omega')
out='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies)+'\n'
src=(r/'N25F_ProjectiveProductFormula.lean').read_text()
helper=src[src.index('private theorem hom_zero_of_regular'):src.index('open N25F_RationalBaseInversion')]
out+='namespace MazurProof.N25F_ProjectiveProductFormula\n'+helper
header='''
open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityPrimeContraction
open N25F_InfinityAffineNormComparison N25F_BaseInversionOrder N25F_AffineNormPolynomial
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial W] [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable [hWrank : Fact (Module.finrank BasePolynomial W = 4)]
attribute [local instance] infinityRationalAlgebra
variable {Divisor : Type*} [AddCommGroup Divisor]
variable (principal : Additive CurveFieldˣ →+ Divisor) (degree : Divisor →+ ℤ)
variable (bx byz bz affineDegree : Additive CurveFieldˣ → ℤ)
variable (hsum : ∀ f : Additive CurveFieldˣ,
 WithZero.log (Ring.ordFrac (Localization.AtPrime infinityBasePrime)
   (Algebra.norm BaseField (f.toMul : CurveField))) = bx f + byz f + bz f)
variable (hsplit : ∀ f : Additive CurveFieldˣ,
 degree (principal f) = bx f + byz f + bz f + affineDegree f)
variable (hquot : ∀ (a : W), a ≠ 0 → ∀ (f : Additive CurveFieldˣ),
 (f.toMul : CurveField) = algebraMap W CurveField a →
 affineDegree f = (Module.finrank (ZMod 2) (W ⧸ Ideal.span {a}) : ℤ))
variable (hnormdim : ∀ (a : W), a ≠ 0 →
 Module.finrank (ZMod 2) (W ⧸ Ideal.span {a}) = (Algebra.norm BasePolynomial a).natDegree)
'''
body=src[src.index('/-- Degree zero for every'):src.index('end MazurProof.N25F_ProjectiveProductFormula')]
body=body.replace('fullClosedPointGrading25Two.divisorDegree','degree')
for a,b in [('infinity_norm_boundary_order_sum','hsum'),
 ('wChart_principal_degree_eq_quotient_finrank','hquot'),
 ('wChart_quotient_finrank_eq_natDegree_norm','hnormdim'),
 ('projectivePrincipalDivisor_degree','hsplit'),
 ('projectivePrincipalDivisor','principal'),('xBoundaryOrder','bx'),('yzBoundaryOrder','byz'),('zBoundaryOrder','bz')]:
 body=re.sub(r'\b'+a+r'\b',lambda _:b,body)
body=body.replace('/-- Degree zero for every','include hWrank hsum hsplit hquot hnormdim in\n/-- Degree zero for every',1)
body=body.replace('/-- The actual projective','include hWrank hsum hsplit hquot hnormdim in\n/-- The actual projective',1)
body=body.replace('projectivePrincipalDivisor_degree_regular a ha _ rfl',
 'projectivePrincipalDivisor_degree_regular principal degree bx byz bz affineDegree hsum hsplit hquot hnormdim a ha _ rfl')
out+=header+body+'''
#print axioms projectivePrincipalDivisor_degree_regular
#print axioms projectivePrincipalDivisor_degree_eq_zero
end MazurProof.N25F_ProjectiveProductFormula
'''
(r/'ProjectiveProductFormulaFamilyCheck.lean').write_text(out)
