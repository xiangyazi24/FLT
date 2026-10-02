from pathlib import Path
import re
r=Path(__file__).parent
space=(r/'RiemannRochSpaceFamilyInput.lean').read_text().split('#print axioms')[0]
space+='end MazurProof.N25F_RiemannRochSpace\n'
binary=(r/'N25F_BinaryResidueOrder.lean').read_text()
allimports=[]
for s in [space,binary]: allimports.extend(x for x in s.splitlines() if x.startswith('import '))
allimports.append('import Mathlib.LinearAlgebra.FiniteDimensional.Basic')
def noimports(s): return '\n'.join(x for x in s.splitlines() if not x.startswith('import '))
out='\n'.join(dict.fromkeys(allimports))+'\n'+noimports(space)+'\n'+noimports(binary)+'\n'
src=(r/'N25F_ZeroDegreeConstants.lean').read_text()
unit=src[src.index('private theorem unit_mk0_eq'):src.index('theorem one_mem_fullRiemannRochSpace25Two_zero')].replace('CurveField','L')
body=src[src.index('theorem one_mem_fullRiemannRochSpace25Two_zero'):src.index('end MazurProof.N25F_ZeroDegreeConstants')]
body=body.replace('    letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra\n','')
body=body.replace('    letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing\n','')
for a,b in [('fullBoundaryAtomOfTag .X','x'),('projectivePrincipalDivisor_apply_X','hpoint'),
 ('projectivePrincipalDivisor','principal'),('fullClosedPointGrading25Two','C'),
 ('xLocalResidueRingEquivF2','e'),('XLocalRing','R'),('CurveField','L')]: body=body.replace(a,b)
body=re.sub(r'\bxBoundaryOrder f\b','WithZero.log (Ring.ordFrac R (f.toMul : L))',body)
body=body.replace('simp [ClosedPointGrading.divisorDegree]', 'simp [ClosedPointGrading.divisorDegree, hdeg]')
body=body.replace('fullRiemannRochSpace25Two_eq_bot_of_degree_neg _ hD',
 'fullRiemannRochSpace25Two_eq_bot_of_degree_neg C principal hmin hzero _ hD')
body=re.sub(r'\bfullRiemannRochSpace25Two\b', '(fullRiemannRochSpace25Two C principal hmin)',body)
args='(C := C) (principal := principal) (hmin := hmin)'
more=args+' (hzero := hzero) (x := x) (hdeg := hdeg) (hpoint := hpoint)'
allargs=more+' (e := e)'
mapping={'one_mem_fullRiemannRochSpace25Two_zero':args,
 'xBoundaryOrder_eq_zero_of_mem_zero':more,
 'mem_fullRiemannRochSpace25Two_zero_iff':allargs,
 'fullRiemannRochSpace25Two_zero_eq_span_one':allargs,
 'fullPrincipalDivisor_eq_zero_iff':allargs}
for name,aa in mapping.items():
 body=re.sub(r'\b'+name+r'\b', '('+name+' '+aa+')',body)
 body=body.replace('theorem ('+name+' '+aa+')','theorem '+name)
body=body.replace('instance fullRiemannRochSpace25Two_zero_finite', 'theorem fullRiemannRochSpace25Two_zero_finite')
body=body.replace('/-- A nonzero globally regular function', 'include hzero hdeg hpoint in\n/-- A nonzero globally regular function')
body=body.replace('/-- Every globally regular function', 'include hzero hdeg hpoint e in\n/-- Every globally regular function')
body=body.replace('/-- The degree-zero section space', 'include hzero hdeg hpoint e in\n/-- The degree-zero section space')
body=body.replace('/-- The full principal', 'include hmin hzero hdeg hpoint e in\n/-- The full principal')
for name in ['fullRiemannRochSpace25Two_zero_finite','finrank_fullRiemannRochSpace25Two_zero']:
 body=body.replace('theorem '+name,'include hzero hdeg hpoint e in\ntheorem '+name)
out+='''namespace MazurProof.N25F_ZeroDegreeConstants
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_BinaryResidueOrder
variable {L : Type*} [Field L]
'''+unit+'''
variable (C : ClosedPointGrading) [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (x : C.Atom) (hdeg : C.atomDegree x = 1)
variable (hpoint : ∀ f : Additive Lˣ, principal f x = WithZero.log (Ring.ordFrac R (f.toMul : L)))
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
'''+body+'''
#print axioms one_mem_fullRiemannRochSpace25Two_zero
#print axioms xBoundaryOrder_eq_zero_of_mem_zero
#print axioms mem_fullRiemannRochSpace25Two_zero_iff
#print axioms fullRiemannRochSpace25Two_zero_eq_span_one
#print axioms fullRiemannRochSpace25Two_zero_finite
#print axioms finrank_fullRiemannRochSpace25Two_zero
#print axioms fullPrincipalDivisor_eq_zero_iff
#print axioms fullPrincipalDivisor_injective
end MazurProof.N25F_ZeroDegreeConstants
'''
(r/'ZeroDegreeConstantsFamilyCheck.lean').write_text(out)
