from pathlib import Path
import re
r=Path(__file__).parent
rr=(r/'RiemannRochSpaceFamilyInput.lean').read_text()
rr=rr[:rr.index('#print axioms')]+ 'end MazurProof.N25F_RiemannRochSpace\n'
bi=(r/'BinaryResidueCancellationCheck.lean').read_text()
bi=bi[:bi.index('#print axioms')]
imports=[]
for s in [rr,bi]:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
def stripimports(s):return '\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n'
base='\n'.join(imports)+'\n'+stripimports(rr)+stripimports(bi)
src=(r/'N25F_XSectionFiltration.lean').read_text()
unit=src[src.index('private theorem unit_mk0_eq'):src.index('/-- Removing the genuine X point')].replace('CurveField','L')
body=src[src.index('/-- Removing the genuine X point'):src.index('end MazurProof.N25F_XSectionFiltration')]
body=body.replace('  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra\n','').replace('  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing\n','')
for a,b in [('projectivePrincipalDivisor_apply_X','hcoeff'),('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),('CurveField','L'),('XLocalRing','R'),('xLocalResidueRingEquivF2','e')]:body=body.replace(a,b)
body=re.sub(r'\bxBoundaryOrder\b','boundaryOrder R',body)
args={'fullRiemannRochSpace25Two':'C principal hmin','fullRiemannRochSpace25Two_sub_X_le':'C principal hmin XPoint','mem_fullRiemannRochSpace25Two_sub_X_iff':'C principal hmin R XPoint hcoeff','xBoundaryOrder_eq_neg_of_not_mem_sub_X':'C principal hmin R XPoint hcoeff','sub_mem_fullRiemannRochSpace25Two_sub_X':'C principal hmin R XPoint hcoeff e'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 body=body.replace('theorem '+n+' '+a,'theorem '+n)
for marker in ['/-- Membership in the next','/-- A section outside the next']:
 body=body.replace(marker,'include hcoeff in\n'+marker)
body=body.replace('/-- All sections outside','include hcoeff e in\n/-- All sections outside')
head='''
namespace MazurProof.N25F_XSectionFiltration
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_BinaryResidueCancellation
variable {L : Type*} [Field L]
'''+unit+'''
variable (C : ClosedPointGrading) [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
def boundaryOrder (f : Additive Lˣ) : ℤ := WithZero.log (Ring.ordFrac R (f.toMul : L))
variable (XPoint : C.Atom)
variable (hcoeff : ∀ f : Additive Lˣ, principal f XPoint = boundaryOrder R f)
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
'''
out=base+head+body
for n in list(args)[1:]:out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_XSectionFiltration\n'
(r/'XSectionFiltrationFamilyCheck.lean').write_text(out)
