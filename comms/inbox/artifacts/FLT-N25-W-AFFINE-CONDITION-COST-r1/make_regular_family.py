from pathlib import Path
import re
r=Path(__file__).parent
rr=(r/'RiemannRochSpaceFamilyInput.lean').read_text()
rr=rr[:rr.index('#print axioms')]+'end MazurProof.N25F_RiemannRochSpace\n'
mem=(r/'DedekindOrderMembershipCheck.lean').read_text().split('#print axioms')[0]
imports=[]
for s in [rr,mem]:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
imports+=['import Mathlib.RingTheory.Localization.FractionRing']
base='\n'.join(imports)+'\n'+''.join('\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n' for s in [rr,mem])
head='''
namespace MazurProof.N25F_WRegularSectionLift
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_DedekindOrderMembership
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop := ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) := {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem boundary_isBoundary (b : Boundary → C.Atom) (t : Boundary) :
  IsBoundary C b (b t) := ⟨t, rfl⟩
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (ZMod 2) S]
variable (principal : Additive ((FractionRing S)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing S)ˣ),
  (h.toMul : FractionRing S) = (f.toMul : FractionRing S) + (g.toMul : FractionRing S) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum S)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
def basePoleDivisor : C.Divisor :=
  Finsupp.single (boundaryAtom .X) 1 + Finsupp.single (boundaryAtom .YZ) 1 +
    Finsupp.single (boundaryAtom .Z) 2
'''
src=(r/'N25F_WRegularSectionLift.lean').read_text()
body=src[src.index('private theorem basePoleDivisor_nonBoundary'):src.index('end MazurProof.N25F_WRegularSectionLift')]
body=body.replace('projectivePrincipalDivisor_apply_nonBoundary _ A, nonBoundaryPrincipalDivisor_apply','haff _ A')
for a,b in [('fullNonBoundaryAtomEquivHeightOne','e'),('fullBoundaryAtomOfTag_isFullBoundaryAtom','boundary_isBoundary C boundaryAtom'),('FullNonBoundaryAtom25Two','NonBoundary C boundaryAtom'),('FullBoundaryTag25Two','Boundary'),('fullBoundaryAtomOfTag','boundaryAtom'),('basePoleDivisor25Two','(basePoleDivisor C boundaryAtom)')]:body=body.replace(a,b)
body=re.sub(r'\bW\b','S',body).replace('W⁰','S⁰')
body=re.sub(r'\bK\b','(FractionRing S)',body)
common='C S principal hmin boundaryAtom e haff'
args={'basePoleDivisor_nonBoundary':'C boundaryAtom','fullRiemannRochSpace25Two':'C principal hmin'}
names=['existsUnique_wChart_lift_of_mem_basePole_space','wRegularSectionLift25Two','algebraMap_wRegularSectionLift25Two','wRegularSectionLift_zero','wRegularSectionLift_add','wRegularSectionLiftLinearMap25Two','wRegularSectionLiftLinearMap25Two_injective']
args.update({n:common for n in names})
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('simp [(basePoleDivisor C boundaryAtom),','simp [basePoleDivisor,')
body=body.replace('/-- Every genuine nH section','include haff in\n/-- Every genuine nH section')
out=base+head+body
for n in ['existsUnique_wChart_lift_of_mem_basePole_space','wRegularSectionLift25Two','algebraMap_wRegularSectionLift25Two','wRegularSectionLiftLinearMap25Two','wRegularSectionLiftLinearMap25Two_injective']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WRegularSectionLift\n'
(r/'WRegularSectionLiftFamilyCheck.lean').write_text(out)
