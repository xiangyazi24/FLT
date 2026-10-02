from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'SectionClassFiberFamilyInput.lean').read_text()
base=base[:base.index('#print axioms FullEffectiveClassFiber25Two')]
base+='end MazurProof.N25F_SectionClassFiber\n'
base=base.replace('import Mathlib.FieldTheory.Finiteness','import Mathlib.FieldTheory.Finiteness\nimport Mathlib.Algebra.Module.Submodule.Equiv')
src=(r/'N25F_SectionPrincipalTransport.lean').read_text()
body=src[src.index('/-- The actual principal relation'):src.index('end MazurProof.N25F_SectionPrincipalTransport')]
for a,b in [('fullProjectiveClassOf_eq_iff_exists_principal','N25F_SectionClassFiber.class_eq_iff C principal'),('fullProjectivePrincipalSubgroup25Two','principal.range'),('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C'),('CurveField','L')]:body=body.replace(a,b)
names=['mul_mem_fullRiemannRochSpace25Two','principalSectionLinearEquiv25Two','finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq','fullClassSectionRank25Two','fullClassSectionRank25Two_classOf','fullRiemannRochSpace25Two']
for n in names:
 body=re.sub(r'\b'+n+r'\b(?!\s*\((D|n)\s*:)(?!\s*:)',n+' C principal hmin',body)
 for kind in ['def','theorem']:
  body=body.replace(kind+' '+n+' C principal hmin',kind+' '+n)
# Nullary definitions become definitions on the explicit family data.
body=body.replace('def fullClassSectionRank25Two :','def fullClassSectionRank25Two :')
head='''
namespace MazurProof.N25F_SectionPrincipalTransport
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
'''
out=base+head+body
for n in names[:-1]:out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_SectionPrincipalTransport\n'
(r/'SectionPrincipalTransportFamilyCheck.lean').write_text(out)
