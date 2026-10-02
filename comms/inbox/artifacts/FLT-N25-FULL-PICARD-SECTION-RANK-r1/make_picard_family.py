from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'SectionPrincipalTransportFamilyCheck.lean').read_text()
base=base[:base.index('#print axioms mul_mem_fullRiemannRochSpace25Two')]
base+='end MazurProof.N25F_SectionPrincipalTransport\n'
base=base.replace('import Mathlib.FieldTheory.Finiteness','import Mathlib.FieldTheory.Finiteness\nimport Mathlib.Algebra.Ring.GeomSum')
p=(r/'picard-source.lean').read_text()
core='namespace MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading\nvariable (C : ClosedPointGrading)\n'
core+=p[p.index('noncomputable def classDegree'):p.index('/-! ## Translation and canonical residual duality')]
core+='end MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading\n'
cs=(r/'class-number-source.lean').read_text()
core+='namespace MazurProof.CurveZetaClassNumber\nopen scoped BigOperators\n'
core+=cs[cs.index('def linearSystemCard ('):cs.index('/-- Casting the natural-valued')]
core+='end MazurProof.CurveZetaClassNumber\n'
head='''
namespace MazurProof.N25F_FullPicardSectionRank
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace
open N25F_SectionClassFiber N25F_SectionPrincipalTransport
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
include hzero in
omit [Algebra (ZMod 2) L] in
theorem principal_le_degree_ker : principal.range ≤ C.divisorDegree.ker := by
  rintro D ⟨f, rfl⟩
  exact hzero f
def fullClassDegree : C.DivisorClass principal.range →+ ℤ :=
  C.classDegree principal.range (principal_le_degree_ker C principal hzero)
omit [Algebra (ZMod 2) L] in
@[simp]
theorem fullClassDegree_classOf (D : C.Divisor) :
    fullClassDegree C principal hzero (C.classOf principal.range D) = C.divisorDegree D := rfl
'''
src=(r/'N25F_FullPicardSectionRank.lean').read_text()
body=src[src.index('/-- The actual section dimension'):src.index('end MazurProof.N25F_FullPicardSectionRank')]
for a,b in [('fullProjectivePrincipalSubgroup25Two_le_degree_ker','(principal_le_degree_ker C principal hzero)'),('fullProjectivePrincipalSubgroup25Two','principal.range'),('fullProjectiveClassDegree25Two_classOf','fullClassDegree_classOf C principal hzero'),('fullProjectiveClassDegree25Two','(fullClassDegree C principal hzero)'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C')]:body=body.replace(a,b)
args={'fullPicardSectionRank25Two':'C principal hmin hzero','fullEffectiveClassFiberEquiv25Two':'C principal hzero','fullEffectiveClass_fiber_card25Two':'C principal hmin hzero hinj','fullEffectiveClass_fiber_linearSystemCard25Two':'C principal hmin hzero hinj','FullEffectiveClassFiber25Two':'C principal','fullEffectiveClassFiber25Two_card':'C principal hmin hzero hinj','fullClassSectionRank25Two':'C principal hmin','fullClassSectionRank25Two_classOf':'C principal hmin'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('congrArg fullClassSectionRank25Two C principal hmin','congrArg (fullClassSectionRank25Two C principal hmin)')
body=body.replace('/-- The existing full effectiveClass','include hinj in\n/-- The existing full effectiveClass')
body=body.replace('/-- This is the exact full-grading','include hinj in\n/-- This is the exact full-grading')
out=base+core+head+body
for n in ['fullPicardSectionRank25Two','fullEffectiveClassFiberEquiv25Two','fullEffectiveClass_fiber_card25Two','fullEffectiveClass_fiber_linearSystemCard25Two']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_FullPicardSectionRank\n'
(r/'FullPicardSectionRankFamilyCheck.lean').write_text(out)
