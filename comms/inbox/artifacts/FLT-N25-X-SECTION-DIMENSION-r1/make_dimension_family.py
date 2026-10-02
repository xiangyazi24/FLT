from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'SectionFinitenessFamilyInput.lean').read_text()
base=base[:base.index('#print axioms MazurProof.CurveZetaEffectiveDivisors.')]
base+='end MazurProof.N25F_SectionFiniteness\n'
base=base.replace('import Mathlib.RingTheory.Finiteness.Basic','import Mathlib.RingTheory.Finiteness.Basic\nimport Mathlib.LinearAlgebra.FiniteDimensional.Lemmas')
head='''
namespace MazurProof.N25F_XSectionDimension
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
variable (XPoint : C.Atom)
variable (hle : ∀ D : C.Divisor,
  fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) ≤
  fullRiemannRochSpace25Two C principal hmin D)
variable (hsub : ∀ D : C.Divisor, ∀ a b : L,
  a ∈ fullRiemannRochSpace25Two C principal hmin D →
  b ∈ fullRiemannRochSpace25Two C principal hmin D →
  a ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) →
  b ∉ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1) →
  a - b ∈ fullRiemannRochSpace25Two C principal hmin (D - Finsupp.single XPoint 1))
variable (hdegree : C.atomDegree XPoint = 1)
'''
src=(r/'N25F_XSectionDimension.lean').read_text()
body=src[src.index('/-- Any section at the extremal'):src.index('end MazurProof.N25F_XSectionDimension')]
for a,b in [('sub_mem_fullRiemannRochSpace25Two_sub_X','hsub'),('fullRiemannRochSpace25Two_sub_X_le','hle'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C'),('CurveField','L')]:body=body.replace(a,b)
args={'fullRiemannRochSpace25Two':'C principal hmin','fullRiemannRochSpace25Two_eq_sub_X_sup_span':'C principal hmin XPoint hle hsub','finrank_fullRiemannRochSpace25Two_le_sub_X_add_one':'C principal hmin hzero hinj XPoint hle hsub','finrank_fullRiemannRochSpace25Two_le_degree_add_one':'C principal hmin hzero hinj XPoint hle hsub hdegree','finrank_fullRiemannRochSpace25Two_X_quotient_le_one':'C principal hmin hzero hinj XPoint hle hsub','fullRiemannRochSpace25Two_eq_bot_of_degree_neg':'C principal hmin hzero'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 body=body.replace('theorem '+n+' '+a,'theorem '+n)
body=body.replace('/-- Any section at the extremal','include hle hsub in\n/-- Any section at the extremal')
body=body.replace('/-- Removing the actual degree-one','include hzero hinj hle hsub in\n/-- Removing the actual degree-one')
body=body.replace('/-- The actual elementary upper','include hzero hinj hle hsub hdegree in\n/-- The actual elementary upper')
body=body.replace('/-- The actual quotient by','include hzero hinj hle hsub in\n/-- The actual quotient by')
body=body.replace('  by_cases hle :','  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj (D - Finsupp.single XPoint 1)\n  by_cases hle :')
# Preserve the named proven inclusion argument when the local case split shadows its name.
body=body.replace('by_cases hle :','by_cases hback :').replace('finrank_mono hle','finrank_mono hback').replace('not_le_iff_exists.mp hle','not_le_iff_exists.mp hback')
body=body.replace('simp [ClosedPointGrading.divisorDegree]','simp [ClosedPointGrading.divisorDegree, hdegree]')
body=body.replace('  let P :=','  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj D\n  let P :=')
out=base+head+body
for n in ['fullRiemannRochSpace25Two_eq_sub_X_sup_span','finrank_fullRiemannRochSpace25Two_le_sub_X_add_one','finrank_fullRiemannRochSpace25Two_le_degree_add_one','finrank_fullRiemannRochSpace25Two_X_quotient_le_one']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_XSectionDimension\n'
(r/'XSectionDimensionFamilyCheck.lean').write_text(out)
