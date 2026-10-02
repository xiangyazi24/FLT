from pathlib import Path
import re
r=Path(__file__).parent
def seg(s,a,b): return s[s.index(a):s.index(b,s.index(a))]
base=(r/'SectionFinitenessFamilyInput.lean').read_text()
base=base[:base.index('#print axioms MazurProof.CurveZetaEffectiveDivisors.')]
base+='end MazurProof.N25F_SectionFiniteness\n'
base=base.replace('import Mathlib.Logic.Equiv.Option','import Mathlib.Logic.Equiv.Option\nimport Mathlib.FieldTheory.Finiteness\nimport Mathlib.GroupTheory.QuotientGroup.Defs\nimport Mathlib.SetTheory.Cardinal.NatCard')
p=(r/'picard-source.lean').read_text()
picard='namespace MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading\nvariable (C : ClosedPointGrading)\n'
picard+=seg(p,'abbrev DivisorClass','/-- Divisor degree descends')
picard+='end MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading\n'
head='''
namespace MazurProof.N25F_SectionClassFiber
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
omit [Algebra (ZMod 2) L] in
theorem class_eq_iff (D E : C.Divisor) :
  C.classOf principal.range D = C.classOf principal.range E ↔
  ∃ f : Additive Lˣ, principal f = D - E := by
  change ((D : C.Divisor ⧸ principal.range) = E) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl
'''
src=(r/'N25F_SectionClassFiber.lean').read_text()
body=seg(src,'/-- Effective full divisors','end MazurProof.N25F_SectionClassFiber')
for a,b in [('fullProjectiveClassOf_eq_iff_exists_principal','class_eq_iff C principal'),('fullProjectivePrincipalSubgroup25Two','principal.range'),('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C'),('CurveField','L')]:body=body.replace(a,b)
args={'FullEffectiveClassFiber25Two':'C principal', 'NonzeroSection25Two':'C principal hmin','fullRiemannRochSpace25Two':'C principal hmin',
 'nonzeroSectionToFullClassFiber25Two':'C principal hmin hzero',
 'nonzeroSectionToFullClassFiber25Two_injective':'C principal hmin hzero hinj',
 'nonzeroSectionToFullClassFiber25Two_surjective':'C principal hmin hzero',
 'nonzeroSectionEquivFullClassFiber25Two':'C principal hmin hzero hinj',
 'effectiveDivisorOfNonzeroSection25Two':'C principal hmin hzero',
 'effectiveDivisorOfNonzeroSection25Two_cast':'C principal hmin hzero',
 'effectiveDivisorOfNonzeroSection25Two_injective':'C principal hmin hzero hinj',
 'fullRiemannRochSpace25Two_card':'C principal hmin hzero hinj',
 'nonzeroSection25Two_card':'C principal hmin hzero hinj',
 'fullEffectiveClassFiber25Two_card':'C principal hmin hzero hinj'}
for n,a in args.items():body=re.sub(r'\b'+n+r'\b(?!\s*\(D :)',n+' '+a,body)
body=body.replace('theorem nonzeroSectionToFullClassFiber25Two_injective','include hinj in\ntheorem nonzeroSectionToFullClassFiber25Two_injective')
body=body.replace('theorem fullRiemannRochSpace25Two_card','include hzero hinj in\ntheorem fullRiemannRochSpace25Two_card')
body=body.replace('theorem nonzeroSection25Two_card','include hzero hinj in\ntheorem nonzeroSection25Two_card')
body=body.replace('/-- The exact finite class-fibre','include hmin hzero hinj in\n/-- The exact finite class-fibre')
body=body.replace('  simpa only [Nat.card_zmod]','  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj D\n  simpa only [Nat.card_zmod]')
body=body.replace('  have h := Nat.card_congr','  letI := nonzeroSection25Two_finite C principal hmin hzero hinj D\n  have h := Nat.card_congr')
out=base+picard+head+body
for n in ['FullEffectiveClassFiber25Two','nonzeroSectionToFullClassFiber25Two','nonzeroSectionToFullClassFiber25Two_injective','nonzeroSectionToFullClassFiber25Two_surjective','nonzeroSectionEquivFullClassFiber25Two','fullRiemannRochSpace25Two_card','nonzeroSection25Two_card','fullEffectiveClassFiber25Two_card']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_SectionClassFiber\n'
(r/'SectionClassFiberFamilyCheck.lean').write_text(out)
