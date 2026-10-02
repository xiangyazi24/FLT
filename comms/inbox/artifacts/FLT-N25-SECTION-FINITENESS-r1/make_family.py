from pathlib import Path
import re
r=Path(__file__).parent
def seg(s,a,b): return s[s.index(a):s.index(b,s.index(a))]
e=(r/'effective-source.lean').read_text()
p=(r/'picard-source.lean').read_text()
rr=(r/'RiemannRochSpaceFamilyInput.lean').read_text()
core=seg(e,'namespace MazurProof.CurveZetaEffectiveDivisors','/-- The number of effective divisors')
core+=seg(p,'abbrev Divisor :=','/-! ## Divisor classes')
core+='end ClosedPointGrading\nend MazurProof.CurveZetaEffectiveDivisors\n'
rr=seg(rr,'namespace MazurProof.N25F_RiemannRochSpace','#print axioms')+'end MazurProof.N25F_RiemannRochSpace\n'
src=(r/'N25F_SectionFiniteness.lean').read_text()
body=seg(src,'/-- The nonzero elements','end MazurProof.N25F_SectionFiniteness')
for a,b in [('projectivePrincipalDivisor_degree_eq_zero','hzero'),('fullPrincipalDivisor_injective','hinj'),('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C'),('CurveField','L')]: body=body.replace(a,b)
args={n:'C principal hmin' for n in ['NonzeroSection25Two','section_value_ne_zero','sectionUnit','section_divisor_nonneg','sectionEffectiveData','sectionEffectiveData_cast']}
args.update({n:'C principal hmin hzero' for n in ['effectiveDivisorOfNonzeroSection25Two','effectiveDivisorOfNonzeroSection25Two_cast']})
args.update({n:'C principal hmin hzero hinj' for n in ['effectiveDivisorOfNonzeroSection25Two_injective','nonzeroSection25Two_finite','fullRiemannRochSpace25Two_finite','fullRiemannRochSpace25Two_moduleFinite']})
args['fullRiemannRochSpace25Two']='C principal hmin'
for n,a in args.items():
    body=re.sub(r'\b'+n+r'\b(?!\s*\(D :)',n+' '+a,body)
body=body.replace('instance ','theorem ')
body=body.replace('/-- The actual constant-kernel','include hinj in\n/-- The actual constant-kernel')
body=body.replace('/-- This uses the full grading','include hzero hinj in\n/-- This uses the full grading')
body=body.replace('theorem fullRiemannRochSpace25Two_finite','include hzero hinj in\ntheorem fullRiemannRochSpace25Two_finite')
body=body.replace('/-- Every actual bounded-pole','include hzero hinj in\n/-- Every actual bounded-pole')
# Full type finiteness consumes the immediately preceding parameterized theorem.
body=body.replace('  exact Finite.of_equiv (Option','  letI := nonzeroSection25Two_finite C principal hmin hzero hinj D\n  exact Finite.of_equiv (Option')
body=body.replace(':= by infer_instance',':= by\n  letI := fullRiemannRochSpace25Two_finite C principal hmin hzero hinj D\n  infer_instance')
imports=rr[:0]+'''import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Logic.Equiv.Option
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
'''
out=imports+core+rr+'''
namespace MazurProof.N25F_SectionFiniteness
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
'''+body
out+='\n#print axioms MazurProof.CurveZetaEffectiveDivisors.ClosedPointGrading.effDivOfDegreeFinite\n'
for n in ['NonzeroSection25Two','effectiveDivisorOfNonzeroSection25Two','effectiveDivisorOfNonzeroSection25Two_cast','effectiveDivisorOfNonzeroSection25Two_injective','nonzeroSection25Two_finite','fullRiemannRochSpace25Two_finite','fullRiemannRochSpace25Two_moduleFinite']:
    out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_SectionFiniteness\n'
(r/'SectionFinitenessFamilyCheck.lean').write_text(out)
