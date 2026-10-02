from pathlib import Path
r=Path(__file__).parent
q=r
e=(q/'effective-source.lean').read_text()
p=(q/'picard-source.lean').read_text()
def segment(s,a,b): return s[s.index(a):s.index(b,s.index(a))]
core=segment(e,'structure ClosedPointGrading where','namespace ClosedPointGrading')
core+='namespace ClosedPointGrading\nvariable (C : ClosedPointGrading)\n'
core+=segment(e,'abbrev Atom :=','/-- Every closed point has positive degree.')
core+=segment(p,'abbrev Divisor :=','/-- Regard an effective divisor')
core+='end ClosedPointGrading\nend MazurProof.CurveZetaEffectiveDivisors\n'
src=(r/'N25F_RiemannRochSpace.lean').read_text()
binary=segment(src,'private theorem zmod_two_cases','/-- The actual F2-vector space')
body=segment(src,'/-- The actual F2-vector space','end MazurProof.N25F_RiemannRochSpace')
for a,b in [('projectivePrincipalDivisor_degree_eq_zero','hzero'),('projectivePrincipalDivisor_add_ge_min','hmin'),
 ('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),
 ('fullClosedPointGrading25Two','C'),('CurveField','L')]: body=body.replace(a,b)
body=body.replace('fullRiemannRochSpace25Two D','fullRiemannRochSpace25Two C principal hmin D')
body=body.replace('degree_nonneg_of_nonzero_mem D f hf hne','degree_nonneg_of_nonzero_mem C principal hmin hzero D f hf hne')
body=body.replace('/-- A nonzero bounded-pole function','include hzero in\n/-- A nonzero bounded-pole function')
body=body.replace('/-- The actual Riemann--Roch space','include hzero in\n/-- The actual Riemann--Roch space')
out='''import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors
'''+core+'''
namespace MazurProof.N25F_RiemannRochSpace
open CurveZetaEffectiveDivisors
'''+binary+'''
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
'''+body+'''
#print axioms fullRiemannRochSpace25Two
#print axioms mem_fullRiemannRochSpace25Two
#print axioms degree_nonneg_of_nonzero_mem
#print axioms fullRiemannRochSpace25Two_eq_bot_of_degree_neg
end MazurProof.N25F_RiemannRochSpace
'''
(r/'RiemannRochSpaceFamilyCheck.lean').write_text(out)
