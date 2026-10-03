from pathlib import Path
import re
r=Path(__file__).parent
old=Path('/workspace/shared/flt-n25-x-filtration')
base=(old/'SectionFinitenessFamilyInput.lean').read_text().split('#print axioms MazurProof.CurveZetaEffectiveDivisors.')[0]+'end MazurProof.N25F_SectionFiniteness\n'
bi=(old/'BinaryResidueCancellationCheck.lean').read_text().split('#print axioms')[0]
imports=[]
for s in [base,bi]:
 for l in s.splitlines():
  if l.startswith('import ') and l not in imports: imports.append(l)
imports.append('import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas')
def strip(s):return '\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n'
src=(r/'N25F_BoundarySectionFiltration.lean').read_text()
body=src[src.index('private theorem unit_mk0_eq'):src.index('end MazurProof.N25F_BoundarySectionFiltration')]
body=body.replace('(t : FullBoundaryTag25Two)', '').replace('(fullBoundaryAtomOfTag t)','P').replace(' D t',' D').replace(' t a b',' a b')
body=body.replace('ProjectiveDivisor25Two','C.Divisor').replace('projectivePrincipalDivisor','principal')
body=body.replace('K','L').replace('fullBoundaryAtomOfTag t','P').replace('/--','/-')
names=re.findall(r'^theorem (\w+)',body,re.M)
args={'fullRiemannRochSpace25Two':'C principal hmin', 'fullRiemannRochSpace25Two_mono':'C principal hmin'}
for n in names:args[n]='C principal hmin P'+(' hcancel' if n in names[3:] else '')+(' hzero hinj' if n in names[4:] else '')
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 body=body.replace('theorem '+n+' '+a,'theorem '+n)
body=body.replace('boundary_principal_sub_gt_of_eq a b','hcancel a b')
body=body.replace('| zero => simp only [Nat.cast_zero, zero_smul, sub_zero, add_zero, le_refl]', '| zero => simp')
body=body.replace('  by_cases hle :','  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj (D - Finsupp.single P 1)\n  by_cases hle :')
head='''
namespace MazurProof.N25F_BoundarySectionFiltration
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness N25F_BinaryResidueCancellation
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (C : ClosedPointGrading) (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ, (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
 min (principal f A) (principal g A) ≤ principal h A)
variable (P : C.Atom)
variable (hcancel : ∀ a b : L, ∀ (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b),
 principal (Additive.ofMul (Units.mk0 a ha)) P = principal (Additive.ofMul (Units.mk0 b hb)) P →
 principal (Additive.ofMul (Units.mk0 b hb)) P < principal (Additive.ofMul (Units.mk0 (a-b) (sub_ne_zero.mpr hab))) P)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
theorem fullRiemannRochSpace25Two_mono {D E : C.Divisor} (h : D ≤ E) :
 fullRiemannRochSpace25Two C principal hmin D ≤ fullRiemannRochSpace25Two C principal hmin E := by
 intro f hf
 rcases hf with hz | ⟨hn,hf⟩
 · exact Or.inl hz
 · refine Or.inr ⟨hn, ?_⟩
   intro A
   have ha := h A
   have hb := hf A
   omega
'''
# Force intended proof inputs into theorem binder elaboration.
for n in names[3:]: body=body.replace('theorem '+n,'include hcancel'+(' hzero hinj' if n in names[4:] else '')+' in\ntheorem '+n)
out='\n'.join(imports)+'\n'+strip(base)+strip(bi)+head+body
out+=(r/'BoundaryDVRAssembly.lean.part').read_text()
out+='\n'.join('#print axioms '+n for n in names)+'\nend MazurProof.N25F_BoundarySectionFiltration\n'
(r/'BoundarySectionFiltrationFamilyCheck.lean').write_text(out)
