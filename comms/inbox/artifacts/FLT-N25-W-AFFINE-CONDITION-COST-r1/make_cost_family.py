from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'WRegularSectionLiftFamilyCheck.lean').read_text()
base=base[:base.index('#print axioms existsUnique_wChart_lift_of_mem_basePole_space')]
base+='end MazurProof.N25F_WRegularSectionLift\n'
degree=(r/'accepted-N25F_DedekindFactorDegree.lean').read_text()
imports=[]
for s in [base,degree]:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
imports+=['import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas','import Mathlib.RingTheory.Jacobson.Artinian','import Mathlib.RingTheory.KrullDimension.Zero']
base='\n'.join(imports)+'\n'+''.join('\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n' for s in [base,degree])
head='''
namespace MazurProof.N25F_WAffineConditionCost
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_WRegularSectionLift N25F_DedekindOrderMembership
open scoped nonZeroDivisors BigOperators
variable (C : ClosedPointGrading)
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (ZMod 2) S]
  [Algebra.FiniteType (ZMod 2) S]
variable (principal : Additive ((FractionRing S)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing S)ˣ),
  (h.toMul : FractionRing S) = (f.toMul : FractionRing S) + (g.toMul : FractionRing S) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum S)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
variable (hfinite : ∀ n : ℕ, Module.Finite (ZMod 2)
  (fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))))
'''
src=(r/'N25F_WAffineConditionCost.lean').read_text()
body=src[src.index('/-- The real affine conditions'):src.index('end MazurProof.N25F_WAffineConditionCost')]
body=body.replace('basePoleDivisor25Two','(basePoleDivisor C boundaryAtom)').replace('WHeightOne','IsDedekindDomain.HeightOneSpectrum S')
body=re.sub(r'\bW\b','S',body).replace('W⁰','S⁰')
body=re.sub(r'\bK\b','(FractionRing S)',body)
common='C S principal hmin boundaryAtom e haff'
args={'fullRiemannRochSpace25Two':'C principal hmin','wRegularSectionLift25Two':common,'wRegularSectionLiftLinearMap25Two':common,'algebraMap_wRegularSectionLift25Two':common,'wSectionIdealQuotient25Two':common,'wSectionIdealQuotient25Two_eq_zero_iff':common,'wSectionIdealQuotient25Two_eq_zero_iff_orders':common,'wIdealQuotient_finite':'S','finrank_basePole_le_kernel_add_ideal_quotient':common+' hfinite','finrank_basePole_le_kernel_add_weighted_affine_cost':common+' hfinite'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('/-- Imposing the actual affine ideal','include hfinite in\n/-- Imposing the actual affine ideal')
body=body.replace('/-- The affine condition cost','include hfinite in\n/-- The affine condition cost')
body=body.replace('  have hdim :=','  letI := hfinite n\n  have hdim :=')
out=base+head+body
for n in ['wSectionIdealQuotient25Two','wSectionIdealQuotient25Two_eq_zero_iff','wSectionIdealQuotient25Two_eq_zero_iff_orders','finrank_basePole_le_kernel_add_ideal_quotient','finrank_basePole_le_kernel_add_weighted_affine_cost']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WAffineConditionCost\n'
(r/'WAffineConditionCostFamilyCheck.lean').write_text(out)
