from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'SectionPrincipalTransportFamilyInput.lean').read_text()
base=base[:base.index('#print axioms mul_mem_fullRiemannRochSpace25Two')]
base+='end MazurProof.N25F_SectionPrincipalTransport\n'
ded=(r/'CurveDedekindDivisorInput.lean').read_text()
major=(r/'N25F_DedekindPrincipalMajorant.lean').read_text()
imports=[]
for s in [base,ded,major]:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
imports+=['import Mathlib.RingTheory.Localization.FractionRing','import Mathlib.GroupTheory.QuotientGroup.Basic']
base='\n'.join(imports)+'\n'+''.join('\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n' for s in [base,ded,major])
head='''
namespace MazurProof.N25F_AffineNonpositiveRepresentative
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionPrincipalTransport
open N25F_DedekindPrincipalMajorant
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop := ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) := {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem isBoundary_iff (b : Boundary → C.Atom) (a : C.Atom) :
  IsBoundary C b a ↔ ∃ t, b t = a := Iff.rfl
variable (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra (ZMod 2) (FractionRing A)]
variable (principal : Additive ((FractionRing A)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing A)ˣ),
  (h.toMul : FractionRing A) = (f.toMul : FractionRing A) + (g.toMul : FractionRing A) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (hzero : ∀ f : Additive ((FractionRing A)ˣ), C.divisorDegree (principal f) = 0)
variable (boundaryAtom : Boundary → C.Atom)
variable (hbinj : Function.Injective boundaryAtom)
variable (hdegree : ∀ t, C.atomDegree (boundaryAtom t) = 1)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum A)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
variable (B : ℕ)
def basePoleDivisor : C.Divisor :=
  Finsupp.single (boundaryAtom .X) 1 + Finsupp.single (boundaryAtom .YZ) 1 +
    Finsupp.single (boundaryAtom .Z) 2
include hdegree in
theorem basePoleDivisor_degree : C.divisorDegree (basePoleDivisor C boundaryAtom) = 4 := by
  unfold basePoleDivisor
  rw [map_add, map_add]
  simp [ClosedPointGrading.divisorDegree, hdegree]
theorem basePoleDivisor_nonneg : 0 ≤ basePoleDivisor C boundaryAtom := by
  exact add_nonneg (add_nonneg (Finsupp.single_nonneg.mpr (by decide))
    (Finsupp.single_nonneg.mpr (by decide))) (Finsupp.single_nonneg.mpr (by decide))
'''
head=re.sub(r'\bA\b','S',head)
src=(r/'N25F_AffineNonpositiveRepresentative.lean').read_text()
body=src[src.index('private def affineHeightOnePart'):src.index('end MazurProof.N25F_AffineNonpositiveRepresentative')]
body=body.replace('projectivePrincipalDivisor_apply_nonBoundary f A, nonBoundaryPrincipalDivisor_apply','haff f A')
for a,b in [('fullNonBoundaryAtomEquivHeightOne','e'),('fullProjectivePrincipalSubgroup25Two','principal.range'),('projectivePrincipalDivisor_degree_eq_zero','hzero'),('projectivePrincipalDivisor','principal'),('ProjectiveDivisor25Two','C.Divisor'),('fullClosedPointGrading25Two','C'),('FullNonBoundaryAtom25Two','NonBoundary C boundaryAtom'),('WHeightOne','IsDedekindDomain.HeightOneSpectrum S'),('fullBoundaryAtomOfTag_injective','hbinj'),('isFullBoundaryAtom_iff_exists_fullBoundaryTag','isBoundary_iff C boundaryAtom'),('fullBoundaryAtomOfTag','boundaryAtom'),('IsFullBoundaryAtom','IsBoundary C boundaryAtom'),('wPolynomialBasisPoleBound25Two','B'),('basePoleDivisor25Two_degree','basePoleDivisor_degree C boundaryAtom hdegree'),('basePoleDivisor25Two_nonneg','basePoleDivisor_nonneg C boundaryAtom'),('basePoleDivisor25Two','(basePoleDivisor C boundaryAtom)')]:body=body.replace(a,b)
body=re.sub(r'\bW\b','S',body).replace('Kˣ','((FractionRing S)ˣ)')
body=re.sub(r'\bK\b','(FractionRing S)',body)
body=body.replace('((FractionRing S) :=','(K :=')
common='C S principal boundaryAtom e haff'
args={'affineHeightOnePart':'C S boundaryAtom e','exists_principal_affine_majorant25Two':common,'affinePrincipalShift':common,'affineNonpositiveRepresentative25Two':common,'affineNonpositiveRepresentative25Two_nonBoundary':common,'affineNonpositiveRepresentative25Two_degree':'C S principal hzero boundaryAtom e haff','affineNonpositiveRepresentative25Two_classOf':common,'affineNonpositiveRepresentative25Two_finrank':'C S principal hmin boundaryAtom e haff','affineNonpositiveRepresentative25Two_le_basePole_multiple':'C S principal boundaryAtom hbinj e haff B','affineRepresentative_complement_degree':'C S principal hzero boundaryAtom hdegree e haff','fullRiemannRochSpace25Two':'C principal hmin','finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq':'C principal hmin'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('/-- A real nonzero function','include haff in\n/-- A real nonzero function')
body=body.replace('/-- The genuine projective product formula','include hzero in\n/-- The genuine projective product formula')
body=body.replace('/-- After the genuine principal shift','include hbinj in\n/-- After the genuine principal shift')
body=body.replace('/-- Exact degree cost','include hzero hdegree in\n/-- Exact degree cost')
body=body.replace('rw [affineNonpositiveRepresentative25Two '+common+',','rw [affineNonpositiveRepresentative25Two,')
body=body.replace('simpa only [affineHeightOnePart C S boundaryAtom e,','simpa only [affineHeightOnePart,')
body=body.replace('simp only [(basePoleDivisor C boundaryAtom),','simp only [basePoleDivisor,')
out=base+head+body
names=['exists_principal_affine_majorant25Two','affineNonpositiveRepresentative25Two','affineNonpositiveRepresentative25Two_nonBoundary','affineNonpositiveRepresentative25Two_degree','affineNonpositiveRepresentative25Two_classOf','affineNonpositiveRepresentative25Two_finrank','affineNonpositiveRepresentative25Two_le_basePole_multiple','affineRepresentative_complement_degree']
for n in names:out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_AffineNonpositiveRepresentative\n'
(r/'AffineNonpositiveRepresentativeFamilyCheck.lean').write_text(out)
