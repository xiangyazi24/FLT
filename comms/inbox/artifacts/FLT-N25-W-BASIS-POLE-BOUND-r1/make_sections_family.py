from pathlib import Path
import re
r=Path(__file__).parent
rr=(r/'RiemannRochSpaceFamilyInput.lean').read_text()
rr=rr[:rr.index('#print axioms')]+'end MazurProof.N25F_RiemannRochSpace\n'
snips=[rr,(r/'CurveDedekindDivisorInput.lean').read_text(),(r/'PrincipalDivisorCoefficientInput.lean').read_text(),(r/'PrincipalDivisorRegularInput.lean').read_text()]
imports=[]
for s in snips:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
imports+=['import Mathlib.LinearAlgebra.Dimension.Free','import Mathlib.RingTheory.Localization.FractionRing']
base='\n'.join(imports)+'\n'+''.join('\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n' for s in snips)
head='''
namespace MazurProof.N25F_WBasisPoleSections
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop :=
  ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) :=
  {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem isBoundary_iff (b : Boundary → C.Atom) (a : C.Atom) :
  IsBoundary C b a ↔ ∃ t, b t = a := Iff.rfl
theorem boundary_isBoundary (b : Boundary → C.Atom) (t : Boundary) :
  IsBoundary C b (b t) := ⟨t, rfl⟩
variable (A : Type*) [CommRing A] [IsDedekindDomain A]
  [Algebra (Polynomial (ZMod 2)) A] [Algebra (ZMod 2) (FractionRing A)]
variable (principal : Additive ((FractionRing A)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing A)ˣ),
  (h.toMul : FractionRing A) = (f.toMul : FractionRing A) + (g.toMul : FractionRing A) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (hbinj : Function.Injective boundaryAtom)
variable (hdegree : ∀ t, C.atomDegree (boundaryAtom t) = 1)
variable (xOrder yzOrder zOrder : Additive ((FractionRing A)ˣ) →+ ℤ)
variable (hxcoeff : ∀ f, principal f (boundaryAtom .X) = xOrder f)
variable (hyzcoeff : ∀ f, principal f (boundaryAtom .YZ) = yzOrder f)
variable (hzcoeff : ∀ f, principal f (boundaryAtom .Z) = zOrder f)
variable (prime : NonBoundary C boundaryAtom → IsDedekindDomain.HeightOneSpectrum A)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (prime a))
variable (basis : Module.Basis (Fin 4) (Polynomial (ZMod 2)) A)
def basisFunction (i : Fin 4) : Additive ((FractionRing A)ˣ) :=
  Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) (basis i))
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr (basis.ne_zero i)))
variable (B : ℕ)
variable (hbounded : ∀ i, -(B : ℤ) ≤ xOrder (basisFunction A basis i) ∧
  -(B : ℤ) ≤ yzOrder (basisFunction A basis i) ∧
  -(2 * (B : ℤ)) ≤ zOrder (basisFunction A basis i))
'''
src=(r/'N25F_WBasisPoleSections.lean').read_text()
body=src[src.index('/-- The actual pole-weight'):src.index('end MazurProof.N25F_WBasisPoleSections')]
body=body.replace('projectivePrincipalDivisor_apply_nonBoundary f B, nonBoundaryPrincipalDivisor_apply','haff f B')
for a,b in [('projectivePrincipalDivisor_apply_X','hxcoeff'),('projectivePrincipalDivisor_apply_YZ','hyzcoeff'),('projectivePrincipalDivisor_apply_Z','hzcoeff'),('fullBoundaryAtomOfTag_injective','hbinj'),('fullBoundaryAtomOfTag_isFullBoundaryAtom','boundary_isBoundary C boundaryAtom'),('isFullBoundaryAtom_iff_exists_fullBoundaryTag','isBoundary_iff C boundaryAtom'),('FullBoundaryTag25Two','Boundary'),('fullBoundaryAtomOfTag','boundaryAtom'),('FullNonBoundaryAtom25Two','NonBoundary C boundaryAtom'),('IsFullBoundaryAtom','IsBoundary C boundaryAtom'),('fullClosedPointGrading25Two','C'),('ProjectiveDivisor25Two','C.Divisor'),('xBoundaryOrder','xOrder'),('yzBoundaryOrder','yzOrder'),('zBoundaryOrder','zOrder'),('wPolynomialBasisPoleBound25Two','B'),('wPolynomialBasis_boundary_orders_bounded','hbounded'),('wPolynomialBasis25Two_ne_zero','basis.ne_zero'),('wPolynomialBasis25Two','basis'),('wPolynomialBasisFunction25Two','basisFunction A basis')]:body=body.replace(a,b)
body=re.sub(r'\bW\b','A',body).replace('Kˣ','((FractionRing A)ˣ)')
body=re.sub(r'\bK\b','(FractionRing A)',body)
args={'basePoleDivisor25Two':'C boundaryAtom','basePoleDivisor25Two_degree':'C boundaryAtom hdegree','basePoleDivisor_apply_boundary':'C boundaryAtom hbinj','basePoleDivisor_apply_nonBoundary':'C boundaryAtom','fullRiemannRochSpace25Two':'C principal hmin','regular_function_mem_basePole_space':'C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff','wPolynomialBasis_mem_uniform_section_space':'C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff basis B hbounded'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('simp [basePoleDivisor25Two C boundaryAtom, ClosedPointGrading.divisorDegree]','simp [basePoleDivisor25Two, ClosedPointGrading.divisorDegree, hdegree]')
body=body.replace('simp [basePoleDivisor25Two C boundaryAtom,','simp [basePoleDivisor25Two,')
body=body.replace('C.divisorDegree basePoleDivisor25Two C boundaryAtom','C.divisorDegree (basePoleDivisor25Two C boundaryAtom)')
body=body.replace('unfold basePoleDivisor25Two C boundaryAtom','unfold basePoleDivisor25Two')
body=body.replace('simp [ClosedPointGrading.divisorDegree]','simp [ClosedPointGrading.divisorDegree, hdegree]')
body=body.replace('theorem basePoleDivisor25Two_degree','include hdegree in\ntheorem basePoleDivisor25Two_degree')
body=body.replace('private theorem basePoleDivisor_apply_boundary','include hbinj in\nprivate theorem basePoleDivisor_apply_boundary')
body=body.replace('/-- An actual regular A function','include hbinj hxcoeff hyzcoeff hzcoeff haff in\nomit [Algebra (Polynomial (ZMod 2)) A] in\n/-- An actual regular A function')
body=body.replace('/-- Every element of the one fixed','include hbinj hxcoeff hyzcoeff hzcoeff haff hbounded in\n/-- Every element of the one fixed')
out=base+head+body
for n in ['basePoleDivisor25Two','basePoleDivisor25Two_degree','regular_function_mem_basePole_space','wPolynomialBasis_mem_uniform_section_space']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WBasisPoleSections\n'
(r/'WBasisPoleSectionsFamilyCheck.lean').write_text(out)
