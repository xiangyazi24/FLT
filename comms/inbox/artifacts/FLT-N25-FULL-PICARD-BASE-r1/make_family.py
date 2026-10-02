from pathlib import Path
r=Path(__file__).parent
e=(r/'effective-source.lean').read_text()
p=(r/'picard-source.lean').read_text()
def segment(s,a,b): return s[s.index(a):s.index(b,s.index(a))]
core=segment(e,'structure ClosedPointGrading where','namespace ClosedPointGrading')
core+='namespace ClosedPointGrading\nvariable (C : ClosedPointGrading)\n'
core+=segment(e,'abbrev Atom :=','/-- Every closed point has positive degree.')
core+=segment(p,'abbrev Divisor :=','/-- Regard an effective divisor')
core+=segment(p,'abbrev DivisorClass','/-- An effective divisor of degree')
core+=segment(p,'noncomputable def picDegreeTranslate','/-- A canonical divisor class of degree six')
core+='end ClosedPointGrading\nend MazurProof.CurveZetaEffectiveDivisors\n'
out='''import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors
'''+core+'''
namespace MazurProof.N25F_FullPicardBasePoint
open CurveZetaEffectiveDivisors
variable (C : ClosedPointGrading) {F : Type*} [AddCommGroup F]
variable (principal : F →+ C.Divisor)
variable (hzero : ∀ f : F, C.divisorDegree (principal f) = 0)
variable (x : C.Atom) (hx : C.atomDegree x = 1)

def fullProjectivePrincipalSubgroup25Two : AddSubgroup C.Divisor := principal.range

include hzero in
theorem fullProjectivePrincipalSubgroup25Two_le_degree_ker :
    fullProjectivePrincipalSubgroup25Two C principal ≤ C.divisorDegree.ker := by
  rintro D ⟨f, rfl⟩
  change C.divisorDegree (principal f) = 0
  exact hzero f

def fullProjectiveClassDegree25Two :
    C.DivisorClass (fullProjectivePrincipalSubgroup25Two C principal) →+ ℤ :=
  C.classDegree (fullProjectivePrincipalSubgroup25Two C principal)
    (fullProjectivePrincipalSubgroup25Two_le_degree_ker C principal hzero)

@[simp]
theorem fullProjectiveClassDegree25Two_classOf (D : C.Divisor) :
    fullProjectiveClassDegree25Two C principal hzero
      (C.classOf (fullProjectivePrincipalSubgroup25Two C principal) D) = C.divisorDegree D := rfl

def fullProjectiveBaseClass25Two :
    C.DivisorClass (fullProjectivePrincipalSubgroup25Two C principal) :=
  C.classOf (fullProjectivePrincipalSubgroup25Two C principal) (Finsupp.single x 1)

include hx in
@[simp]
theorem fullProjectiveBaseClass25Two_degree :
    fullProjectiveClassDegree25Two C principal hzero (fullProjectiveBaseClass25Two C principal x) = 1 := by
  classical
  rw [fullProjectiveBaseClass25Two, fullProjectiveClassDegree25Two_classOf]
  simp [ClosedPointGrading.divisorDegree, hx]

include hx in
theorem fullProjectiveClassDegree25Two_surjective :
    Function.Surjective (fullProjectiveClassDegree25Two C principal hzero) := by
  intro n
  refine ⟨n • fullProjectiveBaseClass25Two C principal x, ?_⟩
  rw [map_zsmul, fullProjectiveBaseClass25Two_degree C principal hzero x hx]
  simp

def fullProjectivePicDegreeEquivZero25Two (n : ℤ) :
    C.PicDegree (fullProjectivePrincipalSubgroup25Two C principal)
        (fullProjectivePrincipalSubgroup25Two_le_degree_ker C principal hzero) n ≃
      C.PicDegree (fullProjectivePrincipalSubgroup25Two C principal)
        (fullProjectivePrincipalSubgroup25Two_le_degree_ker C principal hzero) 0 :=
  C.picDegreeEquivZero (fullProjectivePrincipalSubgroup25Two C principal)
    (fullProjectivePrincipalSubgroup25Two_le_degree_ker C principal hzero)
    (fullProjectiveBaseClass25Two C principal x)
    (fullProjectiveBaseClass25Two_degree C principal hzero x hx) n

#print axioms fullProjectiveBaseClass25Two
#print axioms fullProjectiveBaseClass25Two_degree
#print axioms fullProjectiveClassDegree25Two_surjective
#print axioms fullProjectivePicDegreeEquivZero25Two
end MazurProof.N25F_FullPicardBasePoint
'''
(r/'FullPicardBasePointFamilyCheck.lean').write_text(out)
