import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors
structure ClosedPointGrading where
  Closed : ℕ → Type*
  finite_closed : ∀ d, Finite (Closed d)
  empty_degree_zero : IsEmpty (Closed 0)

namespace ClosedPointGrading
variable (C : ClosedPointGrading)
abbrev Atom := Σ d : ℕ, C.Closed d

/-- The residue degree of a graded closed point. -/
def atomDegree (x : C.Atom) : ℕ := x.1

abbrev Divisor := C.Atom →₀ ℤ

/-- The integer degree of a signed divisor is the sum of each multiplicity
times the residue degree of its closed point. -/
def divisorDegree : C.Divisor →+ ℤ where
  toFun D := D.sum fun x m => m * (C.atomDegree x : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    exact Finsupp.sum_add_index' (by simp) (by
      intro x a b
      simp only [add_mul])

abbrev DivisorClass (Principal : AddSubgroup C.Divisor) :=
  C.Divisor ⧸ Principal

/-- The class of a signed divisor in the quotient by principal divisors. -/
noncomputable def classOf (Principal : AddSubgroup C.Divisor) :
    C.Divisor →+ C.DivisorClass Principal :=
  QuotientAddGroup.mk' Principal

/-- Divisor degree descends through principal equivalence once every
principal divisor has degree zero. -/
noncomputable def classDegree (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker) :
    C.DivisorClass Principal →+ ℤ :=
  QuotientAddGroup.lift Principal C.divisorDegree hPrincipal

@[simp]
theorem classDegree_classOf
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (D : C.Divisor) :
    C.classDegree Principal hPrincipal (C.classOf Principal D) =
      C.divisorDegree D := by
  rfl

/-- The degree-`n` Picard fibre is the subtype of divisor classes whose
descended degree is exactly `n`.  It is not an unrelated finite type standing
in for the geometric Picard torsor. -/
def PicDegree (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker) (n : ℤ) :=
  {c : C.DivisorClass Principal // C.classDegree Principal hPrincipal c = n}

noncomputable def picDegreeTranslate
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    {a b : ℤ}
    (t : C.DivisorClass Principal)
    (ht : C.classDegree Principal hPrincipal t = b - a) :
    C.PicDegree Principal hPrincipal a ≃
      C.PicDegree Principal hPrincipal b where
  toFun c := ⟨c.1 + t, by
    rw [map_add, c.2, ht]
    omega⟩
  invFun c := ⟨c.1 - t, by
    rw [map_sub, c.2, ht]
    omega⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- A degree-one divisor class supplies compatible base points in every
Picard degree.  Translating a degree-`n` class by `-n` copies of that base
class identifies `Pic^n` with the degree-zero Picard group. -/
noncomputable def picDegreeEquivZero
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (base : C.DivisorClass Principal)
    (hbase : C.classDegree Principal hPrincipal base = 1)
    (n : ℤ) :
    C.PicDegree Principal hPrincipal n ≃
      C.PicDegree Principal hPrincipal 0 :=
  C.picDegreeTranslate Principal hPrincipal ((-n) • base) (by
    rw [map_zsmul, hbase]
    simp)

end ClosedPointGrading
end MazurProof.CurveZetaEffectiveDivisors

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
