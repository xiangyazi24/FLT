import Mathlib.GroupTheory.QuotientGroup.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FullPicardDegree
variable {F D : Type*} [AddCommGroup F] [AddCommGroup D]
variable (principal : F →+ D) (degree : D →+ ℤ)
variable (hzero : ∀ f : F, degree (principal f) = 0)

def fullProjectivePrincipalSubgroup25Two : AddSubgroup D := principal.range

include hzero in
theorem fullProjectivePrincipalSubgroup25Two_le_degree_ker :
    fullProjectivePrincipalSubgroup25Two principal ≤ degree.ker := by
  rintro D ⟨f, rfl⟩
  change degree (principal f) = 0
  exact hzero f

def fullProjectiveClassDegree25Two :
    (D ⧸ fullProjectivePrincipalSubgroup25Two principal) →+ ℤ :=
  QuotientAddGroup.lift (fullProjectivePrincipalSubgroup25Two principal) degree
    (fullProjectivePrincipalSubgroup25Two_le_degree_ker principal degree hzero)

@[simp]
theorem fullProjectiveClassDegree25Two_classOf (d : D) :
    fullProjectiveClassDegree25Two principal degree hzero
      (QuotientAddGroup.mk' (fullProjectivePrincipalSubgroup25Two principal) d) =
      degree d := rfl

theorem fullProjectiveClassOf_eq_iff_exists_principal (d e : D) :
    QuotientAddGroup.mk' (fullProjectivePrincipalSubgroup25Two principal) d =
      QuotientAddGroup.mk' (fullProjectivePrincipalSubgroup25Two principal) e ↔
      ∃ f : F, principal f = d - e := by
  change ((d : D ⧸ fullProjectivePrincipalSubgroup25Two principal) = e) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

#print axioms fullProjectivePrincipalSubgroup25Two
#print axioms fullProjectivePrincipalSubgroup25Two_le_degree_ker
#print axioms fullProjectiveClassDegree25Two
#print axioms fullProjectiveClassDegree25Two_classOf
#print axioms fullProjectiveClassOf_eq_iff_exists_principal
end MazurProof.N25F_FullPicardDegree
