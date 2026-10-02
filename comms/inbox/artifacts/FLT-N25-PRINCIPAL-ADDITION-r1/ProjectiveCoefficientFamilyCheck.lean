import Mathlib.Data.Finsupp.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace CoefficientCheck
inductive Boundary | X | YZ | Z

variable {A N C : Type*} (e : A ≃ Sum Boundary N) (q : N ≃ C)

def splitAtoms : (A →₀ ℤ) ≃+ ((Boundary →₀ ℤ) × (N →₀ ℤ)) :=
  (Finsupp.domCongr e).trans Finsupp.sumFinsuppAddEquivProdFinsupp

def chartEquiv : (N →₀ ℤ) ≃+ (C →₀ ℤ) := Finsupp.domCongr q

def splitChart : (A →₀ ℤ) ≃+ ((Boundary →₀ ℤ) × (C →₀ ℤ)) :=
  (splitAtoms e).trans ((AddEquiv.refl (Boundary →₀ ℤ)).prodCongr (chartEquiv q))

def boundaryTriple : (Boundary →₀ ℤ) ≃+ (ℤ × (ℤ × ℤ)) where
  toFun D := (D .X, (D .YZ, D .Z))
  invFun c := Finsupp.single .X c.1 + Finsupp.single .YZ c.2.1 + Finsupp.single .Z c.2.2
  left_inv D := by ext t; cases t <;> simp
  right_inv c := by rcases c with ⟨x,y,z⟩; simp
  map_add' D E := by rfl

def splitTriple : (A →₀ ℤ) ≃+ ((ℤ × (ℤ × ℤ)) × (C →₀ ℤ)) :=
  (splitChart e q).trans (boundaryTriple.prodCongr (AddEquiv.refl (C →₀ ℤ)))

variable (D : A →₀ ℤ) (x y z : ℤ) (n : N →₀ ℤ)
variable (hsplit : splitTriple e q D = ((x,(y,z)),chartEquiv q n))

include hsplit in
theorem coefficient_X : D (e.symm (.inl .X)) = x :=
  congrArg (fun D => D.1.1) hsplit

include hsplit in
theorem coefficient_YZ : D (e.symm (.inl .YZ)) = y :=
  congrArg (fun D => D.1.2.1) hsplit

include hsplit in
theorem coefficient_Z : D (e.symm (.inl .Z)) = z :=
  congrArg (fun D => D.1.2.2) hsplit

include hsplit in
theorem coefficient_nonBoundary (a : N) : D (e.symm (.inr a)) = n a := by
  have h := congrArg (fun D => ((chartEquiv q).symm D.2) a) hsplit
  change ((chartEquiv q).symm (chartEquiv q ((splitAtoms e D).2))) a =
    ((chartEquiv q).symm (chartEquiv q n)) a at h
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h
  exact h

#print axioms coefficient_X
#print axioms coefficient_YZ
#print axioms coefficient_Z
#print axioms coefficient_nonBoundary
end CoefficientCheck
