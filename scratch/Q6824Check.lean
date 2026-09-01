import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Polynomial.Quotient

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Q6824Check

open Polynomial

abbrev R := Polynomial ℚ

abbrev p : Ideal R := Ideal.span ({Polynomial.X} : Set R)

instance p_isMaximal : p.IsMaximal := by
  dsimp [p, R]
  simpa using
    (PrincipalIdealRing.isMaximal_of_irreducible
      (Polynomial.irreducible_X_sub_C (0 : ℚ)))

/-- The residue field of `ℚ[X]` at `(X)` is canonically `ℚ`. -/
noncomputable def baseResidueAlgEquiv : (R ⧸ p) ≃ₐ[ℚ] ℚ :=
  (Ideal.quotientEquivAlgOfEq ℚ (by simp [R, p])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℚ))

attribute [local instance] Ideal.Quotient.field

variable {S : Type*} [CommRing S]
variable [Algebra R S] [Algebra ℚ S] [IsScalarTower ℚ R S]
variable (P : Ideal S) [P.IsMaximal] [P.LiesOver p]

/-- Any maximal point above `(X)` whose residue field is `ℚ` has inertia degree one. -/
theorem inertiaDeg_eq_one_of_residueAlgEquiv
    (e : (S ⧸ P) ≃ₐ[ℚ] ℚ) :
    p.inertiaDeg P = 1 := by
  rw [Ideal.inertiaDeg_algebraMap]
  have hp : Module.finrank ℚ (R ⧸ p) = 1 := by
    simpa using baseResidueAlgEquiv.toLinearEquiv.finrank_eq
  have hP : Module.finrank ℚ (S ⧸ P) = 1 := by
    simpa using e.toLinearEquiv.finrank_eq
  have h := Module.finrank_mul_finrank ℚ (R ⧸ p) (S ⧸ P)
  rw [hp, hP] at h
  simpa using h

end Q6824Check
