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

section EvaluationAlgebra

variable (S : Type*) [CommRing S] [Algebra ℚ S]
variable (u : S)

example : True := by
  letI : Algebra R S :=
    (Polynomial.eval₂RingHom (algebraMap ℚ S) u).toAlgebra
  have hX : algebraMap R S Polynomial.X = u := by
    rfl
  letI : IsScalarTower ℚ R S :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext q
      simp [RingHom.algebraMap_toAlgebra]
  have _ : IsScalarTower ℚ R S := inferInstance
  exact True.intro

end EvaluationAlgebra

variable {S : Type*} [CommRing S]
variable [Algebra R S] [Algebra ℚ S] [IsScalarTower ℚ R S]

/-- A maximal ideal containing the image of `X` lies over `(X)`. -/
theorem liesOver_span_X_of_mem
    (u : S) (huX : algebraMap R S Polynomial.X = u)
    (P : Ideal S) [P.IsMaximal] (hu : u ∈ P) :
    P.LiesOver p := by
  rw [Ideal.liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le p_isMaximal
    (Ideal.comap_ne_top _ (inferInstance : P.IsMaximal).ne_top) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, huX]
  exact hu

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
