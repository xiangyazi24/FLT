import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.AlgebraTower

/-! Polynomial monomials times a finite polynomial-module basis form the
required independent windows, without an assumed dimension formula. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_PolynomialBasisWindow

/-- The first n+1 monomials times four polynomial-basis vectors are independent. -/
theorem polynomial_basis_window_linearIndependent {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra (Polynomial k) A]
    [IsScalarTower k (Polynomial k) A]
    (b : Module.Basis (Fin 4) (Polynomial k) A) (n : ℕ) :
    LinearIndependent k
      (fun ij : Fin 4 × Fin (n + 1) => ((Polynomial.X : Polynomial k) ^ ij.2.val) • b ij.1) := by
  let e : Fin 4 × Fin (n + 1) → Fin 4 × ℕ := fun ij => (ij.1, ij.2.val)
  have he : Function.Injective e := by
    intro i j h
    have h1 : i.1 = j.1 := congrArg (fun p : Fin 4 × ℕ => p.1) h
    have h2 : i.2.val = j.2.val := congrArg (fun p : Fin 4 × ℕ => p.2) h
    exact Prod.ext h1 (Fin.ext h2)
  have h := ((Polynomial.basisMonomials k).smulTower' b).linearIndependent.comp e he
  simpa only [Function.comp_def, e, Module.Basis.smulTower'_apply,
    Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow] using h

end MazurProof.N25F_PolynomialBasisWindow
