import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.AlgebraTower
open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

/-- The monomials form a basis on `R[X]`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`. -/
def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoLinear R)

@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _

end Polynomial
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
    exact Prod.ext (congrArg Prod.fst h) (Fin.ext (congrArg Prod.snd h))
  have h := ((Polynomial.basisMonomials k).smulTower' b).linearIndependent.comp e he
  simpa only [Function.comp_apply, e, Module.Basis.smulTower'_apply,
    Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow] using h

end MazurProof.N25F_PolynomialBasisWindow

#print axioms MazurProof.N25F_PolynomialBasisWindow.polynomial_basis_window_linearIndependent
