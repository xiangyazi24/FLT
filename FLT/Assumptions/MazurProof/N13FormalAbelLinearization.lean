import FLT.Assumptions.MazurProof.N13GoodModelTwo
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The integral linearization of an N13 Abel chart

The two integral points `(0,0)` and `(-1,0)` reduce to points with distinct
`x`-coordinates.  Their degree-two sum is therefore away from the canonical
hyperelliptic pencil.  In generalized Mumford coordinates its base
polynomial is `X² + X`, and the linearized curve relation has determinant
`-1`.

This file proves the polynomial identities behind that unit Jacobian over an
arbitrary nontrivial commutative ring.  No point or divisor enumeration is
used.
-/

open Polynomial

namespace MazurProof.N13FormalAbelLinearization

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The monic polynomial of the base divisor `(0,0)+(-1,0)`. -/
def uBase : R[X] :=
  X ^ 2 + X

/-- The coefficient of `Y` in the good generalized equation. -/
def hPoly : R[X] :=
  X ^ 3 + X + 1

theorem uBase_monic : (uBase : R[X]).Monic := by
  unfold uBase
  (monicity; norm_num)

theorem uBase_natDegree [Nontrivial R] :
    (uBase : R[X]).natDegree = 2 := by
  unfold uBase
  (compute_degree; norm_num)

/-- The two selected points lie on the integral generalized model. -/
theorem base_points_on_curve :
    N13GoodModelTwo.AffineEquation (0 : R) 0 ∧
      N13GoodModelTwo.AffineEquation (-1 : R) 0 := by
  constructor
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
    ring

/-- The `Y`-derivatives at the two base points are the units `1` and `-1`. -/
theorem base_derivativeY :
    N13GoodModelTwo.affineDerivativeY (0 : R) 0 = 1 ∧
      N13GoodModelTwo.affineDerivativeY (-1 : R) 0 = -1 := by
  constructor
  · simp [N13GoodModelTwo.affineDerivativeY,
      N13GoodModelTwo.h]
  · simp [N13GoodModelTwo.affineDerivativeY,
      N13GoodModelTwo.h]
    ring

private theorem linear_remainder_degree_lt
    [Nontrivial R]
    (a b : R) :
    (C a * X + C b).degree < (uBase : R[X]).degree := by
  rw [degree_eq_natDegree uBase_monic.ne_zero, uBase_natDegree]
  (compute_degree; norm_num)

/-- Reduction of `h` modulo the base divisor polynomial. -/
theorem hPoly_mod_uBase [Nontrivial R] :
    (hPoly : R[X]) %ₘ uBase = 2 * X + 1 := by
  calc
    (hPoly : R[X]) %ₘ uBase =
        (2 * X + 1 : R[X]) %ₘ uBase := by
      apply modByMonic_eq_of_dvd_sub uBase_monic
      refine ⟨X - 1, ?_⟩
      simp only [hPoly, uBase]
      ring
    _ = 2 * X + 1 := by
      apply (modByMonic_eq_self_iff uBase_monic).2
      have huDegree : (uBase : R[X]).degree = 2 := by
        rw [degree_eq_natDegree uBase_monic.ne_zero, uBase_natDegree]
        norm_num
      rw [huDegree]
      (compute_degree; norm_num)

/-- A linear polynomial used for the nearby generalized Mumford graph. -/
def vLinear (c d : R) : R[X] :=
  C c * X + C d

/-- Exact linearized remainder of the generalized Mumford relation at the
base divisor. -/
theorem neg_h_mul_linear_mod [Nontrivial R]
    (c d : R) :
    (-(hPoly * vLinear c d) : R[X]) %ₘ uBase =
      C (c - 2 * d) * X + C (-d) := by
  calc
    (-(hPoly * vLinear c d) : R[X]) %ₘ uBase =
        (C (c - 2 * d) * X + C (-d)) %ₘ uBase := by
      apply modByMonic_eq_of_dvd_sub uBase_monic
      refine
        ⟨-C c * X ^ 2 + C (c - d) * X + C (d - 2 * c), ?_⟩
      simp [hPoly, vLinear, uBase, C_ofNat]
      ring
    _ = C (c - 2 * d) * X + C (-d) := by
      apply (modByMonic_eq_self_iff uBase_monic).2
      exact linear_remainder_degree_lt (c - 2 * d) (-d)

/-- Jacobian of the two remainder coefficients with respect to the two
coefficients of `v`. -/
def remainderLinearization : Matrix (Fin 2) (Fin 2) R :=
  !![1, -2; 0, -1]

@[simp] theorem remainderLinearization_det :
    (remainderLinearization : Matrix (Fin 2) (Fin 2) R).det = -1 := by
  rw [Matrix.det_fin_two]
  simp [remainderLinearization]

/-- The linearization is its own inverse. -/
theorem remainderLinearization_mul_self :
    (remainderLinearization : Matrix (Fin 2) (Fin 2) R) *
        remainderLinearization = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [remainderLinearization, Matrix.mul_apply, Fin.sum_univ_two]

theorem remainderLinearization_isUnit :
    IsUnit
      (remainderLinearization :
        Matrix (Fin 2) (Fin 2) R) :=
  ⟨⟨remainderLinearization, remainderLinearization,
    remainderLinearization_mul_self,
    remainderLinearization_mul_self⟩, rfl⟩

end

end MazurProof.N13FormalAbelLinearization
