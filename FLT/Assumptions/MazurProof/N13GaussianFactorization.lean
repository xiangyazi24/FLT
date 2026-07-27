import FLT.Assumptions.MazurProof.N13Mumford
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Gaussian factorization of the N13 sextic

The N13 sextic is the norm of a cubic over the Gaussian rationals.  This is
the structural input for a Gaussian two-descent.
-/

open Polynomial

namespace MazurProof.N13GaussianFactorization

noncomputable section

/-- The Gaussian rational algebra `ℚ[i]`, with `i² = -1`. -/
abbrev GaussianQ := QuadraticAlgebra ℚ (-1) 0

/-- The Gaussian unit `i`. -/
def gaussianI : GaussianQ := ⟨0, 1⟩

@[simp] theorem gaussianI_sq : gaussianI * gaussianI = -1 := by
  ext <;> simp [gaussianI, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The real cubic in the Gaussian factor. -/
def A : ℚ[X] := X ^ 3 + 2 * X ^ 2 - X - 1

/-- The imaginary quadratic part in the Gaussian factor. -/
def B : ℚ[X] := 2 * X * (X + 1)

/-- The N13 sextic is the sum of the two displayed squares. -/
theorem f_eq_sum_squares : N13Mumford.f ℚ = A ^ 2 + B ^ 2 := by
  simp only [N13Mumford.f, A, B]
  ring

theorem f_eval_eq_sum_squares (x : ℚ) :
    (N13Mumford.f ℚ).eval x = (A.eval x) ^ 2 + (B.eval x) ^ 2 := by
  rw [f_eq_sum_squares]
  simp only [eval_add, eval_pow]

/-- The cubic Gaussian factor evaluated at a rational parameter. -/
def gaussianFactor (x : ℚ) : GaussianQ :=
  ⟨A.eval x, B.eval x⟩

/-- Its Gaussian conjugate. -/
def gaussianConjugateFactor (x : ℚ) : GaussianQ :=
  ⟨A.eval x, -B.eval x⟩

theorem star_gaussianFactor (x : ℚ) :
    star (gaussianFactor x) = gaussianConjugateFactor x := by
  ext <;> simp [gaussianFactor, gaussianConjugateFactor,
    QuadraticAlgebra.star_mk]

/-- The two Gaussian factors multiply to the N13 sextic. -/
theorem gaussian_factor_mul_conjugate (x : ℚ) :
    gaussianFactor x * gaussianConjugateFactor x =
      QuadraticAlgebra.C ((N13Mumford.f ℚ).eval x) := by
  change (⟨A.eval x, B.eval x⟩ : GaussianQ) *
      ⟨A.eval x, -B.eval x⟩ =
    ⟨(N13Mumford.f ℚ).eval x, 0⟩
  have hf := f_eval_eq_sum_squares x
  apply QuadraticAlgebra.ext
  · simp
    rw [hf]
    ring
  · simp
    ring

/-- Equivalently, the sextic is the quadratic-algebra norm of its cubic
Gaussian factor. -/
theorem gaussian_factor_norm (x : ℚ) :
    QuadraticAlgebra.norm (gaussianFactor x) = (N13Mumford.f ℚ).eval x := by
  have hf := f_eval_eq_sum_squares x
  simp only [gaussianFactor, QuadraticAlgebra.norm_def]
  rw [hf]
  ring

end

end MazurProof.N13GaussianFactorization
