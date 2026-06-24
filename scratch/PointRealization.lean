import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Point realization: over an algebraically closed field, every x gives a nonsingular point.
Uses Mathlib's `equation_iff_nonsingular` (IsElliptic ⟹ Equation ↔ Nonsingular). -/

open Polynomial WeierstrassCurve

namespace WeierstrassCurve

variable {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- Over an algebraically closed field, the Weierstrass equation at any x has a y-root. -/
theorem exists_equation (x : K) : ∃ y : K, W.toAffine.Equation x y := by
  set qy : K[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) with hqy
  have hdeg : qy.degree = 2 := by rw [hqy]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root qy (by rw [hdeg]; decide)
  rw [Polynomial.IsRoot, hqy] at hy
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C] at hy
  exact ⟨y, by rw [Affine.Equation, Affine.evalEval_polynomial]; linear_combination hy⟩

/-- Over an algebraically closed field with IsElliptic, every x has a NONSINGULAR point. -/
theorem exists_nonsingular (x : K) : ∃ y : K, W.toAffine.Nonsingular x y := by
  obtain ⟨y, hEq⟩ := exists_equation W x
  exact ⟨y, W.toAffine.equation_iff_nonsingular.mp hEq⟩

end WeierstrassCurve
