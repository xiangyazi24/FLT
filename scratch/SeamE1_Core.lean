module

public import scratch.SeamE1_Jet
public import scratch.SeamE1_Dual
public import scratch.SeamE1_DualUnit
public import scratch.SeamE1_FormalNsmul
public import scratch.SeamE1_SeparabilityCore
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import scratch.Bridge1Even

/-! # SEAM1 / E1 — rootwise-core assembly

`preΨ'_deriv_ne_zero_at_root` is assembled from the separability core
(`SeamE1_SeparabilityCore.lean`) which proves rootwise separability of
`preΨ' n` using Bézout certificates + EDS recurrence descent.

The dual-number machinery (A1 + jet scaffolding) is retained for the
formal bridge decomposition in `SeamE1_FormalBridge.lean`. -/

open Polynomial

namespace WeierstrassCurve.SEAM1

variable {K : Type*} [Field K]

/-- MECHANICAL (proven): over an algebraically closed field, `Ψ₂Sq(x) ≠ 0` gives a curve point
over `x` with nonzero `ψ₂` (non-2-torsion). `∃ y` is the alg-closed quadratic root; `ψ₂ ≠ 0` is
`ψ₂² = Ψ₂Sq` on the curve. -/
public theorem nonTwo_of_Ψ₂Sq_ne [IsAlgClosed K] (W : WeierstrassCurve K) {x : K}
    (hΨ : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ y, W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y ≠ 0 := by
  set qy : K[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    with hqy
  have hdeg : qy.degree = 2 := by rw [hqy]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root qy (by rw [hdeg]; decide)
  rw [Polynomial.IsRoot, hqy] at hy
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C] at hy
  have hEq : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial]
    linear_combination hy
  refine ⟨y, hEq, ?_⟩
  intro h0
  apply hΨ
  have hEq' := hEq
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial] at hEq'
  have hsq : (W.toAffine.polynomialY.evalEval x y) ^ 2 = W.Ψ₂Sq.eval x := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Ψ₂Sq]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hEq'
  rw [h0] at hsq
  simpa using hsq.symm

/-- BRIDGE 1': a root of `preΨ' n` is not a root of `Ψ₂Sq`. -/
public theorem preΨ'_root_Ψ₂Sq_ne (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    W.Ψ₂Sq.eval x ≠ 0 := WeierstrassCurve.preΨ'_root_Ψ₂Sq_ne' W hn hx

public theorem root_exists_non_two [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ∃ y : K, W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y ≠ 0 :=
  nonTwo_of_Ψ₂Sq_ne W (preΨ'_root_Ψ₂Sq_ne W hn hx)

/-- BRIDGE 2: a dual root of preΨ' n forces (n:K) = 0.

The proof extracts value and derivative roots from the dual root, then applies
the rootwise separability theorem from `SeamE1_SeparabilityCore`. -/
public theorem dual_root_implies_tangent_zero [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y) (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ n (1 : K) = 0 := by
  exfalso
  -- Extract value root and derivative root from the dual root
  have heval := SeamE1.eval_dualNumber (W.preΨ' n) x 1
  simp only [MultipleRootBridge.xε, Dual.c, Dual.e] at hrootε
  rw [hrootε] at heval
  rw [TrivSqZeroExt.ext_iff] at heval
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, add_zero, zero_add] at heval
  have hroot : (W.preΨ' n).IsRoot x := heval.1.symm
  have hderiv : (derivative (W.preΨ' n)).IsRoot x := by
    rw [IsRoot]; simpa [one_mul] using heval.2.symm
  -- Apply the separability theorem: the value root and derivative root are contradictory
  exact (SeparabilityCore.preΨ'_deriv_ne_zero_at_root_general W hn hroot) hderiv

/-- ROOTWISE CORE, assembled: a root of `preΨ' n` is a SIMPLE root when `(n:K) ≠ 0`. -/
public theorem preΨ'_deriv_ne_zero_at_root [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x :=
  SeparabilityCore.preΨ'_deriv_ne_zero_at_root_general W hn hx

end WeierstrassCurve.SEAM1
