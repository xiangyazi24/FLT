module

public import scratch.SeamE1_Jet
public import scratch.SeamE1_Dual
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # SEAM1 / E1 — rootwise-core assembly

`preΨ'_deriv_ne_zero_at_root` is assembled from the dual-Taylor engine (A1) + the jet scaffolding,
reduced to TWO precise bridge lemmas: a tractable root-dictionary and the deep raw-coordinate
`[n]`-tangent lemma. Both are named `sorry` (NOT axiom). -/

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

/-- BRIDGE 1', shrunk to the pure coprimality: a root of `preΨ' n` is not a root of `Ψ₂Sq`
(the 2-division polynomial). The avenue-c resultant certs give this for Ψ₃/preΨ₄; the general-`n`
version is the remaining content of bridge 1.

REUSE LEAD (verified 2026-06-24): the ODD-n case is already proven in avenue-c as
`KeystoneCoprimality.preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero` (Ψ₂Sq(x)=0 ⟹ (preΨ n).eval x ≠ 0 for n
odd, needs 4≠0), modulo the preΨ(ℤ)↔preΨ'(ℕ) cast. The EVEN-n case is the missing half — the
analogous even-recurrence argument. -/
public theorem preΨ'_root_Ψ₂Sq_ne (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    W.Ψ₂Sq.eval x ≠ 0 := sorry

public theorem root_exists_non_two [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ∃ y : K, W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y ≠ 0 :=
  nonTwo_of_Ψ₂Sq_ne W (preΨ'_root_Ψ₂Sq_ne W hn hx)

/-- BRIDGE 2 (THE DEEP CRUX: raw multiplication-by-n over k[eps]): a first-order root of preΨ' n
over k[eps] at a non-2-torsion point forces the [n]-tangent coordinate at O to vanish.
Ingredients (DESIGN_SEAM1_CD_assembly.md): lift to affine jet (AffineJet.equation_dual_lift,
psi2-unit via Dual fst nonzero), evaluate raw Jacobian/Projective addXYZ/dblXYZ mult-by-n on the
dual point, land in the O-chart, identify the tangent coordinate with TangentO.nsmul1 n 1. -/
public theorem dual_root_implies_tangent_zero [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y) (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ n (1 : K) = 0 := sorry

/-- ROOTWISE CORE, assembled: a root of `preΨ' n` is a SIMPLE root when `(n:K) ≠ 0`. -/
public theorem preΨ'_deriv_ne_zero_at_root [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  intro hdx
  obtain ⟨y, hcurve, hY⟩ := root_exists_non_two W hn hx
  have hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0 := by
    have h := SeamE1.aeval_dual_eq_zero_of_root_of_deriv_root (f := W.preΨ' n) (x := x) (v := 1)
      hx hdx
    simpa [MultipleRootBridge.xε, Dual.c, Dual.e] using h
  have hzero := dual_root_implies_tangent_zero W hn hcurve hY hrootε
  have hlin : TangentO.nsmul₁ n (1 : K) = (n : K) := by
    simpa using TangentO.nsmul₁_eq_natCast_mul n (1 : K)
  rw [hlin] at hzero
  exact hn hzero

end WeierstrassCurve.SEAM1

