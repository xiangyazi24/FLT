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

/-- BRIDGE 1 (root dictionary): over an algebraically closed field a root of preΨ' n is the
x-coordinate of a non-2-torsion point on the curve.

NON-CIRCULARITY TRAP (verified 2026-06-24): do NOT prove via the repo's
preΨ'_eval_eq_zero_iff_exists_non_two_torsion / rootPointExists — those depend on
preΨ'_rootSet_card, which depends on preΨ'_separable (the lemma this bridge feeds). Non-circular
path: (a) exists y with W.Equation x y from the alg-closed quadratic polynomial.evalEval x Y
(degree 2 in Y, splits); (b) Ψ₂Sq.eval x nonzero from a general preΨ'_n / Ψ₂Sq coprimality
(NOT yet in repo — only Ψ₃/preΨ₄ vs Ψ₂Sq certs exist), then polynomialY nonzero via the on-curve
relation psi2^2 = Ψ₂Sq. -/
public theorem root_exists_non_two [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ∃ y : K, W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y ≠ 0 := sorry

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

