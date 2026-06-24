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

/-- BRIDGE 1 (root dictionary, tractable): over an algebraically closed field a root of `preΨ' n`
is the x-coordinate of a non-2-torsion point on the curve. -/
public theorem root_exists_non_two [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ∃ y : K, W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y ≠ 0 := sorry

/-- BRIDGE 2 (the deep crux: raw multiplication-by-`n` over `k[ε]`): a first-order root of `preΨ' n`
over `k[ε]` at a non-2-torsion point forces the `[n]`-tangent coordinate at `O` to vanish. -/
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

