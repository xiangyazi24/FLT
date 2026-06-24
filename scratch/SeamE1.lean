module

public import scratch.SeamE1_Algebra
public import scratch.SeamE1_Core
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # SEAM1 / E1 — the separability reduction scaffold

`preΨ'_separable_of_natCast_ne_zero` is reduced (over the algebraic closure, descending via
`separable_map`) to the ROOTWISE CORE `preΨ'_deriv_ne_zero_at_root` (layers B+C+D: the first-order
tangent argument). -/

open Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k]

/-- ROOTWISE CORE (B+C+D, the first-order tangent argument). Over an algebraically closed field,
a root of `preΨ' n` is a SIMPLE root when `(n : K) ≠ 0`. -/
public theorem preΨ'_deriv_ne_zero_at_root {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) : ¬ (derivative (W.preΨ' n)).IsRoot x :=
  SEAM1.preΨ'_deriv_ne_zero_at_root W hn hx

/-- SEAM1: the reduced `n`-division polynomial is separable when `(n : k) ≠ 0`. -/
public theorem preΨ'_separable_of_natCast_ne_zero (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) : (W.preΨ' n).Separable := by
  rw [← separable_map (algebraMap k (AlgebraicClosure k))]
  have hn' : (n : AlgebraicClosure k) ≠ 0 := by
    rw [← map_natCast (algebraMap k (AlgebraicClosure k)) n]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k))).mpr hn
  rw [show (W.preΨ' n).map (algebraMap k (AlgebraicClosure k))
        = (W.map (algebraMap k (AlgebraicClosure k))).preΨ' n from (W.map_preΨ' (algebraMap k (AlgebraicClosure k)) n).symm]
  refine SeamE1.separable_of_deriv_ne_zero_at_roots ((W.map (algebraMap k (AlgebraicClosure k))).preΨ'_ne_zero hn')
    (IsAlgClosed.splits _) ?_
  intro x hx
  exact preΨ'_deriv_ne_zero_at_root _ hn' hx

end WeierstrassCurve
