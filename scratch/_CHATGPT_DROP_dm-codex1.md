# Q2928 (dm-codex1): first group-law exclusion lemma

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

The direct route is `two_nsmul` plus `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`.  The hypothesis `h6` is not needed for the final line once `hO` is already supplied; keep it in the signature for the later Tate-normal-form workflow.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

theorem origin_order_two_if_a3_eq_zero
    (W : WeierstrassCurve ℚ)
    (h6 : W.a₆ = 0)
    (h3 : W.a₃ = 0)
    (hO : (WeierstrassCurve.toAffine W).Nonsingular 0 0) :
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 hO) = 0 := by
  rw [two_nsmul]
  have hy : (0 : ℚ) = (WeierstrassCurve.toAffine W).negY 0 0 := by
    simp [WeierstrassCurve.Affine.negY, h3]
  simpa using
    (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      (W := WeierstrassCurve.toAffine W) (h₁ := hO) hy)
```

If Lean complains that `two_nsmul` is not found by the imports already in the file, try one of these equivalent first lines:

```lean
  change WeierstrassCurve.Affine.Point.some 0 0 hO +
      WeierstrassCurve.Affine.Point.some 0 0 hO = 0
```

or:

```lean
  norm_num [two_nsmul]
```

The immediate exact-order-12 exclusion can use the order-of-element API generated from `orderOf_dvd_of_pow_eq_one`.

```lean
theorem origin_a3_ne_zero_of_addOrderOf_eq_12
    (W : WeierstrassCurve ℚ)
    (h6 : W.a₆ = 0)
    (hO : (WeierstrassCurve.toAffine W).Nonsingular 0 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    W.a₃ ≠ 0 := by
  intro h3
  let O : WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine W) :=
    WeierstrassCurve.Affine.Point.some 0 0 hO
  have h2 : (2 : ℕ) • O = 0 := by
    simpa [O] using origin_order_two_if_a3_eq_zero W h6 h3 hO
  have hdvd : addOrderOf O ∣ 2 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [hOrder] at hdvd
  norm_num at hdvd

end
end MazurProof.KubertBridgeN12
```

If `addOrderOf_dvd_of_nsmul_eq_zero` has a slightly different generated name locally, this replacement is usually accepted:

```lean
  have hdvd : addOrderOf O ∣ 2 := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact h2
```

The only real mathematical content is proving that `negY 0 0 = 0` when `a₃ = 0`; the rest is the existing affine group-law vertical-addition lemma.
