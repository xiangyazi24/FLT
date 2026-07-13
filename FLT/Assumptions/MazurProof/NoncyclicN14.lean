import FLT.Assumptions.MazurProof.CyclicExclusion14

/-!
# Noncyclic ℤ/2 × ℤ/14 exclusion via cyclic order-14

The injective embedding ℤ/2 × ℤ/14 ↪ E(ℚ) gives a rational point of
additive order 14 (the image of (0,1)).  The cyclic order-14 exclusion
already proves ¬ HasRationalPointOfOrder E 14.  So the noncyclic
embedding is impossible.

This eliminates the `Z2xZ14_gives_non_degenerate_N14_point` axiom in
DescentBridgeN14.lean, providing the same conclusion axiom-free.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.NoncyclicN14

theorem no_Z2_cross_Z14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hord : addOrderOf (f (0, 1)) = 14 := by
    rw [addOrderOf_injective f hf]
    decide
  exact no_rational_point_of_order_14 E ⟨f (0, 1), hord⟩

end MazurProof.NoncyclicN14
