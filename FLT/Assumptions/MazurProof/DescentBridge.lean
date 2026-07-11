import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsC20
import FLT.Assumptions.MazurProof.KubertBridgeN10

/-!
# N=10 descent bridge

Connects the rational-points computation on the C20 obstruction curve and the
Kubert N=10 bridge to the noncyclic exclusion.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem no_Z2_cross_Z10_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases KubertBridgeN10.bridge_N10 E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (RationalPointsC20.obstruction_curve_20a4_from_elementary u w hcurve)

end MazurProof
