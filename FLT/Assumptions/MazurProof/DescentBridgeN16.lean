import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN16Defs
import FLT.Assumptions.MazurProof.KubertBridgeN16
import FLT.Assumptions.MazurProof.RationalPointsN16

/-! # N=16 descent bridge -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u :=
  KubertBridgeN16.bridge_N16 E hE

theorem no_Z2_cross_Z16_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ16_gives_non_degenerate_N16_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (RationalPointsN16.obstruction_curve_N16_from_elementary u w hcurve)

end MazurProof
