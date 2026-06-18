import Mathlib
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.DescentBridge
import FLT.Assumptions.MazurProof.DescentBridgeN12

/-! # N=10 and N=12 noncyclic exclusions — both proved from descent bridges -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem no_Z2_cross_Z10 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 10 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z10_from_descent E

theorem no_Z2_cross_Z12 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z12_from_descent E

end MazurProof
