import Mathlib
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.DescentBridge

/-!
# N=10 and N=12 noncyclic exclusions

N=10: proved from the descent bridge (DescentBridge.no_Z2_cross_Z10_from_descent).
N=12: axiom (descent certificate not yet formalized).
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-- No elliptic curve over ℚ has ℤ/2 × ℤ/10 as a torsion subgroup.
Proved via Kubert parametrization + 2-isogeny descent on obstruction curve 20.a4. -/
theorem no_Z2_cross_Z10 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 10 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z10_from_descent E

/-- No elliptic curve over ℚ has ℤ/2 × ℤ/12 as a torsion subgroup.
Axiom: descent certificate not yet formalized. -/
axiom no_Z2_cross_Z12 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f

end MazurProof
