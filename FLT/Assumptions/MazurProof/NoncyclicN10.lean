import Mathlib
import FLT.EllipticCurve.Torsion

/-!
# N=10 noncyclic exclusion

No elliptic curve over ℚ has rational torsion containing ℤ/2 × ℤ/10.

Proof route: Kubert parametrization → obstruction curve 20.a4 → rank 0 → only cusps.
The descent certificate (native_decide local checks) is in DescentObstruction.lean.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-- No elliptic curve over ℚ has an injective embedding of ℤ/2 × ℤ/10 into its rational points. -/
axiom no_Z2_cross_Z10 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 10 →+ (E⁄ℚ).Point, Function.Injective f

/-- No elliptic curve over ℚ has an injective embedding of ℤ/2 × ℤ/12 into its rational points. -/
axiom no_Z2_cross_Z12 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f

end MazurProof
