import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 35 exclusion

A rational point of order 35 = 5 · 7 gives simultaneous rational points of
order 5 and 7 on the same curve. This corresponds to a rational point on
the fiber product X₁(5) ×_{j-line} X₁(7), which has no non-cuspidal rational
points.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion35

axiom order35_contradiction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h35 : HasRationalPointOfOrder E 35) : False

theorem no_rational_point_of_order_35
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 35 :=
  fun h => order35_contradiction E h

end MazurProof.CyclicExclusion35
