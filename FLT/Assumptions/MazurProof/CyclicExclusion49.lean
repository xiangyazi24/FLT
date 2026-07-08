import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 49 exclusion

A rational point of order 49 gives a rational cyclic-49 isogeny, hence a
non-cuspidal rational point on X₀(49). The curve X₀(49) is 49a1 (rank 0,
torsion ℤ/2ℤ), whose only rational points are cusps.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion49

axiom order49_gives_X0_49_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h49 : HasRationalPointOfOrder E 49) : False

theorem no_rational_point_of_order_49
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 49 :=
  fun h => order49_gives_X0_49_point E h

end MazurProof.CyclicExclusion49
