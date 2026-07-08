import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 25 exclusion

A rational point of order 25 on E/ℚ. This is the hardest composite
exclusion: X₁(25) has genus 12, and no rank-0 elliptic bridge exists
at level 25 (J₁(25) decomposes into 4-dimensional abelian varieties).

This may remain as a named sub-axiom until a descent-evaluation
approach (via the Miller function / 5th-power residue symbol) is
developed.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion25

axiom order25_contradiction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) : False

theorem no_rational_point_of_order_25
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 25 :=
  fun h => order25_contradiction E h

end MazurProof.CyclicExclusion25
