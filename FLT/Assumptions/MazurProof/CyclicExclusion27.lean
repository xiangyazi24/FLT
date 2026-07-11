import FLT.Assumptions.MazurProof.RationalPointsN27ThreeDescent

/-!
# Cyclic order 27 exclusion

An exact order-27 point `P` gives the order-nine point `3P`.  We put `3P`
in Kubert's Tate normal form while transporting `P` through the same group
isomorphism.  The resulting Kubert origin is therefore rationally divisible
by three.

The special three-descent in `RationalPointsN27ThreeDescent` moves the rational
three-torsion flex to the origin.  Its `Y`-coordinate is a rational cube on
triples, which constructs a noncuspidal rational point on the level-27 curve

`y^2 + y = x^3`.

`RationalPointsN27CM` proves that this curve has only its two affine cusps, so
the assumed order-27 point cannot exist.  In particular, this proof does not
use the old and incorrect assertion that the level-27 quotient is isomorphic
to the Fermat cubic.
-/

namespace MazurProof.CyclicExclusion27

theorem no_rational_point_of_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 27 :=
  RationalPointsN27ThreeDescent.no_rational_point_of_order_27 E

end MazurProof.CyclicExclusion27
