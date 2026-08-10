import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoProj
import FLT.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# The N25 canonical quotient is a closed projective subscheme

The homogeneous coordinate quotient is surjective, so the induced morphism
from its `Proj` to binary projective three-space is a closed immersion.  The
proof is scheme-theoretic and chartwise; it does not enumerate points or
compare dimensions.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoClosedImmersion

open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective quadric-cubic quotient is a closed subscheme of binary
projective three-space. -/
instance canonicalProjectiveCurveMap_isClosedImmersion :
    IsClosedImmersion canonicalProjectiveCurveMap :=
  Proj.isClosedImmersion_map_of_surjective
    canonicalConeGradedProjection canonicalCone_irrelevant_le_map
    canonicalConeGradedProjection_surjective

end MazurProof.RationalPointsN25QuotientTwoClosedImmersion
