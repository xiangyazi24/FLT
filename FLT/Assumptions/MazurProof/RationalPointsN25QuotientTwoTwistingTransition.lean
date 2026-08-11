import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoProj
import FLT.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistingTransition

/-!
# Twisting transitions on the N25 coordinate charts

The four quotient coordinate classes are homogeneous of degree one and their
projective basic opens cover the binary canonical curve.  This file
specializes the generic degree-one transition units to those charts.  On the
overlap of charts `i` and `j`, the negative twist by `debt` changes
trivialization by `(x_j/x_i)^debt`; the transition ratios satisfy the required
triple-overlap cocycle.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoTwistingTransition

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The image of the `i`th projective coordinate in the canonical quotient
ring. -/
def coordinateClass (i : Fin 4) : CanonicalConeRing25Two :=
  canonicalConeProjection (MvPolynomial.X i)

/-- Every quotient coordinate class remains homogeneous of degree one. -/
theorem coordinateClass_mem_degreeOne (i : Fin 4) :
    coordinateClass i ∈ literalConePiece 1 := by
  exact canonicalConeGradedProjection.2
    (MvPolynomial.isHomogeneous_X (ZMod 2) i)

/-- The ratio `x_j/x_i` as a unit on the overlap of the two coordinate
charts. -/
def coordinateRatioUnit (i j : Fin 4) :
    (Away literalConePiece (coordinateClass i * coordinateClass j))ˣ :=
  Away.degreeOneRatioUnit literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)

/-- The change of trivialization for the negative twist by `debt` between
the `i`th and `j`th coordinate charts. -/
def negativeTwistCoordinateTransition (debt : ℕ) (i j : Fin 4) :
    Away literalConePiece (coordinateClass i * coordinateClass j) ≃ₗ[
      Away literalConePiece (coordinateClass i * coordinateClass j)]
      Away literalConePiece (coordinateClass i * coordinateClass j) :=
  Away.negativeTwistTransition literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) debt

/-- On each coordinate overlap, the determinant of the degree-two and
degree-three conormal transitions is the degree-five negative twist. -/
theorem coordinateConormalDetTransition (i j : Fin 4) :
    coordinateRatioUnit i j ^ 2 * coordinateRatioUnit i j ^ 3 =
      coordinateRatioUnit i j ^ 5 :=
  Away.degreeTwoThreeDetTransition literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)

/-- The chartwise adjunction transition is exactly that of the positive
twist by one. -/
theorem coordinateAdjunctionTransition (i j : Fin 4) :
    (Away.negativeTwistTransition literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 4).trans
      (Away.positiveTwistTransition literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 5) =
    Away.positiveTwistTransition literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) 1 :=
  Away.degreeTwoThreeAdjunctionTransition literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)

/-- The N25 coordinate transition ratios satisfy the multiplicative cocycle
identity on every ordered triple overlap. -/
theorem coordinateRatio_cocycle (i j l : Fin 4) :
    Away.degreeOneRatio12 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) *
      Away.degreeOneRatio23 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) =
      Away.degreeOneRatio13 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) :=
  Away.degreeOneRatio_cocycle literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne l)

end MazurProof.RationalPointsN25QuotientTwoTwistingTransition
