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
open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The image of the `i`th projective coordinate in the canonical quotient
ring. -/
abbrev coordinateClass (i : Fin 4) : CanonicalConeRing25Two :=
  canonicalConeGradedProjection (MvPolynomial.X i)

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

/-- The transition unit from a coordinate chart to itself is the identity. -/
theorem coordinateRatioUnit_self (i : Fin 4) :
    coordinateRatioUnit i i = 1 :=
  Away.degreeOneRatioUnit_self literalConePiece
    (coordinateClass_mem_degreeOne i)

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

/-- The pairwise N25 coordinate ratios satisfy the genuine Čech cocycle after
restriction to the common ordered triple overlap. -/
theorem coordinateRatio_restricted_cocycle (i j l : Fin 4) :
    Away.restrict12 literalConePiece (coordinateClass_mem_degreeOne l)
        (Away.degreeOneRatio literalConePiece
          (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)) *
      Away.restrict23 literalConePiece (coordinateClass_mem_degreeOne i)
        (Away.degreeOneRatio literalConePiece
          (coordinateClass_mem_degreeOne j) (coordinateClass_mem_degreeOne l)) =
    Away.restrict13 literalConePiece (coordinateClass_mem_degreeOne j)
      (Away.degreeOneRatio literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne l)) :=
  Away.degreeOneRatio_restricted_cocycle literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne l)

/-- Every integral power of the N25 coordinate transition units satisfies
the restricted Čech cocycle.  This simultaneously covers all positive and
negative twists used in adjunction. -/
theorem coordinateTwistUnit_restricted_cocycle (i j l : Fin 4) (d : ℤ) :
    (Units.map (Away.restrict12 literalConePiece
        (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
        (coordinateClass_mem_degreeOne l)).toMonoidHom
      (coordinateRatioUnit i j)) ^ d *
    (Units.map (Away.restrict23 literalConePiece
        (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
        (coordinateClass_mem_degreeOne i)).toMonoidHom
      (coordinateRatioUnit j l)) ^ d =
    (Units.map (Away.restrict13 literalConePiece
        (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
        (coordinateClass_mem_degreeOne j)).toMonoidHom
      (coordinateRatioUnit i l)) ^ d :=
  Away.degreeOneRatioUnit_zpow_restricted_cocycle literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne l) d

/-- The free rank-one module transition isomorphisms for the integral twist
of exponent `d` satisfy the categorical descent cocycle on N25 coordinate
triple overlaps. -/
theorem coordinateTwistModuleIso_cocycle (i j l : Fin 4) (d : ℤ) :
    (Away.ratioPowerModuleIso12 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) d).hom ≫
      (Away.ratioPowerModuleIso23 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) d).hom =
    (Away.ratioPowerModuleIso13 literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne l) d).hom :=
  Away.ratioPowerModuleIso_cocycle literalConePiece
    (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne l) d

end MazurProof.RationalPointsN25QuotientTwoTwistingTransition
