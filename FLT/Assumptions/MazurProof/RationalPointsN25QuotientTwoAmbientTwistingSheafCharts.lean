import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoKoszulSheafTransition

/-!
# Ambient twisting module sheaves for the N25 projective Koszul resolution

The Koszul resolution lives on binary projective three-space.  Its terms are
the twists `O`, `O(-2)`, `O(-3)`, and `O(-5)`, so the twisting descent datum
must be built from the ambient polynomial ring rather than from the quotient
coordinate ring of the curve.

This file constructs the free rank-one affine-tilde model on every ambient
coordinate chart, its integer-power transition on each ordered pair overlap,
and the actual module-sheaf cocycle on each ordered triple overlap.  These are
the local objects and coherence maps needed by the ambient Čech equalizer.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafCharts

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoKoszulTransition
open RationalPointsN25QuotientTwoKoszulSheafTransition
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Coordinate-chart and pair-overlap modules -/

/-- Every ambient integral twist is locally the free rank-one affine tilde
module.  The integer affects gluing but not the local object. -/
def ambientLocalTwistModule (_d : ℤ) (i : Fin 4) :
    (ambientCoordinateChartScheme i).Modules :=
  tilde (ModuleCat.of (AmbientChartRingCat i) (AmbientChartRingCat i))

/-- The local affine model of every ambient twist is the unit module sheaf. -/
def ambientLocalTwistUnitIso (d : ℤ) (i : Fin 4) :
    ambientLocalTwistModule d i ≅
      SheafOfModules.unit (ambientCoordinateChartScheme i).ringCatSheaf :=
  tildeSelf

/-- The free rank-one affine tilde module on an ordered ambient overlap. -/
def ambientOverlapTwistModule (_d : ℤ) (i j : Fin 4) :
    (Spec (AmbientOverlapRingCat i j)).Modules :=
  tilde (ModuleCat.of (AmbientOverlapRingCat i j)
    (AmbientOverlapRingCat i j))

/-- The overlap model of every ambient twist is the overlap unit sheaf. -/
def ambientOverlapTwistUnitIso (d : ℤ) (i j : Fin 4) :
    ambientOverlapTwistModule d i j ≅
      SheafOfModules.unit (Spec (AmbientOverlapRingCat i j)).ringCatSheaf :=
  tildeSelf

/-- The integer-power coordinate-ratio transition on an ordered ambient
pair overlap, lifted from modules to affine tilde sheaves. -/
def ambientOverlapTwistIso (d : ℤ) (i j : Fin 4) :
    ambientOverlapTwistModule d i j ≅ ambientOverlapTwistModule d i j :=
  (tilde.functor (AmbientOverlapRingCat i j)).mapIso
    (Away.ratioPowerTransition standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) d).toModuleIso

/-- The transition on a chart's self-overlap is the identity. -/
theorem ambientOverlapTwistIso_self (d : ℤ) (i : Fin 4) :
    (ambientOverlapTwistIso d i i).hom = 𝟙 _ := by
  change (tilde.functor (AmbientOverlapRingCat i i)).map
      (Away.ratioPowerTransition standardConePiece
        (coordinate_isHomogeneous i) (coordinate_isHomogeneous i) d).toModuleIso.hom =
    𝟙 _
  rw [Away.ratioPowerTransition_self]
  exact tilde.map_id

/-! ## Triple-overlap cocycle -/

/-- The ordered ambient triple-overlap ring. -/
abbrev AmbientTripleOverlapRing (i j l : Fin 4) :=
  Away standardConePiece
    ((MvPolynomial.X i * MvPolynomial.X j) * MvPolynomial.X l)

/-- The ordered ambient triple-overlap ring as a bundled commutative ring. -/
abbrev AmbientTripleOverlapRingCat (i j l : Fin 4) : CommRingCat :=
  .of (AmbientTripleOverlapRing i j l)

/-- The free rank-one affine tilde module on an ordered triple overlap. -/
def ambientTripleTwistModule (_d : ℤ) (i j l : Fin 4) :
    (Spec (AmbientTripleOverlapRingCat i j l)).Modules :=
  tilde (ModuleCat.of (AmbientTripleOverlapRingCat i j l)
    (AmbientTripleOverlapRingCat i j l))

/-- The triple-overlap model is canonically the unit module sheaf. -/
def ambientTripleTwistUnitIso (d : ℤ) (i j l : Fin 4) :
    ambientTripleTwistModule d i j l ≅
      SheafOfModules.unit
        (Spec (AmbientTripleOverlapRingCat i j l)).ringCatSheaf :=
  tildeSelf

/-- Restriction of the first-to-second transition to the ordered triple
overlap. -/
def ambientTripleTwistIso12 (d : ℤ) (i j l : Fin 4) :
    ambientTripleTwistModule d i j l ≅ ambientTripleTwistModule d i j l :=
  (tilde.functor (AmbientTripleOverlapRingCat i j l)).mapIso
    (Away.ratioPowerModuleIso12 standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
      (coordinate_isHomogeneous l) d)

/-- Restriction of the second-to-third transition to the ordered triple
overlap. -/
def ambientTripleTwistIso23 (d : ℤ) (i j l : Fin 4) :
    ambientTripleTwistModule d i j l ≅ ambientTripleTwistModule d i j l :=
  (tilde.functor (AmbientTripleOverlapRingCat i j l)).mapIso
    (Away.ratioPowerModuleIso23 standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
      (coordinate_isHomogeneous l) d)

/-- Direct restriction of the first-to-third transition to the ordered
triple overlap. -/
def ambientTripleTwistIso13 (d : ℤ) (i j l : Fin 4) :
    ambientTripleTwistModule d i j l ≅ ambientTripleTwistModule d i j l :=
  (tilde.functor (AmbientTripleOverlapRingCat i j l)).mapIso
    (Away.ratioPowerModuleIso13 standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
      (coordinate_isHomogeneous l) d)

/-- The ambient twisting transitions satisfy the categorical Čech cocycle on
every ordered triple overlap. -/
theorem ambientTripleTwistIso_cocycle (d : ℤ) (i j l : Fin 4) :
    (ambientTripleTwistIso12 d i j l).hom ≫
        (ambientTripleTwistIso23 d i j l).hom =
      (ambientTripleTwistIso13 d i j l).hom := by
  change (tilde.functor (AmbientTripleOverlapRingCat i j l)).map
      (Away.ratioPowerModuleIso12 standardConePiece
        (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
        (coordinate_isHomogeneous l) d).hom ≫
    (tilde.functor (AmbientTripleOverlapRingCat i j l)).map
      (Away.ratioPowerModuleIso23 standardConePiece
        (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
        (coordinate_isHomogeneous l) d).hom =
    (tilde.functor (AmbientTripleOverlapRingCat i j l)).map
      (Away.ratioPowerModuleIso13 standardConePiece
        (coordinate_isHomogeneous i) (coordinate_isHomogeneous j)
        (coordinate_isHomogeneous l) d).hom
  rw [← Functor.map_comp]
  rw [Away.ratioPowerModuleIso_cocycle]

end MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
