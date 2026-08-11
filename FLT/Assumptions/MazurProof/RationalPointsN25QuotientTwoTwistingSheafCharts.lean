import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingTransition
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Local twisting module sheaves on the N25 projective charts

Each standard coordinate chart of the canonical projective curve is the
affine scheme of its degree-zero homogeneous localization.  Every integral
twist is free of rank one on such a chart, so its local model is the affine
tilde sheaf of the ring as a module over itself.

On pair overlaps, the integral powers of the coordinate ratios give
isomorphisms of these rank-one tilde sheaves.  After restriction to an
ordered triple overlap, functoriality of affine tilde carries the proved
module cocycle to an actual cocycle of module-sheaf isomorphisms.  This is the
local sheaf datum needed before the final global descent construction.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoTwistingSheafCharts

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingTransition
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory

/-! ## Coordinate charts and their local free modules -/

/-- The degree-zero homogeneous coordinate ring of one standard chart. -/
abbrev coordinateChartRing (i : Fin 4) :=
  Away literalConePiece (coordinateClass i)

/-- The affine scheme of one standard projective chart. -/
abbrev coordinateChartScheme (i : Fin 4) : Scheme :=
  Spec (.of (coordinateChartRing i))

/-- The standard chart as an open subscheme of the canonical projective
curve. -/
def coordinateChartMap (i : Fin 4) :
    coordinateChartScheme i ⟶ CanonicalProjectiveCurve25Two :=
  Proj.awayι literalConePiece (coordinateClass i)
    (coordinateClass_mem_degreeOne i) (by norm_num)

/-- Every standard coordinate-chart map is an open immersion. -/
instance coordinateChartMapIsOpenImmersion (i : Fin 4) :
    IsOpenImmersion (coordinateChartMap i) := by
  dsimp [coordinateChartMap]
  infer_instance

/-- Every integral twist is locally the free rank-one module sheaf.  The
integer controls gluing and does not change the local affine module. -/
def coordinateLocalTwistModule (_d : ℤ) (i : Fin 4) :
    (coordinateChartScheme i).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateChartRing i) (coordinateChartRing i))

/-- The local affine model of every twist is canonically the unit module
sheaf on its coordinate chart. -/
def coordinateLocalTwistUnitIso (d : ℤ) (i : Fin 4) :
    coordinateLocalTwistModule d i ≅
      SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf :=
  AlgebraicGeometry.tildeSelf

/-! ## Pair-overlap transition sheaves -/

/-- The affine ring on a pair overlap. -/
abbrev coordinateOverlapRing (i j : Fin 4) :=
  Away literalConePiece (coordinateClass i * coordinateClass j)

/-- The free rank-one module sheaf on a pair overlap. -/
def coordinateOverlapTwistModule (_d : ℤ) (i j : Fin 4) :
    (Spec (.of (coordinateOverlapRing i j))).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateOverlapRing i j) (coordinateOverlapRing i j))

set_option synthInstance.maxHeartbeats 100000 in
-- The explicit homogeneous localization makes the sheaf-composition
-- instance large after unfolding, so this declaration receives a local
-- typeclass-search budget rather than changing the file-wide setting.
/-- The affine pair-overlap model of every twist is canonically the unit
module sheaf on that overlap. -/
def coordinateOverlapTwistUnitIso (d : ℤ) (i j : Fin 4) :
    coordinateOverlapTwistModule d i j ≅
      SheafOfModules.unit
        (Spec (.of (coordinateOverlapRing i j))).ringCatSheaf :=
  AlgebraicGeometry.tildeSelf

/-- The overlap transition lifted from modules to their affine tilde
sheaves. -/
def coordinateOverlapTwistIso (d : ℤ) (i j : Fin 4) :
    coordinateOverlapTwistModule d i j ≅ coordinateOverlapTwistModule d i j :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
    (Away.ratioPowerTransition literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) d).toModuleIso

/-- On the self-overlap of a coordinate chart, the tilde-sheaf transition is
the identity.  This lifts the algebraic identity `x_i / x_i = 1` through the
affine tilde functor. -/
theorem coordinateOverlapTwistIso_self (d : ℤ) (i : Fin 4) :
    (coordinateOverlapTwistIso d i i).hom = 𝟙 _ := by
  change (AlgebraicGeometry.tilde.functor
      (.of (coordinateOverlapRing i i))).map
        (Away.ratioPowerTransition literalConePiece
          (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne i) d).toModuleIso.hom =
      𝟙 _
  rw [Away.ratioPowerTransition_self]
  exact AlgebraicGeometry.tilde.map_id

/-! ## Triple-overlap sheaf cocycle -/

/-- The affine ring on an ordered triple overlap. -/
abbrev coordinateTripleOverlapRing (i j l : Fin 4) :=
  Away literalConePiece ((coordinateClass i * coordinateClass j) * coordinateClass l)

/-- The free rank-one module sheaf on an ordered triple overlap. -/
def coordinateTripleTwistModule (_d : ℤ) (i j l : Fin 4) :
    (Spec (.of (coordinateTripleOverlapRing i j l))).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateTripleOverlapRing i j l)
      (coordinateTripleOverlapRing i j l))

set_option synthInstance.maxHeartbeats 100000 in
-- The threefold homogeneous localization creates a large sheaf-composition
-- instance, so only this canonical affine trivialization receives more search.
/-- The triple-overlap rank-one tilde sheaf is canonically the unit module
sheaf.  Naming this trivialization keeps the two stages of pair restriction
explicit, so their coherence can be proved without relying on definitional
equality between `tildeSelf` and a reflexive isomorphism. -/
def coordinateTripleTwistUnitIso (d : ℤ) (i j l : Fin 4) :
    coordinateTripleTwistModule d i j l ≅
      SheafOfModules.unit
        (Spec (.of (coordinateTripleOverlapRing i j l))).ringCatSheaf :=
  AlgebraicGeometry.tildeSelf

/-- The restricted first-to-second transition as a tilde-sheaf
isomorphism. -/
def coordinateTripleTwistIso12 (d : ℤ) (i j l : Fin 4) :
    coordinateTripleTwistModule d i j l ≅ coordinateTripleTwistModule d i j l :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateTripleOverlapRing i j l))).mapIso
    (Away.ratioPowerModuleIso12 literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne l) d)

/-- The restricted second-to-third transition as a tilde-sheaf
isomorphism. -/
def coordinateTripleTwistIso23 (d : ℤ) (i j l : Fin 4) :
    coordinateTripleTwistModule d i j l ≅ coordinateTripleTwistModule d i j l :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateTripleOverlapRing i j l))).mapIso
    (Away.ratioPowerModuleIso23 literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne l) d)

/-- The direct restricted first-to-third transition as a tilde-sheaf
isomorphism. -/
def coordinateTripleTwistIso13 (d : ℤ) (i j l : Fin 4) :
    coordinateTripleTwistModule d i j l ≅ coordinateTripleTwistModule d i j l :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateTripleOverlapRing i j l))).mapIso
    (Away.ratioPowerModuleIso13 literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne l) d)

/-- The local rank-one tilde-sheaf isomorphisms satisfy the categorical
descent cocycle on every ordered N25 coordinate triple overlap. -/
theorem coordinateTripleTwistIso_cocycle (d : ℤ) (i j l : Fin 4) :
    (coordinateTripleTwistIso12 d i j l).hom ≫
        (coordinateTripleTwistIso23 d i j l).hom =
      (coordinateTripleTwistIso13 d i j l).hom := by
  change (AlgebraicGeometry.tilde.functor
      (.of (coordinateTripleOverlapRing i j l))).map
        (Away.ratioPowerModuleIso12 literalConePiece
          (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
          (coordinateClass_mem_degreeOne l) d).hom ≫
      (AlgebraicGeometry.tilde.functor
        (.of (coordinateTripleOverlapRing i j l))).map
        (Away.ratioPowerModuleIso23 literalConePiece
          (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
          (coordinateClass_mem_degreeOne l) d).hom =
    (AlgebraicGeometry.tilde.functor
      (.of (coordinateTripleOverlapRing i j l))).map
      (Away.ratioPowerModuleIso13 literalConePiece
        (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l) d).hom
  rw [← Functor.map_comp]
  rw [Away.ratioPowerModuleIso_cocycle]

end MazurProof.RationalPointsN25QuotientTwoTwistingSheafCharts
