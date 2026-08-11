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

/-- Every integral twist is locally the free rank-one module sheaf.  The
integer controls gluing and does not change the local affine module. -/
def coordinateLocalTwistModule (_d : ℤ) (i : Fin 4) :
    (coordinateChartScheme i).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateChartRing i) (coordinateChartRing i))

/-! ## Pair-overlap transition sheaves -/

/-- The affine ring on a pair overlap. -/
abbrev coordinateOverlapRing (i j : Fin 4) :=
  Away literalConePiece (coordinateClass i * coordinateClass j)

/-- The free rank-one module sheaf on a pair overlap. -/
def coordinateOverlapTwistModule (_d : ℤ) (i j : Fin 4) :
    (Spec (.of (coordinateOverlapRing i j))).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateOverlapRing i j) (coordinateOverlapRing i j))

/-- The overlap transition lifted from modules to their affine tilde
sheaves. -/
def coordinateOverlapTwistIso (d : ℤ) (i j : Fin 4) :
    coordinateOverlapTwistModule d i j ≅ coordinateOverlapTwistModule d i j :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
    (Away.ratioPowerTransition literalConePiece
      (coordinateClass_mem_degreeOne i) (coordinateClass_mem_degreeOne j) d).toModuleIso

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
