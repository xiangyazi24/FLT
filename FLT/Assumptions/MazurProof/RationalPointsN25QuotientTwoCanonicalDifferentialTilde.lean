import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine tilde sheaves of the N25 canonical differentials

The actual Kähler differential modules on the four projective charts and
their ordered overlaps define affine tilde sheaves.  Their residue coordinates
give rank-one trivializations.  On every ordered overlap, functoriality of
affine tilde carries the proved inverse coordinate-ratio transition to the
same exponent `-1` transition used by the existing twisting sheaf.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialTilde

open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoCanonicalDifferentialCharts
open RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingTransition
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory

/-! ## Actual affine differential sheaves -/

/-- The affine tilde sheaf of the actual Kähler differential module on a
standard projective chart. -/
abbrev chartCoordinateKaehlerDifferentialSheaf (i : Fin 4) :
    (coordinateChartScheme i).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (ChartCoordinateRing i) Ω[ChartCoordinateRing i⁄k])

/-- The Jacobian residue coordinate trivializes the actual chart differential
sheaf as the rank-one tilde module used by the twist descent. -/
def chartCoordinateKaehlerDifferentialTildeIso (i : Fin 4) :
    chartCoordinateKaehlerDifferentialSheaf i ≅
      coordinateLocalTwistModule (-1) i :=
  (AlgebraicGeometry.tilde.functor (.of (ChartCoordinateRing i))).mapIso
    (chartCoordinateKaehlerDifferentialEquiv i).toModuleIso

/-- The chart residue frame followed by the canonical rank-one frame gives a
unit-sheaf trivialization of the actual differential sheaf. -/
def chartCoordinateKaehlerDifferentialUnitIso (i : Fin 4) :
    chartCoordinateKaehlerDifferentialSheaf i ≅
      SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf :=
  chartCoordinateKaehlerDifferentialTildeIso i ≪≫
    coordinateLocalTwistUnitIso (-1) i

/-- The affine tilde sheaf of relative Kähler differentials on an ordered
coordinate overlap. -/
abbrev coordinateOverlapKaehlerDifferentialSheaf (i j : Fin 4) :
    (Spec (.of (coordinateOverlapRing i j))).Modules :=
  AlgebraicGeometry.tilde
    (ModuleCat.of (coordinateOverlapRing i j) Ω[coordinateOverlapRing i j⁄k])

/-- The residue frame induced from the first chart, before identifying the
rank-one target with the unit sheaf. -/
def coordinateOverlapLeftKaehlerDifferentialTildeIso (i j : Fin 4) :
    coordinateOverlapKaehlerDifferentialSheaf i j ≅
      coordinateOverlapTwistModule (-1) i j :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
    (coordinateOverlapLeftKaehlerDifferentialEquiv i j).toModuleIso

/-- The residue frame induced from the second chart, expressed over the same
ordered overlap ring. -/
def coordinateOverlapRightKaehlerDifferentialTildeIso (i j : Fin 4) :
    coordinateOverlapKaehlerDifferentialSheaf i j ≅
      coordinateOverlapTwistModule (-1) i j :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
    (coordinateOverlapRightKaehlerDifferentialEquiv i j).toModuleIso

set_option synthInstance.maxHeartbeats 100000 in
-- The explicit homogeneous localization makes the sheaf-composition
-- instance large after unfolding.
/-- The first-chart residue frame gives a unit-sheaf trivialization on the
ordered overlap. -/
def coordinateOverlapLeftKaehlerDifferentialUnitIso (i j : Fin 4) :
    coordinateOverlapKaehlerDifferentialSheaf i j ≅
      SheafOfModules.unit
        (Spec (.of (coordinateOverlapRing i j))).ringCatSheaf :=
  coordinateOverlapLeftKaehlerDifferentialTildeIso i j ≪≫
    coordinateOverlapTwistUnitIso (-1) i j

set_option synthInstance.maxHeartbeats 100000 in
-- The explicit homogeneous localization makes the sheaf-composition
-- instance large after unfolding.
/-- The second-chart residue frame gives a unit-sheaf trivialization on the
same ordered overlap. -/
def coordinateOverlapRightKaehlerDifferentialUnitIso (i j : Fin 4) :
    coordinateOverlapKaehlerDifferentialSheaf i j ≅
      SheafOfModules.unit
        (Spec (.of (coordinateOverlapRing i j))).ringCatSheaf :=
  coordinateOverlapRightKaehlerDifferentialTildeIso i j ≪≫
    coordinateOverlapTwistUnitIso (-1) i j

/-! ## Compatibility with the existing twist transition -/

/-- Affine tilde applied to the residue-coordinate change on the overlap
rank-one module. -/
def coordinateOverlapResidueTildeTransition (i j : Fin 4) :
    coordinateOverlapTwistModule (-1) i j ≅
      coordinateOverlapTwistModule (-1) i j :=
  (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
    (coordinateOverlapResidueTransition i j).toModuleIso

/-- The affine-tilde residue transition is exactly the overlap transition of
the effective degree-one twist. -/
theorem coordinateOverlapResidueTildeTransition_eq_twist
    (i j : Fin 4) :
    coordinateOverlapResidueTildeTransition i j =
      coordinateOverlapTwistIso (-1) i j := by
  unfold coordinateOverlapResidueTildeTransition coordinateOverlapTwistIso
  rw [coordinateOverlapResidueTransition_eq_ratioPowerTransition]

/-- Functoriality preserves the factorization of the right residue coordinate
through the left residue coordinate and their change of frame. -/
theorem coordinateOverlapKaehlerDifferentialTildeIso_transition
    (i j : Fin 4) :
    (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
        (coordinateOverlapRightKaehlerDifferentialEquiv i j).toModuleIso =
      (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
          (coordinateOverlapLeftKaehlerDifferentialEquiv i j).toModuleIso ≪≫
        (AlgebraicGeometry.tilde.functor (.of (coordinateOverlapRing i j))).mapIso
          (coordinateOverlapResidueTransition i j).toModuleIso := by
  rw [← Functor.mapIso_trans]
  congr 1
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [coordinateOverlapResidueTransition]

/-- Under the two actual Kähler residue frames, the ordered-overlap change is
the inverse coordinate-ratio transition of `O(1)`. -/
theorem coordinateOverlapRightKaehlerDifferentialTildeIso_eq
    (i j : Fin 4) :
    coordinateOverlapRightKaehlerDifferentialTildeIso i j =
      coordinateOverlapLeftKaehlerDifferentialTildeIso i j ≪≫
        coordinateOverlapTwistIso (-1) i j := by
  calc
    coordinateOverlapRightKaehlerDifferentialTildeIso i j =
        coordinateOverlapLeftKaehlerDifferentialTildeIso i j ≪≫
          coordinateOverlapResidueTildeTransition i j :=
      coordinateOverlapKaehlerDifferentialTildeIso_transition i j
    _ = coordinateOverlapLeftKaehlerDifferentialTildeIso i j ≪≫
          coordinateOverlapTwistIso (-1) i j := by
      rw [coordinateOverlapResidueTildeTransition_eq_twist]

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialTilde
