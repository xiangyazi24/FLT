import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistGlobalComparison

/-!
# The adjunction transition line on the N25 canonical curve

For a `(2,3)` complete intersection in projective three-space, adjunction
combines the ambient canonical transition `O(-4)` with the inverse determinant
of the conormal transition `O(5)`.  On the standard coordinate cover this
composite has exponent `4 - 5 = -1`, hence is the transition of `O(1)`.

This file promotes that calculation from homogeneous localization modules to
the actual Čech equalizer used for the effective curve twists.  It constructs
the line obtained by gluing with the adjunction composite and identifies it
with both the effective degree-one curve twist and the pullback of the ambient
hyperplane twist.  No dualizing sheaf is named or assumed: a later adjunction
theorem must still prove that its local trivializations have this descent
datum.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAdjunctionDescent

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingTransition
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientKoszulPullback
open RationalPointsN25QuotientTwoAmbientTwistRestriction
open RationalPointsN25QuotientTwoAmbientTwistGlobalComparison
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

/-! ## The actual overlap transition supplied by adjunction -/

/-- In the integral-exponent convention used by the Čech construction, the
previously proved `(2,3)` adjunction calculation is the identity
`4 + (-5) = -1`.  This lemma connects the ambient-canonical and conormal
terminology directly to the transition implementation used below. -/
theorem coordinateAdjunctionRatioPowerTransition (i j : Fin 4) :
    (Away.ratioPowerTransition literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) 4).trans
      (Away.ratioPowerTransition literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) (-5)) =
    Away.ratioPowerTransition literalConePiece
      (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) (-1) := by
  change
    (Away.negativeTwistTransition literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) 4).trans
      (Away.positiveTwistTransition literalConePiece
        (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j) 5) =
    Away.positiveTwistTransition literalConePiece
      (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) 1
  exact coordinateAdjunctionTransition i j

/-- The rank-one overlap automorphism obtained by composing the ambient
canonical exponent `4` with the inverse conormal-determinant exponent `-5`.
Its source and target use exponent `-1`, the convention for `O(1)`. -/
def coordinateAdjunctionOverlapIso (i j : Fin 4) :
    coordinateOverlapTwistModule (-1) i j ≅
      coordinateOverlapTwistModule (-1) i j :=
  coordinateOverlapTwistIso 4 i j ≪≫
    coordinateOverlapTwistIso (-5) i j

/-- The sheaf-level adjunction transition is exactly the transition used to
glue the effective positive hyperplane twist.  Functoriality of affine tilde
lifts the exponent identity `4 + (-5) = -1` from rank-one modules. -/
theorem coordinateAdjunctionOverlapIso_eq (i j : Fin 4) :
    coordinateAdjunctionOverlapIso i j =
      coordinateOverlapTwistIso (-1) i j := by
  apply Iso.ext
  change
    (AlgebraicGeometry.tilde.functor
      (.of (coordinateOverlapRing i j))).map
        (Away.ratioPowerTransition literalConePiece
          (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j) 4).toModuleIso.hom ≫
      (AlgebraicGeometry.tilde.functor
        (.of (coordinateOverlapRing i j))).map
        (Away.ratioPowerTransition literalConePiece
          (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j) (-5)).toModuleIso.hom =
    (AlgebraicGeometry.tilde.functor
      (.of (coordinateOverlapRing i j))).map
        (Away.ratioPowerTransition literalConePiece
          (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j) (-1)).toModuleIso.hom
  rw [← Functor.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearEquiv.congr_fun
    (coordinateAdjunctionRatioPowerTransition i j) x

/-! ## Čech descent of the adjunction transition -/

/-- The first Čech arrow formed with the composite adjunction transition,
rather than with a preselected twist exponent.  Its local modules are the
rank-one models of `O(1)`; only the overlap automorphism records its origin
from ambient canonical and conormal determinant factors. -/
def adjunctionCechLeft : twistCechSource (-1) ⟶ twistCechTarget (-1) :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ coordinateLocalPushforward (-1) i) p.1 ≫
      pushforwardRestrictionHom
        (coordinateOverlapToLeft p.1 p.2)
        (coordinateChartMap p.1)
        (coordinateOverlapMap p.1 p.2)
        rfl
        (coordinateLocalTwistModule (-1) p.1)
        (coordinateOverlapTwistModule (-1) p.1 p.2)
        (coordinateRestrictLeftIso (-1) p.1 p.2 ≪≫
          coordinateAdjunctionOverlapIso p.1 p.2)

/-- The composite adjunction Čech arrow is the ordinary degree-one twist
arrow.  Thus its cocycle and effectivity are consequences of an equality of
the actual gluing morphisms, not merely of matching numerical degrees. -/
theorem adjunctionCechLeft_eq_twistCechLeft :
    adjunctionCechLeft = twistCechLeft (-1) := by
  apply Pi.hom_ext
  intro p
  unfold adjunctionCechLeft twistCechLeft
  rw [Pi.lift_π, Pi.lift_π]
  rw [coordinateAdjunctionOverlapIso_eq]

/-- The global line obtained by imposing the adjunction transition equations
on the four standard charts.  This is a transition-defined object and does
not assert that a dualizing sheaf has already been constructed. -/
def adjunctionTransitionLine : CanonicalProjectiveCurve25Two.Modules :=
  equalizer adjunctionCechLeft (twistCechRight (-1))

/-- Equality of the gluing arrows identifies the transition-defined
adjunction line with the effective curve twist of exponent `-1`, namely
`O_C(1)` in the project's sign convention. -/
def adjunctionTransitionLineIsoGlobalTwist :
    adjunctionTransitionLine ≅ globalTwistModule (-1) := by
  simpa only [adjunctionTransitionLine, globalTwistModule,
    adjunctionCechLeft_eq_twistCechLeft] using
      (Iso.refl (globalTwistModule (-1)))

/-- The transition-defined adjunction line is also the actual pullback of the
ambient hyperplane twist.  The comparison uses the independently proved
global ambient/curve Čech isomorphism at exponent `-1`. -/
def adjunctionTransitionLineIsoCurvePullback :
    adjunctionTransitionLine ≅ curvePullbackTwist (-1) :=
  adjunctionTransitionLineIsoGlobalTwist ≪≫
    (curvePullbackTwistGlobalIso (-1)).symm

/-- On every standard chart the transition-defined adjunction line is the
free rank-one unit module.  This is the local trivialization that a future
dualizing adjunction theorem must match. -/
def adjunctionTransitionLineLocalUnitIso (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        adjunctionTransitionLine ≅
      SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap i)).mapIso
      adjunctionTransitionLineIsoGlobalTwist ≪≫
    globalTwistModuleLocalUnitIso (-1) i

end MazurProof.RationalPointsN25QuotientTwoAdjunctionDescent
