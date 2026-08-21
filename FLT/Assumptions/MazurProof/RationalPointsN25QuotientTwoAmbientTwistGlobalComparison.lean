import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistRestriction
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoSmooth

/-!
# Identifying the ambient and Čech twists on the canonical curve

There are two sheaves playing the role of `O(d)` on the canonical curve.  One
is obtained by pulling the projective twisting sheaf back along the canonical
closed immersion.  The other is obtained by gluing the standard rank-one
modules on the four affine coordinate charts.  Their local trivializations
were identified in the preceding file.

The remaining mathematical point is descent: the four local identifications
must agree on every ordered double intersection.  We prove this by comparing
restriction to an overlap with pullback from the corresponding ambient
overlap.  The compatible local maps then factor through the Čech equalizer,
giving the global comparison of the two twists.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientTwistGlobalComparison

open RationalPointsN25QuotientTwoAmbientKoszulPullback
open RationalPointsN25QuotientTwoAmbientTwistRestriction
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientKoszulGeometry
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoTwistingTransition
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingSheafGluing
open RationalPointsN25QuotientTwoSmooth
open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ambientTwistPairCompatibility" =>
  RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleToLocal_pair_compatibility

-- Componentwise symmetry of a natural isomorphism exposes its inverse
-- natural transformation, which keeps the base-change normal forms stable.
@[simp]
theorem natIso_symm_app_hom_eq_inv_app
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    (e.symm.app X).hom = e.inv.app X := by
  rfl

/-- The restriction comparison attached to reflexivity has identity forward
component as well as identity inverse component. -/
theorem restrictFunctorCongr_refl_hom_app
    {Q U : Scheme} (f : Q ⟶ U) [IsOpenImmersion f]
    (F : U.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app F = 𝟙 _ := by
  apply (cancel_mono
    ((Scheme.Modules.restrictFunctorCongr (rfl : f = f)).inv.app F)).1
  rw [Iso.hom_inv_id_app]
  rw [Scheme.Modules.restrictFunctorCongr_refl_inv_app,
    Category.id_comp]

/-- Changing the chosen names of the two vertical arrows in a cartesian
square conjugates Beck--Chevalley by the corresponding restriction
comparisons. -/
theorem verticalOpenPullbackBaseChangeIso_congr
    {Q V P U : Scheme} (r : Q ⟶ V)
    (q q' : Q ⟶ P) (k k' : V ⟶ U) (b : P ⟶ U)
    [iq : IsOpenImmersion q] [iq' : IsOpenImmersion q']
    [ik : IsOpenImmersion k] [ik' : IsOpenImmersion k']
    (hq : q = q') (hk : k = k')
    (H : IsPullback r q k b) (H' : IsPullback r q' k' b)
    (F : U.Modules) :
    (Scheme.Modules.restrictFunctorCongr hq).hom.app
          ((Scheme.Modules.pullback b).obj F) ≫
        (Scheme.Modules.verticalOpenPullbackBaseChangeIso
          r q' k' b H').inv.app F ≫
        (Scheme.Modules.pullback r).map
          ((Scheme.Modules.restrictFunctorCongr hk).inv.app F) =
      (Scheme.Modules.verticalOpenPullbackBaseChangeIso
        r q k b H).inv.app F := by
  subst q'
  subst k'
  have hiq : iq' = iq := Subsingleton.elim _ _
  have hik : ik' = ik := Subsingleton.elim _ _
  subst iq'
  subst ik'
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  rw [restrictFunctorCongr_refl_hom_app,
    Scheme.Modules.restrictFunctorCongr_refl_inv_app]
  rw [Category.id_comp, (Scheme.Modules.pullback r).map_id]
  exact Category.comp_id _

/-! ## Geometry of an ordered double intersection

For coordinate charts `i` and `j`, the curve overlap is obtained by pulling
the ambient coordinate overlap back to the canonical curve.  This cartesian
description is what allows the ambient transition map for `O(d)` to be
compared with the curve-side transition map.
-/

set_option maxHeartbeats 800000 in
-- Comparing the independently chosen affine chart square unfolds large
-- homogeneous-localization equivalences.
/-- The `i`-th affine chart of the canonical curve is the fiber product of
the curve with the `i`-th ambient projective chart.  This version uses the
chart object chosen by the independent Čech construction, so it can be pasted
directly with the ordered-overlap square below. -/
theorem coordinateCurveChart_square_isPullback (i : Fin 4) :
    IsPullback (coordinateLocalCurveMap i) (coordinateChartMap i)
      (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
      canonicalProjectiveCurveMap := by
  convert curveChart_square_isPullback i using 1 <;> rfl

/-- The ambient pullback twist normalized on the chart object used by the
curve-side Čech construction. -/
def curvePullbackTwistCoordinateLocalIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        (curvePullbackTwist d) ≅
      SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf :=
  (Scheme.Modules.verticalOpenPullbackBaseChangeIso
    (coordinateLocalCurveMap i) (coordinateChartMap i)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
    canonicalProjectiveCurveMap
    (coordinateCurveChart_square_isPullback i)).symm.app
      (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d) ≪≫
  (Scheme.Modules.pullback (coordinateLocalCurveMap i)).mapIso
    (ambientRestrictedTwistUnitIso d i) ≪≫
  Scheme.Modules.pullbackUnitIsoOfScheme (coordinateLocalCurveMap i)

/-- The coordinate-chart normalization with the local Čech twist as target. -/
def curvePullbackTwistCoordinateChartIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        (curvePullbackTwist d) ≅ coordinateLocalTwistModule d i :=
  curvePullbackTwistCoordinateLocalIso d i ≪≫
    (coordinateLocalTwistUnitIso d i).symm

/-- The ordered curve overlap `C_{ij}` is the fiber product of the canonical
curve with the ambient overlap `U_{ij}` over projective space.  The square is
the vertical composite of the chart pullback square with the pullback square
defining the overlap inside that chart. -/
theorem curveOverlap_square_isPullback (i j : Fin 4) :
    IsPullback (localOverlapCurveMap i j) (coordinateOverlapMap i j)
      (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
      canonicalProjectiveCurveMap := by
  have h := (localOverlapCurveMap_left_square_isPullback i j).paste_vert
    (coordinateCurveChart_square_isPullback i)
  have hchart : curveChartMap i = coordinateChartMap i := rfl
  simpa only [coordinateOverlapMap,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap,
    hchart] using h

/-- Restricting the pulled-back ambient twist to `C_{ij}` is canonically the
same as first restricting the ambient twist to `U_{ij}` and then pulling it
back to `C_{ij}`.  This is the comparison through which the ambient cocycle
will be transported to the curve-side Čech cocycle. -/
def curvePullbackTwistOverlapBaseChangeIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapMap i j)).obj
        (curvePullbackTwist d) ≅
      (Scheme.Modules.pullback (localOverlapCurveMap i j)).obj
        ((Scheme.Modules.restrictFunctor
          (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)).obj
            (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)) :=
  (Scheme.Modules.verticalOpenPullbackBaseChangeIso
    (localOverlapCurveMap i j) (coordinateOverlapMap i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
    canonicalProjectiveCurveMap (curveOverlap_square_isPullback i j)).symm.app
      (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)

/-- The ambient local trivialization on chart `i`, restricted once more to
the ordered overlap `U_{ij}`.  It is the left-hand representative of the
ambient descent datum whose pullback will be compared with the curve datum. -/
def ambientTwistToOverlapLeft (d : ℤ) (i j : Fin 4) :=
  Scheme.Modules.iteratedRestrictionHom
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j) rfl
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistModule d i)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleToLocal d i)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictLeftIso d i j).hom

/-- The ambient local trivialization on chart `j`, restricted to the ordered
overlap `U_{ij}` from the right. -/
def ambientTwistToOverlapRight (d : ℤ) (i j : Fin 4) :=
  Scheme.Modules.iteratedRestrictionHom
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap_eq_right i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistModule d j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleToLocal d j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictRightIso d i j).hom

/-- The two ambient overlap restrictions differ by the prescribed twisting
transition. -/
theorem ambientTwistToOverlap_pair_compatibility
    (d : ℤ) (i j : Fin 4) :
    ambientTwistToOverlapLeft d i j ≫
        (ambientOverlapTwistIso d i j).hom =
      ambientTwistToOverlapRight d i j := by
  unfold ambientTwistToOverlapLeft
  rw [← Scheme.Modules.iteratedRestrictionHom_comp]
  simpa only [ambientTwistToOverlapRight,
    Iso.trans_hom] using
      ambientTwistPairCompatibility d i j

/-- The left ambient overlap map expressed through the unit trivializations
used by pullback to the curve. -/
def ambientTwistToOverlapLeftUnit (d : ℤ) (i j : Fin 4) :=
  Scheme.Modules.iteratedRestrictionHom
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j) rfl
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (SheafOfModules.unit (ambientChartScheme i).ringCatSheaf)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (ambientRestrictedTwistUnitIso d i).hom
    ((Scheme.Modules.restrictUnitIso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)).hom ≫
      (ambientOverlapTwistUnitIso d i j).inv)

/-- The right ambient overlap map in the same unit normalization. -/
def ambientTwistToOverlapRightUnit (d : ℤ) (i j : Fin 4) :=
  Scheme.Modules.iteratedRestrictionHom
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap_eq_right i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (SheafOfModules.unit (ambientChartScheme j).ringCatSheaf)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (ambientRestrictedTwistUnitIso d j).hom
    ((Scheme.Modules.restrictUnitIso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)).hom ≫
      (ambientOverlapTwistUnitIso d i j).inv)

theorem ambientTwistToOverlapLeftUnit_eq (d : ℤ) (i j : Fin 4) :
    ambientTwistToOverlapLeftUnit d i j = ambientTwistToOverlapLeft d i j := by
  simpa only [ambientTwistToOverlapLeftUnit, ambientTwistToOverlapLeft,
    ambientRestrictedTwistUnitIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleLocalIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictLeftIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using
      (Scheme.Modules.iteratedRestrictionHom_cancel_iso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)
        (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j) rfl
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
        (SheafOfModules.unit (ambientChartScheme i).ringCatSheaf)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistModule d i)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
        (ambientRestrictedTwistUnitIso d i).hom
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistUnitIso d i)
        ((Scheme.Modules.restrictUnitIso
            (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)).hom ≫
          (ambientOverlapTwistUnitIso d i j).inv)).symm

theorem ambientTwistToOverlapRightUnit_eq (d : ℤ) (i j : Fin 4) :
    ambientTwistToOverlapRightUnit d i j = ambientTwistToOverlapRight d i j := by
  simpa only [ambientTwistToOverlapRightUnit, ambientTwistToOverlapRight,
    ambientRestrictedTwistUnitIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleLocalIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictRightIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using
      (Scheme.Modules.iteratedRestrictionHom_cancel_iso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)
        (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap j)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap_eq_right i j)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
        (SheafOfModules.unit (ambientChartScheme j).ringCatSheaf)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistModule d j)
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
        (ambientRestrictedTwistUnitIso d j).hom
        (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientLocalTwistUnitIso d j)
        ((Scheme.Modules.restrictUnitIso
            (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight
              i j)).hom ≫
          (ambientOverlapTwistUnitIso d i j).inv)).symm

/-! ## Compatibility of base change with nested restrictions

The descent calculation uses two nested cartesian squares: an overlap inside
an affine chart, and that chart inside the global curve.  The following two
lemmas state that passing through the two squares successively is identical
to passing through their outer rectangle.  Horizontal arrows are arbitrary;
only the vertical restriction maps are open immersions, so the result applies
to the canonical closed immersion.
-/

set_option maxHeartbeats 800000 in
-- Sectionwise normalization traverses four nested presheaf restrictions.
set_option backward.isDefEq.respectTransparency false in
/-- For two vertically composable cartesian squares, the two successive
direct-image base-change identifications equal the base-change identification
for the outer rectangle, after the canonical identifications of successive
restrictions.  On sections all maps are restrictions along equal open sets,
so the assertion reduces to functoriality of the coefficient presheaf. -/
theorem verticalOpenBaseChangeIso_paste_hom
    {Q V P U X Y : Scheme}
    (r : Q ⟶ V) (q : Q ⟶ P) (k : V ⟶ U) (b : P ⟶ U)
    (iX : P ⟶ X) (iU : U ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion q] [IsOpenImmersion k]
    [IsOpenImmersion iX] [IsOpenImmersion iU]
    (Hinner : IsPullback r q k b)
    (Hchart : IsPullback b iX iU f) (M : X.Modules) :
    (Scheme.Modules.restrictFunctorComp k iU).hom.app
          ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.restrictFunctor k).map
          (Scheme.Modules.verticalOpenBaseChangeIso
            b iX iU f Hchart M).hom ≫
        (Scheme.Modules.verticalOpenBaseChangeIso
          r q k b Hinner
          ((Scheme.Modules.restrictFunctor iX).obj M)).hom ≫
        (Scheme.Modules.pushforward r).map
          ((Scheme.Modules.restrictFunctorComp q iX).inv.app M) =
      (Scheme.Modules.verticalOpenBaseChangeIso
        r (q ≫ iX) (k ≫ iU) f
        (Hinner.paste_vert Hchart) M).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.restrictFunctor_map_app,
    Scheme.Modules.pushforward_map_app]
  change
    ((Scheme.Modules.restrictFunctorComp q iX).inv.app M).app (r ⁻¹ᵁ W)
      ((Scheme.Modules.verticalOpenBaseChangeIso r q k b Hinner
          ((Scheme.Modules.restrictFunctor iX).obj M)).hom.app W
        ((Scheme.Modules.verticalOpenBaseChangeIso b iX iU f Hchart M).hom.app
          (k ''ᵁ W)
          (((Scheme.Modules.restrictFunctorComp k iU).hom.app
            ((Scheme.Modules.pushforward f).obj M)).app W x))) =
      (Scheme.Modules.verticalOpenBaseChangeIso
        r (q ≫ iX) (k ≫ iU) f
        (Hinner.paste_vert Hchart) M).hom.app W x
  let x0 := ((Scheme.Modules.restrictFunctorComp k iU).hom.app
    ((Scheme.Modules.pushforward f).obj M)).app W x
  have houter := Scheme.Modules.verticalOpenBaseChangeIso_hom_app_apply
    b iX iU f Hchart M (k ''ᵁ W) x0
  have hinner := Scheme.Modules.verticalOpenBaseChangeIso_hom_app_apply
    r q k b Hinner ((Scheme.Modules.restrictFunctor iX).obj M) W
      ((Scheme.Modules.verticalOpenBaseChangeIso b iX iU f Hchart M).hom.app
        (k ''ᵁ W) x0)
  have hcomposite := Scheme.Modules.verticalOpenBaseChangeIso_hom_app_apply
    r (q ≫ iX) (k ≫ iU) f (Hinner.paste_vert Hchart) M W x
  rw [hinner, houter, hcomposite]
  simp only [x0, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app]
  change M.presheaf.map _
      (M.presheaf.map _
        (M.presheaf.map _ (M.presheaf.map _ x))) =
    M.presheaf.map _ x
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    ← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The iterated mates calculation expands two adjunctions and both pasted
-- base-change squares.
set_option synthInstance.maxHeartbeats 200000 in
-- The nested pullback-module objects create a large instance-search term.
/-- Pullback base change carries an iterated coefficient restriction through
two nested cartesian squares to the corresponding iterated restriction on the
opposite side.  Equivalently, the pullback comparison for the outer rectangle
is the composite of the comparisons for its two constituent squares.

This is the form needed for descent: `e` is the chartwise coefficient map and
`u` is its further restriction to an overlap.  The proof takes mates of the
pullback squares, applies the preceding direct-image pasting law, and then
uses naturality to reinsert `e` and `u`. -/
theorem verticalOpenPullbackBaseChange_iteratedRestrictionHom
    {Q V P U X Y : Scheme}
    (r : Q ⟶ V) (q : Q ⟶ P) (k : V ⟶ U) (b : P ⟶ U)
    (iX : P ⟶ X) (iU : U ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion q] [IsOpenImmersion k]
    [IsOpenImmersion iX] [IsOpenImmersion iU]
    (Hinner : IsPullback r q k b)
    (Hchart : IsPullback b iX iU f)
    (F : Y.Modules) (H : U.Modules) (K : V.Modules)
    (e : (Scheme.Modules.restrictFunctor iU).obj F ⟶ H)
    (u : (Scheme.Modules.restrictFunctor k).obj H ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom q iX (q ≫ iX) rfl
        ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback b).obj H)
        ((Scheme.Modules.pullback r).obj K)
        ((Scheme.Modules.verticalOpenPullbackBaseChangeIso
            b iX iU f Hchart).inv.app F ≫
          (Scheme.Modules.pullback b).map e)
        ((Scheme.Modules.verticalOpenPullbackBaseChangeIso
            r q k b Hinner).inv.app H ≫
          (Scheme.Modules.pullback r).map u) =
    (Scheme.Modules.verticalOpenPullbackBaseChangeIso
          r (q ≫ iX) (k ≫ iU) f
          (Hinner.paste_vert Hchart)).inv.app F ≫
        (Scheme.Modules.pullback r).map
          (Scheme.Modules.iteratedRestrictionHom
            k iU (k ≫ iU) rfl F H K e u) := by
  let Souter := Scheme.Modules.verticalOpenPullbackBaseChangeSquare
    b iX iU f Hchart
  let Sinner := Scheme.Modules.verticalOpenPullbackBaseChangeSquare
    r q k b Hinner
  let Scomposite := Scheme.Modules.verticalOpenPullbackBaseChangeSquare
    r (q ≫ iX) (k ≫ iU) f (Hinner.paste_vert Hchart)
  have hmate :
      mateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction f)
          (Scheme.Modules.pullbackPushforwardAdjunction r)
          ((Scomposite.whiskerTop
            (Scheme.Modules.restrictFunctorComp k iU).inv).whiskerBottom
              (Scheme.Modules.restrictFunctorComp q iX).hom) =
        ((mateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction f)
          (Scheme.Modules.pullbackPushforwardAdjunction r)
          Scomposite).whiskerRight
            (Scheme.Modules.restrictFunctorComp k iU).inv).whiskerLeft
              (Scheme.Modules.restrictFunctorComp q iX).hom := by
    apply TwoSquare.ext
    intro M
    simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app,
      Functor.id_obj, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerRight_app,
      TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app,
      Category.assoc, Functor.map_comp, Functor.comp_map,
      Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
      Adjunction.unit_naturality_assoc, TwoSquare.whiskerLeft_app,
      TwoSquare.whiskerRight_app, NatIso.cancel_natIso_inv_left]
    slice_lhs 3 4 => rw [← (Scheme.Modules.pushforward r).map_comp]
    slice_rhs 3 4 => rw [← (Scheme.Modules.pushforward r).map_comp]
    rw [(Scheme.Modules.restrictFunctorComp q iX).hom.naturality]
    rfl
  have hmateComposite (M : X.Modules) :
      (mateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction r)
        Scomposite).app M =
      (Scheme.Modules.verticalOpenBaseChangeIso
        r (q ≫ iX) (k ≫ iU) f
        (Hinner.paste_vert Hchart) M).hom := by
    simpa only [Scomposite] using
      (Scheme.Modules.verticalOpenPullbackBaseChangeSquare_mate_app
        r (q ≫ iX) (k ≫ iU) f
        (Hinner.paste_vert Hchart) M)
  have hsquares :
      TwoSquare.hComp Souter Sinner =
        (Scomposite.whiskerTop
          (Scheme.Modules.restrictFunctorComp k iU).inv).whiskerBottom
            (Scheme.Modules.restrictFunctorComp q iX).hom := by
    apply (mateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction r)).injective
    rw [show mateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction r)
        (TwoSquare.hComp Souter Sinner) =
      TwoSquare.vComp
        (mateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction f)
          (Scheme.Modules.pullbackPushforwardAdjunction b) Souter)
        (mateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction b)
          (Scheme.Modules.pullbackPushforwardAdjunction r) Sinner) by
      exact mateEquiv_vcomp _ _ _ _ _]
    rw [hmate]
    apply TwoSquare.ext
    intro M
    unfold TwoSquare.whiskerRight TwoSquare.whiskerLeft
    simp only [TwoSquare.vComp_app, Functor.comp_obj, Category.assoc]
    rw [Scheme.Modules.verticalOpenPullbackBaseChangeSquare_mate_app,
      Scheme.Modules.verticalOpenPullbackBaseChangeSquare_mate_app]
    change
      (Scheme.Modules.restrictFunctor k).map
            (Scheme.Modules.verticalOpenBaseChangeIso
              b iX iU f Hchart M).hom ≫
          (Scheme.Modules.verticalOpenBaseChangeIso
            r q k b Hinner
            ((Scheme.Modules.restrictFunctor iX).obj M)).hom =
        (Scheme.Modules.restrictFunctorComp k iU).inv.app
              ((Scheme.Modules.pushforward f).obj M) ≫
          (mateEquiv
            (Scheme.Modules.pullbackPushforwardAdjunction f)
            (Scheme.Modules.pullbackPushforwardAdjunction r)
            Scomposite).app M ≫
          (Scheme.Modules.pushforward r).map
            ((Scheme.Modules.restrictFunctorComp q iX).hom.app M)
    rw [hmateComposite]
    apply (cancel_epi ((Scheme.Modules.restrictFunctorComp k iU).hom.app
      ((Scheme.Modules.pushforward f).obj M))).1
    apply (cancel_mono ((Scheme.Modules.pushforward r).map
      ((Scheme.Modules.restrictFunctorComp q iX).inv.app M))).1
    simpa using verticalOpenBaseChangeIso_paste_hom
      r q k b iX iU f Hinner Hchart M
  have hnat :
      (Scheme.Modules.restrictFunctor q).map
            ((Scheme.Modules.pullback b).map e) ≫
          (Scheme.Modules.verticalOpenPullbackBaseChangeIso
            r q k b Hinner).inv.app H =
        (Scheme.Modules.verticalOpenPullbackBaseChangeIso
            r q k b Hinner).inv.app
              ((Scheme.Modules.restrictFunctor iU).obj F) ≫
          (Scheme.Modules.pullback r).map
            ((Scheme.Modules.restrictFunctor k).map e) := by
    simpa only [Functor.comp_map] using
      (Scheme.Modules.verticalOpenPullbackBaseChangeIso
        r q k b Hinner).inv.naturality e
  have hpasteHom := congr_app hsquares F
  change
    (Scheme.Modules.verticalOpenPullbackBaseChangeIso
          r q k b Hinner).hom.app
            ((Scheme.Modules.restrictFunctor iU).obj F) ≫
        (Scheme.Modules.restrictFunctor q).map
          ((Scheme.Modules.verticalOpenPullbackBaseChangeIso
            b iX iU f Hchart).hom.app F) =
      (Scheme.Modules.pullback r).map
            ((Scheme.Modules.restrictFunctorComp k iU).inv.app F) ≫
        (Scheme.Modules.verticalOpenPullbackBaseChangeIso
          r (q ≫ iX) (k ≫ iU) f
          (Hinner.paste_vert Hchart)).hom.app F ≫
        (Scheme.Modules.restrictFunctorComp q iX).hom.app
          ((Scheme.Modules.pullback f).obj F) at hpasteHom
  have hpasteInv :
      (Scheme.Modules.restrictFunctor q).map
            ((Scheme.Modules.verticalOpenPullbackBaseChangeIso
              b iX iU f Hchart).inv.app F) ≫
          (Scheme.Modules.verticalOpenPullbackBaseChangeIso
            r q k b Hinner).inv.app
              ((Scheme.Modules.restrictFunctor iU).obj F) =
        (Scheme.Modules.restrictFunctorComp q iX).inv.app
              ((Scheme.Modules.pullback f).obj F) ≫
          (Scheme.Modules.verticalOpenPullbackBaseChangeIso
            r (q ≫ iX) (k ≫ iU) f
            (Hinner.paste_vert Hchart)).inv.app F ≫
          (Scheme.Modules.pullback r).map
            ((Scheme.Modules.restrictFunctorComp k iU).hom.app F) := by
    rw [← IsIso.inv_eq_inv]
    simpa only [Category.assoc, IsIso.inv_comp, ← Functor.map_inv,
      NatIso.inv_hom_app, NatIso.inv_inv_app] using hpasteHom
  rw [Scheme.Modules.iteratedRestrictionHom_middle_comp]
  rw [reassoc_of% hnat]
  unfold Scheme.Modules.iteratedRestrictionHom
  rw [Scheme.Modules.restrictFunctorCongr_refl_inv_app,
    Scheme.Modules.restrictFunctorCongr_refl_inv_app]
  simp only [Category.id_comp, Functor.map_comp]
  rw [reassoc_of% hpasteInv]
  rw [Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 800000 in
-- Taking mates twice and normalizing structure-module maps requires the
-- expanded Beck--Chevalley comparison.
/-- Beck--Chevalley for a square with open vertical arrows preserves the
canonical trivialization of the pulled-back structure module. -/
theorem verticalOpenPullbackBaseChangeIso_unit
    {Q V P U : Scheme}
    (r : Q ⟶ V) (q : Q ⟶ P) (k : V ⟶ U) (b : P ⟶ U)
    [IsOpenImmersion q] [IsOpenImmersion k]
    (H : IsPullback r q k b) :
    (Scheme.Modules.verticalOpenPullbackBaseChangeIso r q k b H).inv.app
          (SheafOfModules.unit U.ringCatSheaf) ≫
        (Scheme.Modules.pullback r).map
          (Scheme.Modules.restrictUnitIso k).hom ≫
        (Scheme.Modules.pullbackUnitIsoOfScheme r).hom =
      (Scheme.Modules.restrictFunctor q).map
          (Scheme.Modules.pullbackUnitIsoOfScheme b).hom ≫
        (Scheme.Modules.restrictUnitIso q).hom := by
  apply (cancel_epi
    ((Scheme.Modules.verticalOpenPullbackBaseChangeIso r q k b H).hom.app
      (SheafOfModules.unit U.ringCatSheaf))).1
  rw [Iso.hom_inv_id_app_assoc]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  have hr :
      ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv _ _)
          (Scheme.Modules.pullbackUnitIsoOfScheme r).hom =
        Scheme.Modules.unitToPushforwardUnit r := by
    change
      ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv _ _)
          (SheafOfModules.pullbackObjUnitToUnit r.toRingCatSheafHom) = _
    exact
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        r.toRingCatSheafHom
  have hrhs :
      ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv _ _)
          ((Scheme.Modules.verticalOpenPullbackBaseChangeIso r q k b H).hom.app
                (SheafOfModules.unit U.ringCatSheaf) ≫
            (Scheme.Modules.restrictFunctor q).map
                (Scheme.Modules.pullbackUnitIsoOfScheme b).hom ≫
              (Scheme.Modules.restrictUnitIso q).hom) =
        (Scheme.Modules.restrictFunctor k).map
              (Scheme.Modules.unitToPushforwardUnit b) ≫
          (Scheme.Modules.verticalOpenBaseChangeIso r q k b H
            (SheafOfModules.unit P.ringCatSheaf)).hom ≫
          (Scheme.Modules.pushforward r).map
            (Scheme.Modules.restrictUnitIso q).hom := by
    rw [Adjunction.homEquiv_naturality_right]
    change
      (Scheme.Modules.pullbackPushforwardAdjunction r).unit.app
            ((Scheme.Modules.restrictFunctor k).obj
              (SheafOfModules.unit U.ringCatSheaf)) ≫
          (Scheme.Modules.pushforward r).map
            ((Scheme.Modules.verticalOpenPullbackBaseChangeIso
              r q k b H).hom.app (SheafOfModules.unit U.ringCatSheaf)) ≫
          (Scheme.Modules.pushforward r).map
            ((Scheme.Modules.restrictFunctor q).map
                (Scheme.Modules.pullbackUnitIsoOfScheme b).hom ≫
              (Scheme.Modules.restrictUnitIso q).hom) = _
    rw [← reassoc_of%
      Scheme.Modules.pullbackPushforwardAdjunction_unit_verticalOpenBaseChange
        r q k b H]
    simp only [Functor.map_comp]
    rw [← Scheme.Modules.verticalOpenBaseChangeMateSquare_app
      r q k b H]
    rw [← Scheme.Modules.verticalOpenBaseChangeMateSquare_app
      r q k b H]
    have hnat := (Scheme.Modules.verticalOpenBaseChangeMateSquare
      r q k b H).naturality
        (Scheme.Modules.pullbackUnitIsoOfScheme b).hom
    simp only [Functor.comp_map] at hnat
    rw [← reassoc_of% hnat]
    have hb :
        (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
              (SheafOfModules.unit U.ringCatSheaf) ≫
            (Scheme.Modules.pushforward b).map
              (Scheme.Modules.pullbackUnitIsoOfScheme b).hom =
          Scheme.Modules.unitToPushforwardUnit b := by
      change
        ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _)
            (Scheme.Modules.pullbackUnitIsoOfScheme b).hom = _
      exact
        SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
          b.toRingCatSheafHom
    rw [← (Scheme.Modules.restrictFunctor k).map_comp_assoc, hb]
  have hunit := Scheme.Modules.unitToPushforwardUnit_verticalOpenBaseChange
    r q k b H
  rw [hr, hrhs]
  apply (cancel_epi (Scheme.Modules.restrictUnitIso k).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hunit.symm

/-- Inserting and then cancelling any chosen trivialization of the upper
structure module does not change the Beck--Chevalley unit comparison. -/
theorem verticalOpenPullbackBaseChangeIso_unit_through_iso
    {Q V P U : Scheme}
    (r : Q ⟶ V) (q : Q ⟶ P) (k : V ⟶ U) (b : P ⟶ U)
    [IsOpenImmersion q] [IsOpenImmersion k]
    (H : IsPullback r q k b) (K : V.Modules)
    (e : K ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.verticalOpenPullbackBaseChangeIso r q k b H).inv.app
          (SheafOfModules.unit U.ringCatSheaf) ≫
        (Scheme.Modules.pullback r).map
            ((Scheme.Modules.restrictUnitIso k).hom ≫ e.inv) ≫
        (Scheme.Modules.pullback r).map e.hom ≫
        (Scheme.Modules.pullbackUnitIsoOfScheme r).hom =
      (Scheme.Modules.restrictFunctor q).map
          (Scheme.Modules.pullbackUnitIsoOfScheme b).hom ≫
        (Scheme.Modules.restrictUnitIso q).hom := by
  rw [← (Scheme.Modules.pullback r).map_comp_assoc]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact verticalOpenPullbackBaseChangeIso_unit r q k b H

/-! ## Agreement of the local comparisons on overlaps

We now apply the abstract pasting law to the canonical curve.  It identifies
the restriction of a curve chart trivialization with the pullback of the
corresponding ambient overlap trivialization.  The ambient cocycle identity
can therefore be transported unchanged to the curve-side Čech diagram.
-/

/-- On `C_{ij}`, the comparison defined from chart `i` equals the pullback of
the ambient trivialization on `U_{ij}`, followed by the fixed identification
with the curve overlap module.  This is the left-hand overlap identity used
to prove equality of the two Čech arrows. -/
@[reassoc]
theorem curvePullbackTwistLocalIso_restrict_left
    (d : ℤ) (i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToLeft i j) (coordinateChartMap i)
        (coordinateOverlapMap i j) rfl
        (curvePullbackTwist d)
        (SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf)
        (coordinateOverlapTwistModule d i j)
        (curvePullbackTwistCoordinateLocalIso d i).hom
        ((Scheme.Modules.restrictUnitIso
            (coordinateOverlapToLeft i j)).hom ≫
          (coordinateOverlapTwistUnitIso d i j).inv) =
        (curvePullbackTwistOverlapBaseChangeIso d i j).hom ≫
        (Scheme.Modules.pullback (localOverlapCurveMap i j)).map
          (ambientTwistToOverlapLeftUnit d i j) ≫
        (curvePullbackTwistOverlapIso d i j).hom := by
  let Hchart := coordinateCurveChart_square_isPullback i
  have h := verticalOpenPullbackBaseChange_iteratedRestrictionHom
    (localOverlapCurveMap i j) (coordinateOverlapToLeft i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)
    (coordinateLocalCurveMap i) (coordinateChartMap i)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap i)
    canonicalProjectiveCurveMap
    (localOverlapCurveMap_left_square_isPullback i j) Hchart
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (SheafOfModules.unit (ambientChartScheme i).ringCatSheaf)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (ambientRestrictedTwistUnitIso d i).hom
    ((Scheme.Modules.restrictUnitIso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)).hom ≫
      (ambientOverlapTwistUnitIso d i j).inv)
  have h' := congrArg (fun z => z ≫
    (curvePullbackTwistOverlapIso d i j).hom) h
  have hroute := congrArg (fun z => z ≫
    (coordinateOverlapTwistUnitIso d i j).inv)
    (verticalOpenPullbackBaseChangeIso_unit
    (localOverlapCurveMap i j) (coordinateOverlapToLeft i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToLeft i j)
    (coordinateLocalCurveMap i)
    (localOverlapCurveMap_left_square_isPullback i j))
  simp only [Category.assoc] at hroute
  conv_lhs at h' => rw [← Scheme.Modules.iteratedRestrictionHom_comp]
  simp only [curvePullbackTwistOverlapIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] at h'
  rw [← (Scheme.Modules.pullback
    (localOverlapCurveMap i j)).map_comp_assoc] at h'
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
  simp only [Iso.symm_hom] at h'
  rw [hroute] at h'
  conv_lhs at h' => rw [← Scheme.Modules.iteratedRestrictionHom_middle_comp]
  simpa only [curvePullbackTwist, curvePullbackTwistCoordinateLocalIso,
    ambientRestrictedTwistUnitIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleLocalIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictLeftIso,
    curvePullbackTwistOverlapBaseChangeIso,
    curvePullbackTwistOverlapIso, ambientTwistToOverlapLeftUnit,
    coordinateOverlapMap,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap,
    Iso.trans_hom, Iso.symm_hom, NatIso.inv_hom_app,
    natIso_symm_app_hom_eq_inv_app,
    asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using h'

/-- The analogous comparison for restriction from chart `j` to the right
projection of `C_{ij}`. -/
@[reassoc]
theorem curvePullbackTwistLocalIso_restrict_right
    (d : ℤ) (i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToRight i j) (coordinateChartMap j)
        (coordinateOverlapMap i j) (coordinateOverlapMap_eq_right i j)
        (curvePullbackTwist d)
        (SheafOfModules.unit (coordinateChartScheme j).ringCatSheaf)
        (coordinateOverlapTwistModule d i j)
        (curvePullbackTwistCoordinateLocalIso d j).hom
        ((Scheme.Modules.restrictUnitIso
            (coordinateOverlapToRight i j)).hom ≫
          (coordinateOverlapTwistUnitIso d i j).inv) =
        (curvePullbackTwistOverlapBaseChangeIso d i j).hom ≫
        (Scheme.Modules.pullback (localOverlapCurveMap i j)).map
          (ambientTwistToOverlapRightUnit d i j) ≫
        (curvePullbackTwistOverlapIso d i j).hom := by
  apply (cancel_epi
    ((Scheme.Modules.restrictFunctorCongr
      (coordinateOverlapMap_eq_right i j)).hom.app
        (curvePullbackTwist d))).1
  let Hchart := coordinateCurveChart_square_isPullback j
  have h := verticalOpenPullbackBaseChange_iteratedRestrictionHom
    (localOverlapCurveMap i j) (coordinateOverlapToRight i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)
    (coordinateLocalCurveMap j) (coordinateChartMap j)
    (RationalPointsN25QuotientTwoAmbientTwistingDescent.ambientChartMap j)
    canonicalProjectiveCurveMap
    (localOverlapCurveMap_right_square_isPullback i j) Hchart
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
    (SheafOfModules.unit (ambientChartScheme j).ringCatSheaf)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafCharts.ambientOverlapTwistModule d i j)
    (ambientRestrictedTwistUnitIso d j).hom
    ((Scheme.Modules.restrictUnitIso
        (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)).hom ≫
      (ambientOverlapTwistUnitIso d i j).inv)
  have h' := congrArg (fun z => z ≫
    (curvePullbackTwistOverlapIso d i j).hom) h
  have hroute := congrArg (fun z => z ≫
    (coordinateOverlapTwistUnitIso d i j).inv)
    (verticalOpenPullbackBaseChangeIso_unit
    (localOverlapCurveMap i j) (coordinateOverlapToRight i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight i j)
    (coordinateLocalCurveMap j)
    (localOverlapCurveMap_right_square_isPullback i j))
  simp only [Category.assoc] at hroute
  conv_lhs at h' => rw [← Scheme.Modules.iteratedRestrictionHom_comp]
  simp only [curvePullbackTwistOverlapIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] at h'
  rw [← (Scheme.Modules.pullback
    (localOverlapCurveMap i j)).map_comp_assoc] at h'
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
  simp only [Iso.symm_hom] at h'
  rw [hroute] at h'
  conv_lhs at h' => rw [← Scheme.Modules.iteratedRestrictionHom_middle_comp]
  have hBC := verticalOpenPullbackBaseChangeIso_congr
    (r := localOverlapCurveMap i j)
    (q := coordinateOverlapToRight i j ≫ coordinateChartMap j)
    (q' := coordinateOverlapMap i j)
    (k := RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapToRight
      i j ≫ ambientChartMap j)
    (k' := RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap i j)
    (b := canonicalProjectiveCurveMap)
    (coordinateOverlapMap_eq_right i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap_eq_right i j)
    ((localOverlapCurveMap_right_square_isPullback i j).paste_vert Hchart)
    (curveOverlap_square_isPullback i j)
    (RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModule d)
  unfold ambientTwistToOverlapRightUnit
  unfold Scheme.Modules.iteratedRestrictionHom
  unfold curvePullbackTwist curvePullbackTwistOverlapBaseChangeIso
  simp only [Functor.map_comp, Category.assoc,
    natIso_symm_app_hom_eq_inv_app]
  rw [reassoc_of% hBC]
  simpa only [curvePullbackTwist, curvePullbackTwistCoordinateLocalIso,
    Scheme.Modules.iteratedRestrictionHom,
    Scheme.Modules.restrictFunctorCongr_refl_inv_app,
    ambientRestrictedTwistUnitIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.globalTwistModuleLocalIso,
    RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientRestrictRightIso,
    curvePullbackTwistOverlapBaseChangeIso,
    curvePullbackTwistOverlapIso, ambientTwistToOverlapRightUnit,
    ← coordinateOverlapMap_eq_right,
    ← RationalPointsN25QuotientTwoAmbientTwistingSheafGluing.ambientOverlapMap_eq_right,
    Iso.trans_hom, Iso.symm_hom, NatIso.inv_hom_app,
    natIso_symm_app_hom_eq_inv_app,
    asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Category.id_comp,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc] using h'

/-! ## Descent through the Čech equalizer

Each chartwise comparison is transposed across restriction--pushforward and
assembled into a map to the product of chart pushforwards.  Equality of its
two overlap restrictions is precisely the condition for this map to factor
through the equalizer defining the globally glued twist.
-/

/-- The product of the four transposed chartwise comparisons from the ambient
pullback twist to the source of the curve Čech diagram. -/
def curvePullbackTwistToCechSource (d : ℤ) :
    curvePullbackTwist d ⟶ twistCechSource d :=
  Pi.lift fun i ↦
    (Scheme.Modules.restrictAdjunction
      (coordinateChartMap i)).unit.app (curvePullbackTwist d) ≫
    (Scheme.Modules.pushforward (coordinateChartMap i)).map
      (curvePullbackTwistCoordinateChartIso d i).hom

/-- Projecting the product map to chart `i` recovers the transpose of the
local comparison on that chart. -/
@[reassoc]
theorem curvePullbackTwistToCechSource_π (d : ℤ) (i : Fin 4) :
    curvePullbackTwistToCechSource d ≫
        Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i =
      (Scheme.Modules.restrictAdjunction
        (coordinateChartMap i)).unit.app (curvePullbackTwist d) ≫
      (Scheme.Modules.pushforward (coordinateChartMap i)).map
        (curvePullbackTwistCoordinateChartIso d i).hom := by
  unfold curvePullbackTwistToCechSource
  exact Pi.lift_π _ i

/-- The four chartwise comparisons have equal restrictions along the two
projections of every ordered double intersection.  Hence they form a descent
datum for the curve-side twist. -/
theorem curvePullbackTwistToCechSource_compatibility (d : ℤ) :
    curvePullbackTwistToCechSource d ≫ twistCechLeft d =
      curvePullbackTwistToCechSource d ≫ twistCechRight d := by
  apply Pi.hom_ext _ _
  intro p
  simp only [Category.assoc]
  unfold twistCechLeft twistCechRight
  rw [Pi.lift_π, Pi.lift_π]
  rw [curvePullbackTwistToCechSource_π_assoc,
    curvePullbackTwistToCechSource_π_assoc]
  apply (((Scheme.Modules.restrictAdjunction
    (coordinateOverlapMap p.1 p.2)).homEquiv
      (curvePullbackTwist d)
      (coordinateOverlapTwistModule d p.1 p.2)).symm).injective
  unfold pushforwardRestrictionHom
  rw [Scheme.Modules.pushforwardRestrictionHomOfHom_transpose,
    Scheme.Modules.pushforwardRestrictionHomOfHom_transpose]
  change
    Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToLeft p.1 p.2) (coordinateChartMap p.1)
        (coordinateOverlapMap p.1 p.2) rfl
        (curvePullbackTwist d) (coordinateLocalTwistModule d p.1)
        (coordinateOverlapTwistModule d p.1 p.2)
        (curvePullbackTwistCoordinateChartIso d p.1).hom
        (coordinateRestrictLeftIso d p.1 p.2 ≪≫
          coordinateOverlapTwistIso d p.1 p.2).hom =
      Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToRight p.1 p.2) (coordinateChartMap p.2)
        (coordinateOverlapMap p.1 p.2)
        (coordinateOverlapMap_eq_right p.1 p.2)
        (curvePullbackTwist d) (coordinateLocalTwistModule d p.2)
        (coordinateOverlapTwistModule d p.1 p.2)
        (curvePullbackTwistCoordinateChartIso d p.2).hom
        (coordinateRestrictRightIso d p.1 p.2).hom
  have hleft :=
    Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (coordinateOverlapToLeft p.1 p.2) (coordinateChartMap p.1)
      (coordinateOverlapMap p.1 p.2) rfl
      (curvePullbackTwist d)
      (SheafOfModules.unit (coordinateChartScheme p.1).ringCatSheaf)
      (coordinateLocalTwistModule d p.1)
      (coordinateOverlapTwistModule d p.1 p.2)
      (curvePullbackTwistCoordinateLocalIso d p.1).hom
      (coordinateLocalTwistUnitIso d p.1)
      ((Scheme.Modules.restrictUnitIso
          (coordinateOverlapToLeft p.1 p.2)).hom ≫
        (coordinateOverlapTwistUnitIso d p.1 p.2).inv ≫
        (coordinateOverlapTwistIso d p.1 p.2).hom)
  have hright :=
    Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (coordinateOverlapToRight p.1 p.2) (coordinateChartMap p.2)
      (coordinateOverlapMap p.1 p.2)
      (coordinateOverlapMap_eq_right p.1 p.2)
      (curvePullbackTwist d)
      (SheafOfModules.unit (coordinateChartScheme p.2).ringCatSheaf)
      (coordinateLocalTwistModule d p.2)
      (coordinateOverlapTwistModule d p.1 p.2)
      (curvePullbackTwistCoordinateLocalIso d p.2).hom
      (coordinateLocalTwistUnitIso d p.2)
      ((Scheme.Modules.restrictUnitIso
          (coordinateOverlapToRight p.1 p.2)).hom ≫
        (coordinateOverlapTwistUnitIso d p.1 p.2).inv)
  calc
    _ = Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToLeft p.1 p.2) (coordinateChartMap p.1)
        (coordinateOverlapMap p.1 p.2) rfl
        (curvePullbackTwist d)
        (SheafOfModules.unit (coordinateChartScheme p.1).ringCatSheaf)
        (coordinateOverlapTwistModule d p.1 p.2)
        (curvePullbackTwistCoordinateLocalIso d p.1).hom
        ((Scheme.Modules.restrictUnitIso
            (coordinateOverlapToLeft p.1 p.2)).hom ≫
          (coordinateOverlapTwistUnitIso d p.1 p.2).inv ≫
          (coordinateOverlapTwistIso d p.1 p.2).hom) := by
      simp only [curvePullbackTwistCoordinateChartIso, coordinateRestrictLeftIso,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc]
      exact hleft
    _ = Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToRight p.1 p.2) (coordinateChartMap p.2)
        (coordinateOverlapMap p.1 p.2)
        (coordinateOverlapMap_eq_right p.1 p.2)
        (curvePullbackTwist d)
        (SheafOfModules.unit (coordinateChartScheme p.2).ringCatSheaf)
        (coordinateOverlapTwistModule d p.1 p.2)
          (curvePullbackTwistCoordinateLocalIso d p.2).hom
        ((Scheme.Modules.restrictUnitIso
            (coordinateOverlapToRight p.1 p.2)).hom ≫
          (coordinateOverlapTwistUnitIso d p.1 p.2).inv) := by
      have hsplit := Scheme.Modules.iteratedRestrictionHom_comp
          (q := coordinateOverlapToLeft p.1 p.2)
          (a := coordinateChartMap p.1)
          (g := coordinateOverlapMap p.1 p.2)
          (hq := rfl)
          (F := curvePullbackTwist d)
          (H := SheafOfModules.unit
            (coordinateChartScheme p.1).ringCatSheaf)
          (K := coordinateOverlapTwistModule d p.1 p.2)
          (L := coordinateOverlapTwistModule d p.1 p.2)
          (e₁ := (curvePullbackTwistCoordinateLocalIso d p.1).hom)
          (e₂ := (Scheme.Modules.restrictUnitIso
            (coordinateOverlapToLeft p.1 p.2)).hom ≫
            (coordinateOverlapTwistUnitIso d p.1 p.2).inv)
          (u := (coordinateOverlapTwistIso d p.1 p.2).hom)
      simp only [Category.assoc] at hsplit
      rw [hsplit]
      rw [curvePullbackTwistLocalIso_restrict_left_assoc]
      rw [ambientTwistToOverlapLeftUnit_eq]
      rw [← curvePullbackTwistOverlapIso_transition]
      rw [← (Scheme.Modules.pullback
        (localOverlapCurveMap p.1 p.2)).map_comp_assoc]
      rw [ambientTwistToOverlap_pair_compatibility]
      rw [← ambientTwistToOverlapRightUnit_eq]
      rw [← curvePullbackTwistLocalIso_restrict_right]
    _ = _ := by
      simp only [curvePullbackTwistCoordinateChartIso, coordinateRestrictRightIso,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      exact hright.symm

/-- The compatible chartwise comparison factors through the equalizer that
defines the curve-side global twist. -/
def curvePullbackTwistToGlobalTwist (d : ℤ) :
    curvePullbackTwist d ⟶ globalTwistModule d :=
  equalizer.lift (curvePullbackTwistToCechSource d)
    (curvePullbackTwistToCechSource_compatibility d)

/-- Forgetting the target equalizer condition recovers the product of the
four chartwise comparison maps. -/
@[reassoc]
theorem curvePullbackTwistToGlobalTwist_comp_ι (d : ℤ) :
    curvePullbackTwistToGlobalTwist d ≫
        equalizer.ι (twistCechLeft d) (twistCechRight d) =
      curvePullbackTwistToCechSource d := by
  exact equalizer.lift_ι _ _

/-- On every coordinate chart, the global comparison is the local
base-change trivialization used to construct it. -/
theorem curvePullbackTwistToGlobalTwist_restrict_comp_evaluation
    (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          (curvePullbackTwistToGlobalTwist d) ≫
        globalTwistModuleToLocal d i =
      (curvePullbackTwistCoordinateChartIso d i).hom := by
  apply ((Scheme.Modules.restrictAdjunction
    (coordinateChartMap i)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [globalTwistModuleToLocal, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  rw [curvePullbackTwistToGlobalTwist_comp_ι_assoc]
  exact curvePullbackTwistToCechSource_π d i

/-- Restriction of the global comparison to every standard coordinate chart
is an isomorphism. -/
theorem curvePullbackTwistToGlobalTwist_restrict_isIso
    (d : ℤ) (i : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
      (curvePullbackTwistToGlobalTwist d)) := by
  letI := globalTwistModuleToLocal_isIso d i
  haveI : IsIso
      ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          (curvePullbackTwistToGlobalTwist d) ≫
        globalTwistModuleToLocal d i) := by
    rw [curvePullbackTwistToGlobalTwist_restrict_comp_evaluation]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
      (curvePullbackTwistToGlobalTwist d))
    (globalTwistModuleToLocal d i)

set_option synthInstance.maxHeartbeats 200000 in
-- Stalkwise isomorphy uses the coordinate cover and several transported
-- module instances simultaneously.
/-- The pullback of the ambient projective twist is the effective curve-side
Čech twist.  Isomorphy is checked on stalks after choosing a coordinate
chart containing each point. -/
theorem curvePullbackTwistToGlobalTwist_isIso (d : ℤ) :
    IsIso (curvePullbackTwistToGlobalTwist d) := by
  let F := SheafOfModules.toSheaf
    CanonicalProjectiveCurve25Two.ringCatSheaf
  have hStalk (x : CanonicalProjectiveCurve25Two) :
      IsIso
        ((Scheme.Modules.toPresheaf CanonicalProjectiveCurve25Two ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (curvePullbackTwistToGlobalTwist d)) := by
    let i := coordinateAffineOpenCover.idx x
    have hx := coordinateAffineOpenCover.covers x
    change x ∈ Set.range (coordinateChartMap i) at hx
    obtain ⟨y, hy⟩ := hx
    let G := Scheme.Modules.toPresheaf (coordinateChartScheme i) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat y
    have hRestrictedStalk : IsIso
        ((Scheme.Modules.restrictFunctor (coordinateChartMap i) ⋙ G).map
          (curvePullbackTwistToGlobalTwist d)) := by
      change IsIso (G.map
        ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          (curvePullbackTwistToGlobalTwist d)))
      letI := curvePullbackTwistToGlobalTwist_restrict_isIso d i
      infer_instance
    have hCurveStalk : IsIso
        ((Scheme.Modules.toPresheaf CanonicalProjectiveCurve25Two ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (coordinateChartMap i y)).map
              (curvePullbackTwistToGlobalTwist d)) :=
      (CategoryTheory.NatIso.isIso_map_iff
        (Scheme.Modules.restrictStalkNatIso (coordinateChartMap i) y)
          (curvePullbackTwistToGlobalTwist d)).mp hRestrictedStalk
    exact hy ▸ hCurveStalk
  have hUnderlyingStalk (x : CanonicalProjectiveCurve25Two) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (F.map (curvePullbackTwistToGlobalTwist d)).hom) := by
    change IsIso
      ((Scheme.Modules.toPresheaf CanonicalProjectiveCurve25Two ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (curvePullbackTwistToGlobalTwist d))
    exact hStalk x
  letI : ∀ x : CanonicalProjectiveCurve25Two,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (F.map (curvePullbackTwistToGlobalTwist d)).hom) := hUnderlyingStalk
  haveI hUnderlying : IsIso (F.map (curvePullbackTwistToGlobalTwist d)) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (F.map (curvePullbackTwistToGlobalTwist d))
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso
    ((F.map (curvePullbackTwistToGlobalTwist d)).hom.app (.op U))
  infer_instance

/-- The canonical global identification between the two constructions of
the twist on the canonical curve. -/
def curvePullbackTwistGlobalIso (d : ℤ) :
    curvePullbackTwist d ≅ globalTwistModule d := by
  letI := curvePullbackTwistToGlobalTwist_isIso d
  exact asIso (curvePullbackTwistToGlobalTwist d)

end MazurProof.RationalPointsN25QuotientTwoAmbientTwistGlobalComparison
