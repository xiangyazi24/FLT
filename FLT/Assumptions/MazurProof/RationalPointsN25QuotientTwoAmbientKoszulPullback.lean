import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientKoszulShifted

/-!
# Geometric targets for the shifted N25 ambient Koszul quotients

The coefficient `globalTwistModule d` represents the ambient line bundle
`O(-d)`.  Its pullback to the canonical curve is therefore the geometric
twist whose direct image should be the shifted Koszul quotient.  The local
comparison below is obtained entirely from Beck--Chevalley mates and the
rank-one chart trivializations.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientKoszulPullback

open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientKoszulGeometry
open RationalPointsN25QuotientTwoAmbientKoszulGlobal
open RationalPointsN25QuotientTwoAmbientKoszulShifted
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- The actual restriction of the ambient twist `O(-d)` to the canonical
curve. -/
abbrev curvePullbackTwist (d : ℤ) :
    CanonicalProjectiveCurve25Two.Modules :=
  (Scheme.Modules.pullback canonicalProjectiveCurveMap).obj
    (globalTwistModule d)

/-- The direct image of the restricted ambient twist. -/
abbrev shiftedGeometricTarget (d : ℤ) :
    BinaryProjectiveThreeSpace.Modules :=
  (Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
    (curvePullbackTwist d)

/-- The canonical adjunction-unit map from the ambient twist to the direct
image of its restriction to the curve. -/
abbrev shiftedAmbientToCurve (d : ℤ) :
    globalTwistModule d ⟶ shiftedGeometricTarget d :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    canonicalProjectiveCurveMap).unit.app (globalTwistModule d)

/-- The chosen ambient chart trivialization of the restricted global twist. -/
def ambientRestrictedTwistUnitIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        (globalTwistModule d) ≅
      SheafOfModules.unit (ambientChartScheme i).ringCatSheaf :=
  globalTwistModuleLocalIso d i ≪≫ ambientLocalTwistUnitIso d i

/-- Pullback base change and the ambient chart trivialization identify the
restriction of the actual curve twist with the curve-chart unit module. -/
def curvePullbackTwistLocalIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (curveChartMap i)).obj
        (curvePullbackTwist d) ≅
      SheafOfModules.unit (curveChartScheme i).ringCatSheaf :=
  (Scheme.Modules.verticalOpenPullbackBaseChangeIso
    (localCurveMap i) (curveChartMap i) (ambientChartMap i)
    canonicalProjectiveCurveMap
    (curveChart_square_isPullback i)).symm.app (globalTwistModule d) ≪≫
  (Scheme.Modules.pullback (localCurveMap i)).mapIso
    (ambientRestrictedTwistUnitIso d i) ≪≫
  Scheme.Modules.pullbackUnitIsoOfScheme (localCurveMap i)

/-- Restriction of the geometric target to an ambient chart is the affine
curve direct image with its coefficient normalized to the unit module. -/
def shiftedCurveChartTargetIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        (shiftedGeometricTarget d) ≅
      (Scheme.Modules.pushforward (localCurveMap i)).obj
        (SheafOfModules.unit (curveChartScheme i).ringCatSheaf) :=
  Scheme.Modules.verticalOpenBaseChangeIso
      (localCurveMap i) (curveChartMap i) (ambientChartMap i)
      canonicalProjectiveCurveMap (curveChart_square_isPullback i)
      (curvePullbackTwist d) ≪≫
    (Scheme.Modules.pushforward (localCurveMap i)).mapIso
      (curvePullbackTwistLocalIso d i)

/-- After both chart trivializations, the restricted global adjunction unit
is the ordinary affine structure-module map. -/
theorem shiftedAmbientToCurve_restrict_geometric (d : ℤ) (i : Fin 4) :
    (ambientRestrictedTwistUnitIso d i).hom ≫
        Scheme.Modules.unitToPushforwardUnit (localCurveMap i) =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedAmbientToCurve d) ≫
        (shiftedCurveChartTargetIso d i).hom := by
  let H := curveChart_square_isPullback i
  let e := ambientRestrictedTwistUnitIso d i
  have hBC :=
    Scheme.Modules.pullbackPushforwardAdjunction_unit_verticalOpenBaseChange
      (localCurveMap i) (curveChartMap i) (ambientChartMap i)
      canonicalProjectiveCurveMap H (globalTwistModule d)
  have hUnit :=
    Scheme.Modules.pullbackPushforwardAdjunction_unit_conjugate_unit
      (localCurveMap i)
      ((Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        (globalTwistModule d)) e
  change e.hom ≫ Scheme.Modules.unitToPushforwardUnit (localCurveMap i) = _
  rw [hUnit]
  rw [shiftedCurveChartTargetIso, Iso.trans_hom,
    Functor.mapIso_hom]
  slice_rhs 1 2 => rw [hBC]
  simp only [curvePullbackTwistLocalIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp
  rfl

/-! ## Local and global geometric right complexes -/

/-- The affine terminal arrow after trivializing the debt-`d` twist. -/
def shiftedLocalZeroToCurve (d : ℤ) (i : Fin 4) :
    ambientLocalTwistModule d i ⟶
      (Scheme.Modules.pushforward (localCurveMap i)).obj
        (SheafOfModules.unit (curveChartScheme i).ringCatSheaf) :=
  (ambientLocalTwistUnitIso d i).hom ≫
    Scheme.Modules.unitToPushforwardUnit (localCurveMap i)

/-- The shifted local middle differential is killed by the affine curve
structure map. -/
theorem shiftedLocalMiddle_comp_zeroToCurve (d : ℤ) (i : Fin 4) :
    shiftedLocalMiddleMap d i ≫ shiftedLocalZeroToCurve d i = 0 := by
  change ambientLocalKoszulMiddleMap i ≫
      (ambientLocalTwistUnitIso 0 i).hom ≫
      Scheme.Modules.unitToPushforwardUnit (localCurveMap i) = 0
  exact localMiddle_comp_affineCurveTarget i

/-- The shifted affine right Koszul complex with geometric terminal object. -/
def shiftedLocalGeometricRightComplex (d : ℤ) (i : Fin 4) :
    ShortComplex (ambientChartScheme i).Modules :=
  ShortComplex.mk (shiftedLocalMiddleMap d i)
    (shiftedLocalZeroToCurve d i)
    (shiftedLocalMiddle_comp_zeroToCurve d i)

/-- Debt shifts disappear in the chosen affine rank-one trivializations, so
the shifted local geometric complex is the previously proved degree-zero
complex. -/
def ambientLocalGeometricRightComplexIsoShifted (d : ℤ) (i : Fin 4) :
    ambientLocalGeometricRightComplex i ≅
      shiftedLocalGeometricRightComplex d i := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rfl
  · rfl

/-- The shifted local geometric right complex is exact. -/
theorem shiftedLocalGeometricRightComplex_exact (d : ℤ) (i : Fin 4) :
    (shiftedLocalGeometricRightComplex d i).Exact :=
  (ShortComplex.exact_iff_of_iso
    (ambientLocalGeometricRightComplexIsoShifted d i)).mp
      (ambientLocalGeometricRightComplex_exact i)

/-- Morphism-level chart compatibility in the source convention used by
short-complex isomorphisms. -/
theorem shiftedAmbientToCurve_restrict_geometric_local
    (d : ℤ) (i : Fin 4) :
    (globalTwistModuleLocalIso d i).hom ≫
        shiftedLocalZeroToCurve d i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedAmbientToCurve d) ≫
        (shiftedCurveChartTargetIso d i).hom := by
  simpa only [ambientRestrictedTwistUnitIso, shiftedLocalZeroToCurve,
    Iso.trans_hom, Category.assoc] using
      shiftedAmbientToCurve_restrict_geometric d i

/-- On each ambient coordinate chart, the shifted middle differential
followed by the geometric terminal arrow is zero. -/
theorem shiftedGlobalMiddle_comp_ambientToCurve_restrict
    (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
      (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d) = 0 := by
  let RF := Scheme.Modules.restrictFunctor (ambientChartMap i)
  rw [Functor.map_comp]
  change RF.map (shiftedGlobalMiddleMap d) ≫
      RF.map (shiftedAmbientToCurve d) =
    (0 : RF.obj (shiftedGlobalMiddle d) ⟶
      RF.obj (shiftedGeometricTarget d))
  apply (cancel_mono (shiftedCurveChartTargetIso d i).hom).1
  simp only [Category.assoc, zero_comp, RF]
  rw [← shiftedAmbientToCurve_restrict_geometric_local]
  rw [← Category.assoc]
  rw [← shiftedGlobalMiddleMap_restrict]
  simp only [Category.assoc]
  rw [shiftedLocalMiddle_comp_zeroToCurve]
  simp

/-- Every stalk of the global shifted middle-to-target composite is zero.
Choose a standard chart through the point and transport the chartwise result
through the restriction--stalk comparison. -/
theorem shiftedGlobalMiddle_comp_ambientToCurve_stalk
    (d : ℤ) (x : BinaryProjectiveThreeSpace) :
    (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d) = 0 := by
  let i := ambientCoordinateAffineOpenCover.idx x
  have hx := ambientCoordinateAffineOpenCover.covers x
  change x ∈ Set.range (ambientChartMap i) at hx
  obtain ⟨y, hy⟩ := hx
  let G := Scheme.Modules.toPresheaf (ambientChartScheme i) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  letI : (Scheme.Modules.toPresheaf
      (ambientChartScheme i)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : G.PreservesZeroMorphisms := inferInstance
  have hRestricted :
      (Scheme.Modules.restrictFunctor (ambientChartMap i) ⋙ G).map
        (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d) = 0 := by
    change G.map
      ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d)) = 0
    rw [shiftedGlobalMiddle_comp_ambientToCurve_restrict]
    exact G.map_zero _ _
  have hAtImage :
      (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y)).map
        (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d) = 0 := by
    let e := Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y
    apply (cancel_epi (e.hom.app (shiftedGlobalMiddle d))).1
    rw [← e.hom.naturality]
    rw [hRestricted]
    simp
  rw [← hy]
  exact hAtImage

/-- The shifted middle differential is globally annihilated by the
adjunction-unit map to the restricted twist.  Vanishing of every germ implies
vanishing of the morphism of module sheaves. -/
theorem shiftedGlobalMiddle_comp_ambientToCurve (d : ℤ) :
    shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d = 0 := by
  let target := shiftedGeometricTarget d
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext (F.obj target) U
  intro x hx
  change target.presheaf.germ U x hx
      ((shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d).app U s) =
    target.presheaf.germ U x hx
      ((0 : shiftedGlobalMiddle d ⟶ target).app U s)
  have hRight :
      target.presheaf.germ U x hx
          ((0 : shiftedGlobalMiddle d ⟶ target).app U s) = 0 := by
    rw [Scheme.Modules.Hom.zero_app]
    change target.presheaf.germ U x hx 0 = 0
    exact map_zero _
  have hNaturality :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (shiftedGlobalMiddleMap d ≫
            shiftedAmbientToCurve d).mapPresheaf)
          ((shiftedGlobalMiddle d).presheaf.germ U x hx s) =
        target.presheaf.germ U x hx
          ((shiftedGlobalMiddleMap d ≫
            shiftedAmbientToCurve d).app U s) := by
    simpa only [Scheme.Modules.mapPresheaf_app] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        (shiftedGlobalMiddleMap d ≫
          shiftedAmbientToCurve d).mapPresheaf s)
  have hZero :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (shiftedGlobalMiddleMap d ≫
            shiftedAmbientToCurve d).mapPresheaf)
          ((shiftedGlobalMiddle d).presheaf.germ U x hx s) = 0 := by
    change ((Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (shiftedGlobalMiddleMap d ≫ shiftedAmbientToCurve d))
        ((shiftedGlobalMiddle d).presheaf.germ U x hx s) = 0
    rw [shiftedGlobalMiddle_comp_ambientToCurve_stalk]
    rfl
  exact hNaturality.symm.trans (hZero.trans hRight.symm)

/-- The global shifted right Koszul complex with geometric terminal object
`i_* i^* O(-d)`. -/
def shiftedGlobalGeometricRightComplex (d : ℤ) :
    ShortComplex BinaryProjectiveThreeSpace.Modules :=
  ShortComplex.mk (shiftedGlobalMiddleMap d) (shiftedAmbientToCurve d)
    (shiftedGlobalMiddle_comp_ambientToCurve d)

/-- Restricting the global geometric complex to a standard chart recovers
the shifted affine geometric complex. -/
def shiftedRestrictedGlobalGeometricRightComplexIso
    (d : ℤ) (i : Fin 4) :
    (shiftedGlobalGeometricRightComplex d).map
        (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
      shiftedLocalGeometricRightComplex d i :=
  ShortComplex.isoMk
    (shiftedRestrictedMiddleIso d i)
    (globalTwistModuleLocalIso d i)
    (shiftedCurveChartTargetIso d i)
    (shiftedGlobalMiddleMap_restrict d i)
    (shiftedAmbientToCurve_restrict_geometric_local d i)

/-- Exactness is visible after restriction to every standard chart. -/
theorem shiftedRestrictedGlobalGeometricRightComplex_exact
    (d : ℤ) (i : Fin 4) :
    ((shiftedGlobalGeometricRightComplex d).map
      (Scheme.Modules.restrictFunctor (ambientChartMap i))).Exact :=
  (ShortComplex.exact_iff_of_iso
    (shiftedRestrictedGlobalGeometricRightComplexIso d i)).mpr
      (shiftedLocalGeometricRightComplex_exact d i)

/-- Each affine curve chart is a closed subscheme of its ambient chart because
its coordinate-ring map is the proved surjective equation quotient. -/
instance localCurveMap_isClosedImmersion (i : Fin 4) :
    IsClosedImmersion (localCurveMap i) := by
  unfold localCurveMap
  exact IsClosedImmersion.spec_of_surjective _
    (RationalPointsN25QuotientTwoChartIdeal.canonicalConeChartMap_surjective i)

/-- The local geometric terminal arrow is epic: its trivialization is an
isomorphism and a closed immersion is locally surjective on functions. -/
instance shiftedLocalZeroToCurve_epi (d : ℤ) (i : Fin 4) :
    Epi (shiftedLocalZeroToCurve d i) := by
  letI : Epi (Scheme.Modules.unitToPushforwardUnit (localCurveMap i)) :=
    Scheme.Modules.unitToPushforwardUnit_epi (localCurveMap i)
  unfold shiftedLocalZeroToCurve
  infer_instance

/-- The geometric terminal arrow remains epic after restriction to every
standard ambient chart.  The chart-target isomorphism conjugates it to the
local terminal arrow above. -/
instance shiftedAmbientToCurve_restrict_epi (d : ℤ) (i : Fin 4) :
    Epi ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
      (shiftedAmbientToCurve d)) := by
  letI : Epi (shiftedLocalZeroToCurve d i) :=
    shiftedLocalZeroToCurve_epi d i
  rw [← epi_comp_iff_of_isIso _ (shiftedCurveChartTargetIso d i).hom]
  rw [← shiftedAmbientToCurve_restrict_geometric_local]
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
-- The proof composes restriction, sheaf-forgetful, and stalk functors; the
-- extra budget is confined to categorical instance synthesis.
/-- The shifted global geometric right Koszul complex is exact. -/
theorem shiftedGlobalGeometricRightComplex_exact (d : ℤ) :
    (shiftedGlobalGeometricRightComplex d).Exact := by
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  letI : F.Additive := inferInstance
  letI : F.PreservesZeroMorphisms :=
    CategoryTheory.Functor.preservesZeroMorphisms_of_additive F
  apply F.reflects_exact_of_faithful
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  let i := ambientCoordinateAffineOpenCover.idx x
  have hx := ambientCoordinateAffineOpenCover.covers x
  change x ∈ Set.range (ambientChartMap i) at hx
  obtain ⟨y, hy⟩ := hx
  let G := Scheme.Modules.toPresheaf (ambientChartScheme i) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  letI : (Scheme.Modules.toPresheaf
      (ambientChartScheme i)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : G.PreservesZeroMorphisms := inferInstance
  have hChartSheaf := AlgebraicGeometry.tilde_map_toSheaf_exact
    (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulRightComplex i)
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulRightComplex_exact i)
  have hChartStalk :=
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mp hChartSheaf y
  have hChartStalk' :
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulRightSheafComplex i).map
          G |>.Exact := by
    exact hChartStalk
  let e :
      (shiftedGlobalGeometricRightComplex d).map
          (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
        RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulRightSheafComplex i :=
    shiftedRestrictedGlobalGeometricRightComplexIso d i ≪≫
      (ambientLocalGeometricRightComplexIsoShifted d i).symm ≪≫
      (chartKoszulRightSheafComplexIsoLocalGeometric i).symm
  have hRestrictedStalk :
      (((shiftedGlobalGeometricRightComplex d).map
          (Scheme.Modules.restrictFunctor (ambientChartMap i))).map G).Exact :=
    (ShortComplex.exact_iff_of_iso
      ((G.mapShortComplex).mapIso e)).mpr hChartStalk'
  have hAlongChart :
      ((shiftedGlobalGeometricRightComplex d).map
        (Scheme.Modules.restrictFunctor (ambientChartMap i) ⋙ G)).Exact := by
    exact hRestrictedStalk
  have hStalkIso := (shiftedGlobalGeometricRightComplex d).mapNatIso
    (Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y)
  have hAmbientStalk :
      ((shiftedGlobalGeometricRightComplex d).map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y))).Exact :=
    (ShortComplex.exact_iff_of_iso hStalkIso).mp hAlongChart
  have hAmbientAtX :
      ((shiftedGlobalGeometricRightComplex d).map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
    simpa only [hy] using hAmbientStalk
  let underlyingPresheafIso :=
    SheafOfModules.toSheafCompSheafToPresheafIso
      BinaryProjectiveThreeSpace.ringCatSheaf
  letI : (SheafOfModules.forget
      BinaryProjectiveThreeSpace.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf
          BinaryProjectiveThreeSpace.ringCatSheaf.obj).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let underlyingComplexIso :=
    (shiftedGlobalGeometricRightComplex d).mapNatIso underlyingPresheafIso
  let stalkComplexIso :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapShortComplex.mapIso
      underlyingComplexIso
  exact (ShortComplex.exact_iff_of_iso stalkComplexIso).mpr hAmbientAtX

/-- The global adjunction-unit map is an epimorphism.  Cancellation is checked
on the standard affine cover and then descended from chart stalks to ambient
stalks; equality of all germs determines a sheaf morphism. -/
instance shiftedAmbientToCurve_epi (d : ℤ) :
    Epi (shiftedAmbientToCurve d) := by
  constructor
  intro Z a b hab
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  let target := shiftedGeometricTarget d
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  apply TopCat.Presheaf.section_ext (F.obj Z) U
  intro x hx
  let i := ambientCoordinateAffineOpenCover.idx x
  have hxi := ambientCoordinateAffineOpenCover.covers x
  change x ∈ Set.range (ambientChartMap i) at hxi
  obtain ⟨y, hy⟩ := hxi
  let RF := Scheme.Modules.restrictFunctor (ambientChartMap i)
  have hRestrictedComp :
      RF.map (shiftedAmbientToCurve d) ≫ RF.map a =
        RF.map (shiftedAmbientToCurve d) ≫ RF.map b := by
    simpa only [← RF.map_comp] using congrArg RF.map hab
  have hRestricted : RF.map a = RF.map b :=
    (cancel_epi (RF.map (shiftedAmbientToCurve d))).1 hRestrictedComp
  let G := Scheme.Modules.toPresheaf (ambientChartScheme i) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  have hRestrictedAtY :
      (RF ⋙ G).map a = (RF ⋙ G).map b := by
    exact congrArg G.map hRestricted
  let e := Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y
  have hAtImage :
      (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y)).map a =
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y)).map b := by
    apply (cancel_epi (e.hom.app target)).1
    rw [← e.hom.naturality a, ← e.hom.naturality b]
    exact congrArg (fun k => k ≫ e.hom.app Z) hRestrictedAtY
  have hAtX :
      (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map a =
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map b := by
    rw [← hy]
    exact hAtImage
  have hNaturalityA :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map a.mapPresheaf)
          (target.presheaf.germ U x hx s) =
        Z.presheaf.germ U x hx (a.app U s) := by
    simpa only [Scheme.Modules.mapPresheaf_app] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx a.mapPresheaf s)
  have hNaturalityB :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map b.mapPresheaf)
          (target.presheaf.germ U x hx s) =
        Z.presheaf.germ U x hx (b.app U s) := by
    simpa only [Scheme.Modules.mapPresheaf_app] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx b.mapPresheaf s)
  exact hNaturalityA.symm.trans
    ((ConcreteCategory.congr_hom hAtX
      (target.presheaf.germ U x hx s)).trans hNaturalityB)

/-! ## Identification of the categorical quotient -/

/-- The adjunction-unit map factors through the categorical shifted Koszul
quotient. -/
def shiftedGlobalQuotientToCurve (d : ℤ) :
    shiftedGlobalQuotient d ⟶ shiftedGeometricTarget d :=
  cokernel.desc (shiftedGlobalMiddleMap d) (shiftedAmbientToCurve d)
    (shiftedGlobalMiddle_comp_ambientToCurve d)

/-- The quotient comparison recovers the adjunction-unit map after the
cokernel projection. -/
theorem shiftedGlobalProjection_comp_quotientToCurve (d : ℤ) :
    shiftedGlobalProjection d ≫ shiftedGlobalQuotientToCurve d =
      shiftedAmbientToCurve d := by
  exact cokernel.π_desc _ _ _

/-- Exactness and epimorphy give the adjunction-unit map the universal
property of the cokernel of the shifted middle differential. -/
noncomputable def shiftedAmbientToCurveIsCokernel (d : ℤ) :
    IsColimit (CokernelCofork.ofπ (shiftedAmbientToCurve d)
      (shiftedGlobalMiddle_comp_ambientToCurve d)) := by
  letI : Epi (shiftedGlobalGeometricRightComplex d).g :=
    shiftedAmbientToCurve_epi d
  exact (shiftedGlobalGeometricRightComplex_exact d).gIsCokernel

/-- Both geometric restriction and the categorical shifted quotient are
cokernels of the same middle differential. -/
noncomputable def shiftedGlobalQuotientIsoCurve (d : ℤ) :
    shiftedGlobalQuotient d ≅ shiftedGeometricTarget d :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (shiftedGlobalMiddleMap d))
    (shiftedAmbientToCurveIsCokernel d)

/-- The descended comparison is the forward map of the canonical cokernel
isomorphism. -/
theorem shiftedGlobalQuotientToCurve_eq_iso_hom (d : ℤ) :
    shiftedGlobalQuotientToCurve d =
      (shiftedGlobalQuotientIsoCurve d).hom := by
  apply (cancel_epi (shiftedGlobalProjection d)).1
  rw [shiftedGlobalProjection_comp_quotientToCurve]
  exact (IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (shiftedGlobalMiddleMap d))
    (shiftedAmbientToCurveIsCokernel d)
    WalkingParallelPair.one).symm

/-- Hence `Q_d` is canonically isomorphic to `i_* i^* O(-d)` for every
integer debt `d`. -/
instance shiftedGlobalQuotientToCurve_isIso (d : ℤ) :
    IsIso (shiftedGlobalQuotientToCurve d) := by
  rw [shiftedGlobalQuotientToCurve_eq_iso_hom]
  infer_instance

end MazurProof.RationalPointsN25QuotientTwoAmbientKoszulPullback
