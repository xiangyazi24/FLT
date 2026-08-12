import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientKoszulQuotient

/-!
# Shifted ambient Koszul resolutions for the N25 curve

The effective ambient twist `globalTwistModule d` uses the degree-debt
convention and represents `O(-d)`.  This file upgrades the previously fixed
degree-zero Koszul resolution to the uniformly shifted sequence

`O(-(d+5)) -> O(-(d+2)) × O(-(d+3)) -> O(-d) -> Q_d`.

The construction is structural.  The quadric and cubic multipliers are
descended from their four affine-chart maps at the normalized debts.  On each
chart, every twist is the same free rank-one sheaf, so the shifted complex is
the affine regular-sequence Koszul complex already proved exact.  Restriction
to the coordinate cover and the stalk criterion then yield global exactness.
The terminal object `Q_d` is the categorical cokernel of the middle map.

No coefficient enumeration or new axiom is used here.  In particular, the
proof packages a reusable exact resolution for every integer twist rather
than reproving isolated numerical cases.
-/

noncomputable section

-- The module-sheaf objects below are exposed through reducible aliases.
-- These settings let Lean compare those aliases across restriction and
-- stalk functors without changing the mathematical content.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientKoszulShifted

open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingMorphisms
open RationalPointsN25QuotientTwoAmbientKoszulGlobal
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoProj
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- The left-overlap naturality square for cubic multiplication, written
with the normalized source debt `d+5`. -/
theorem shiftedCubic_restrictLeft (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map
          (ambientLocalCubicMul (d + 5) (d + 2) i) ≫
        (ambientRestrictLeftIso (d + 2) i j ≪≫
          ambientOverlapTwistIso (d + 2) i j).hom =
      (ambientRestrictLeftIso (d + 5) i j ≪≫
          ambientOverlapTwistIso (d + 5) i j).hom ≫
        ambientOverlapCubicMul (d + 5) (d + 2) i j := by
  convert ambientLocalCubicMul_restrictLeft (d + 2) i j using 1 <;>
    simp only [ambientLocalCubicMul, ambientOverlapCubicMul,
      ambientRestrictLeftIso, ambientLocalTwistUnitIso,
      ambientOverlapTwistUnitIso, ambientLocalTwistModule,
      ambientOverlapTwistModule] <;> congr 3 <;>
      first | omega | (congr 1 <;> omega)

/-- The left-overlap naturality square for quadric multiplication, written
with the normalized source debt `d+5`. -/
theorem shiftedQuadric_restrictLeft (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map
          (ambientLocalQuadricMul (d + 5) (d + 3) i) ≫
        (ambientRestrictLeftIso (d + 3) i j ≪≫
          ambientOverlapTwistIso (d + 3) i j).hom =
      (ambientRestrictLeftIso (d + 5) i j ≪≫
          ambientOverlapTwistIso (d + 5) i j).hom ≫
        ambientOverlapQuadricMul (d + 5) (d + 3) i j := by
  convert ambientLocalQuadricMul_restrictLeft (d + 3) i j using 1 <;>
    simp only [ambientLocalQuadricMul, ambientOverlapQuadricMul,
      ambientRestrictLeftIso, ambientLocalTwistUnitIso,
      ambientOverlapTwistUnitIso, ambientLocalTwistModule,
      ambientOverlapTwistModule] <;> congr 3 <;>
      first | omega | (congr 1 <;> omega)

/-- The cubic component from debt `d+5` to debt `d+2`.  It is descended
directly at the normalized debts, avoiding transports between equalizers. -/
def shiftedCubicToFirst (d : ℤ) :
    globalTwistModule (d + 5) ⟶ globalTwistModule (d + 2) :=
  ambientGlobalTwistMap (d + 5) (d + 2)
    (ambientLocalCubicMul (d + 5) (d + 2))
    (ambientOverlapCubicMul (d + 5) (d + 2))
    (shiftedCubic_restrictLeft d)
    (ambientLocalCubicMul_restrictRight (d + 5) (d + 2))

/-- The quadric component from debt `d+5` to debt `d+3`.  As above, the
descent data are instantiated at the normalized source debt. -/
def shiftedQuadricToSecond (d : ℤ) :
    globalTwistModule (d + 5) ⟶ globalTwistModule (d + 3) :=
  ambientGlobalTwistMap (d + 5) (d + 3)
    (ambientLocalQuadricMul (d + 5) (d + 3))
    (ambientOverlapQuadricMul (d + 5) (d + 3))
    (shiftedQuadric_restrictLeft d)
    (ambientLocalQuadricMul_restrictRight (d + 5) (d + 3))

/-- The normalized cubic map followed by the target equalizer inclusion. -/
@[reassoc]
theorem shiftedCubicToFirst_comp_ι (d : ℤ) :
    shiftedCubicToFirst d ≫
        (equalizer.ι _ _ : globalTwistModule (d + 2) ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule (d + 5) ⟶ _) ≫
        ambientTwistCechSourceMap (d + 5) (d + 2)
          (ambientLocalCubicMul (d + 5) (d + 2)) := by
  exact ambientGlobalTwistMap_comp_ι (d + 5) (d + 2)
    (ambientLocalCubicMul (d + 5) (d + 2))
    (ambientOverlapCubicMul (d + 5) (d + 2))
    (shiftedCubic_restrictLeft d)
    (ambientLocalCubicMul_restrictRight (d + 5) (d + 2))

/-- The normalized quadric map followed by the target equalizer inclusion. -/
@[reassoc]
theorem shiftedQuadricToSecond_comp_ι (d : ℤ) :
    shiftedQuadricToSecond d ≫
        (equalizer.ι _ _ : globalTwistModule (d + 3) ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule (d + 5) ⟶ _) ≫
        ambientTwistCechSourceMap (d + 5) (d + 3)
          (ambientLocalQuadricMul (d + 5) (d + 3)) := by
  exact ambientGlobalTwistMap_comp_ι (d + 5) (d + 3)
    (ambientLocalQuadricMul (d + 5) (d + 3))
    (ambientOverlapQuadricMul (d + 5) (d + 3))
    (shiftedQuadric_restrictLeft d)
    (ambientLocalQuadricMul_restrictRight (d + 5) (d + 3))

/-- Local cubic and quadric multiplication commute at every shifted debt. -/
theorem shiftedLocalCubicQuadric_comm (d : ℤ) (i : Fin 4) :
    ambientLocalCubicMul (d + 5) (d + 2) i ≫
        ambientLocalQuadricMul (d + 2) d i =
      ambientLocalQuadricMul (d + 5) (d + 3) i ≫
        ambientLocalCubicMul (d + 3) d i := by
  simpa only [ambientLocalCubicMul, ambientLocalQuadricMul,
    ambientLocalTwistModule] using ambientLocalCubicQuadric_comm i

/-- The shifted global cubic and quadric multipliers commute. -/
theorem shiftedGlobalCubicQuadric_comm (d : ℤ) :
    shiftedCubicToFirst d ≫ ambientGlobalQuadricMul d =
      shiftedQuadricToSecond d ≫ ambientGlobalCubicMul d := by
  have hSource :
      ambientTwistCechSourceMap (d + 5) (d + 2)
          (ambientLocalCubicMul (d + 5) (d + 2)) ≫
        ambientTwistCechSourceMap (d + 2) d
          (ambientLocalQuadricMul (d + 2) d) =
      ambientTwistCechSourceMap (d + 5) (d + 3)
          (ambientLocalQuadricMul (d + 5) (d + 3)) ≫
        ambientTwistCechSourceMap (d + 3) d
          (ambientLocalCubicMul (d + 3) d) := by
    unfold ambientTwistCechSourceMap
    apply Pi.hom_ext
    intro i
    let pushforward_i := Scheme.Modules.pushforward (ambientChartMap i)
    simp only [Category.assoc, Pi.map_π, Pi.map_π_assoc]
    rw [← pushforward_i.map_comp, ← pushforward_i.map_comp,
      shiftedLocalCubicQuadric_comm d i]
  apply (cancel_mono
    (equalizer.ι _ _ : globalTwistModule d ⟶ _)).1
  calc
    (shiftedCubicToFirst d ≫ ambientGlobalQuadricMul d) ≫
        (equalizer.ι _ _ : globalTwistModule d ⟶ _) =
      shiftedCubicToFirst d ≫
        (ambientGlobalQuadricMul d ≫
          (equalizer.ι _ _ : globalTwistModule d ⟶ _)) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => shiftedCubicToFirst d ≫ f)
      (ambientGlobalQuadricMul_comp_ι d)
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ _) (shiftedCubicToFirst_comp_ι d)
    _ = _ := Category.assoc _ _ _
    _ = _ := by rw [hSource]
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ _)
      (shiftedQuadricToSecond_comp_ι d).symm
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun f => shiftedQuadricToSecond d ≫ f)
      (ambientGlobalCubicMul_comp_ι d).symm
    _ = (shiftedQuadricToSecond d ≫ ambientGlobalCubicMul d) ≫
        (equalizer.ι _ _ : globalTwistModule d ⟶ _) :=
      (Category.assoc _ _ _).symm

/-! ## Shifted global and local complexes -/

/-- The shifted middle term `O(-(d+2)) ⊕ O(-(d+3))`. -/
abbrev shiftedGlobalMiddle (d : ℤ) : BinaryProjectiveThreeSpace.Modules :=
  Limits.prod (globalTwistModule (d + 2)) (globalTwistModule (d + 3))

/-- The shifted top Koszul differential. -/
def shiftedGlobalTop (d : ℤ) :
    globalTwistModule (d + 5) ⟶ shiftedGlobalMiddle d :=
  prod.lift (shiftedCubicToFirst d) (-(shiftedQuadricToSecond d))

/-- The shifted middle Koszul differential. -/
def shiftedGlobalMiddleMap (d : ℤ) :
    shiftedGlobalMiddle d ⟶ globalTwistModule d :=
  prod.fst ≫ ambientGlobalQuadricMul d +
    prod.snd ≫ ambientGlobalCubicMul d

/-- The two shifted global differentials compose to zero. -/
theorem shiftedGlobalMiddle_comp_top (d : ℤ) :
    shiftedGlobalTop d ≫ shiftedGlobalMiddleMap d = 0 := by
  calc
    shiftedGlobalTop d ≫ shiftedGlobalMiddleMap d =
        shiftedGlobalTop d ≫ prod.fst ≫ ambientGlobalQuadricMul d +
          shiftedGlobalTop d ≫ prod.snd ≫ ambientGlobalCubicMul d := by
      unfold shiftedGlobalMiddleMap
      rw [Preadditive.comp_add]
    _ = shiftedCubicToFirst d ≫ ambientGlobalQuadricMul d +
        (-shiftedQuadricToSecond d) ≫ ambientGlobalCubicMul d := by
      simp only [shiftedGlobalTop, prod.lift_fst_assoc,
        prod.lift_snd_assoc]
    _ = shiftedCubicToFirst d ≫ ambientGlobalQuadricMul d -
        shiftedQuadricToSecond d ≫ ambientGlobalCubicMul d := by
      simp only [Preadditive.neg_comp, sub_eq_add_neg]
    _ = 0 := sub_eq_zero.mpr (shiftedGlobalCubicQuadric_comm d)

/-- The shifted global left Koszul complex. -/
def shiftedGlobalLeftComplex (d : ℤ) :
    ShortComplex BinaryProjectiveThreeSpace.Modules :=
  ShortComplex.mk (shiftedGlobalTop d) (shiftedGlobalMiddleMap d)
    (shiftedGlobalMiddle_comp_top d)

/-- The shifted local middle term on chart `i`. -/
abbrev shiftedLocalMiddle (d : ℤ) (i : Fin 4) :
    (ambientChartScheme i).Modules :=
  Limits.prod (ambientLocalTwistModule (d + 2) i)
    (ambientLocalTwistModule (d + 3) i)

/-- The shifted local top differential. -/
def shiftedLocalTop (d : ℤ) (i : Fin 4) :
    ambientLocalTwistModule (d + 5) i ⟶ shiftedLocalMiddle d i :=
  prod.lift (ambientLocalCubicMul (d + 5) (d + 2) i)
    (-(ambientLocalQuadricMul (d + 5) (d + 3) i))

/-- The shifted local middle differential. -/
def shiftedLocalMiddleMap (d : ℤ) (i : Fin 4) :
    shiftedLocalMiddle d i ⟶ ambientLocalTwistModule d i :=
  prod.fst ≫ ambientLocalQuadricMul (d + 2) d i +
    prod.snd ≫ ambientLocalCubicMul (d + 3) d i

/-- The shifted local differentials compose to zero. -/
theorem shiftedLocalMiddle_comp_top (d : ℤ) (i : Fin 4) :
    shiftedLocalTop d i ≫ shiftedLocalMiddleMap d i = 0 := by
  simp only [shiftedLocalTop, shiftedLocalMiddleMap,
    Preadditive.comp_add, prod.lift_fst_assoc, prod.lift_snd_assoc,
    Preadditive.neg_comp]
  rw [shiftedLocalCubicQuadric_comm]
  simp

/-- The shifted local left Koszul complex. -/
def shiftedLocalLeftComplex (d : ℤ) (i : Fin 4) :
    ShortComplex (ambientChartScheme i).Modules :=
  ShortComplex.mk (shiftedLocalTop d i) (shiftedLocalMiddleMap d i)
    (shiftedLocalMiddle_comp_top d i)

/-- The shifted local complex is literally the unshifted affine complex in
the chosen rank-one trivializations; only its later gluing remembers `d`. -/
def ambientLocalKoszulLeftComplexIsoShiftedLocal (d : ℤ) (i : Fin 4) :
    ambientLocalKoszulLeftComplex i ≅ shiftedLocalLeftComplex d i := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rfl
  · rfl

/-- Shifting the debt does not change the affine free-module complex. -/
def chartKoszulLeftSheafComplexIsoShiftedLocal (d : ℤ) (i : Fin 4) :
    RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftSheafComplex i ≅
      shiftedLocalLeftComplex d i :=
  chartKoszulLeftSheafComplexIsoLocal i ≪≫
    ambientLocalKoszulLeftComplexIsoShiftedLocal d i

/-- The shifted local left complex is exact. -/
theorem shiftedLocalLeftComplex_exact (d : ℤ) (i : Fin 4) :
    (shiftedLocalLeftComplex d i).Exact :=
  (ShortComplex.exact_iff_of_iso
    (chartKoszulLeftSheafComplexIsoShiftedLocal d i)).mp
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftSheafComplex_exact i)

/-! ## Restriction of the shifted global complex -/

/-- Restriction of the normalized cubic component recovers its local
multiplier. -/
theorem shiftedCubicToFirst_restrict_evaluation (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedCubicToFirst d) ≫ globalTwistModuleToLocal (d + 2) i =
      globalTwistModuleToLocal (d + 5) i ≫
        ambientLocalCubicMul (d + 5) (d + 2) i := by
  exact ambientGlobalTwistMap_restrict_comp_evaluation
    (d + 5) (d + 2)
    (ambientLocalCubicMul (d + 5) (d + 2))
    (ambientOverlapCubicMul (d + 5) (d + 2))
    (shiftedCubic_restrictLeft d)
    (ambientLocalCubicMul_restrictRight (d + 5) (d + 2)) i

/-- Restriction of the normalized quadric component recovers its local
multiplier. -/
theorem shiftedQuadricToSecond_restrict_evaluation (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedQuadricToSecond d) ≫ globalTwistModuleToLocal (d + 3) i =
      globalTwistModuleToLocal (d + 5) i ≫
        ambientLocalQuadricMul (d + 5) (d + 3) i := by
  exact ambientGlobalTwistMap_restrict_comp_evaluation
    (d + 5) (d + 3)
    (ambientLocalQuadricMul (d + 5) (d + 3))
    (ambientOverlapQuadricMul (d + 5) (d + 3))
    (shiftedQuadric_restrictLeft d)
    (ambientLocalQuadricMul_restrictRight (d + 5) (d + 3)) i

/-- Restriction preserves the shifted binary product and evaluates both
factors in their local trivializations. -/
def shiftedRestrictedMiddleIso (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        (shiftedGlobalMiddle d) ≅ shiftedLocalMiddle d i :=
  PreservesLimitPair.iso
      (Scheme.Modules.restrictFunctor (ambientChartMap i))
      (globalTwistModule (d + 2)) (globalTwistModule (d + 3)) ≪≫
    prod.mapIso (globalTwistModuleLocalIso (d + 2) i)
      (globalTwistModuleLocalIso (d + 3) i)

/-- The shifted global top differential restricts to the shifted local top
differential. -/
theorem shiftedGlobalTop_restrict (d : ℤ) (i : Fin 4) :
    (globalTwistModuleLocalIso (d + 5) i).hom ≫ shiftedLocalTop d i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedGlobalTop d) ≫
        (shiftedRestrictedMiddleIso d i).hom := by
  let RF := Scheme.Modules.restrictFunctor (ambientChartMap i)
  have hTopFst : shiftedGlobalTop d ≫ prod.fst =
      shiftedCubicToFirst d := by
    unfold shiftedGlobalTop
    exact prod.lift_fst _ _
  have hTopSnd : shiftedGlobalTop d ≫ prod.snd =
      -shiftedQuadricToSecond d := by
    unfold shiftedGlobalTop
    exact prod.lift_snd _ _
  have hC := shiftedCubicToFirst_restrict_evaluation d i
  have hQ := shiftedQuadricToSecond_restrict_evaluation d i
  have map_neg_Q : RF.map (-shiftedQuadricToSecond d) =
      -(RF.map (shiftedQuadricToSecond d)) := by
    rfl
  apply prod.hom_ext
  · simp only [shiftedLocalTop, shiftedRestrictedMiddleIso,
      Iso.trans_hom, Category.assoc, prod.mapIso_hom,
      prod.lift_fst, prod.map_fst, PreservesLimitPair.iso_hom,
      prodComparison_fst_assoc, globalTwistModuleLocalIso]
    change globalTwistModuleToLocal (d + 5) i ≫
        ambientLocalCubicMul (d + 5) (d + 2) i =
      RF.map (shiftedGlobalTop d) ≫ RF.map prod.fst ≫
        globalTwistModuleToLocal (d + 2) i
    rw [← RF.map_comp_assoc, hTopFst]
    exact hC.symm
  · simp only [shiftedLocalTop, shiftedRestrictedMiddleIso,
      Iso.trans_hom, Category.assoc, prod.mapIso_hom,
      prod.lift_snd, prod.map_snd, PreservesLimitPair.iso_hom,
      prodComparison_snd_assoc, globalTwistModuleLocalIso]
    change globalTwistModuleToLocal (d + 5) i ≫
        (-(ambientLocalQuadricMul (d + 5) (d + 3) i)) =
      RF.map (shiftedGlobalTop d) ≫ RF.map prod.snd ≫
        globalTwistModuleToLocal (d + 3) i
    rw [← RF.map_comp_assoc, hTopSnd, map_neg_Q,
      Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg hQ.symm

/-- The shifted global middle differential restricts to the shifted local
middle differential. -/
theorem shiftedGlobalMiddleMap_restrict (d : ℤ) (i : Fin 4) :
    (shiftedRestrictedMiddleIso d i).hom ≫ shiftedLocalMiddleMap d i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (shiftedGlobalMiddleMap d) ≫
        (globalTwistModuleLocalIso d i).hom := by
  simp only [shiftedRestrictedMiddleIso, shiftedLocalMiddleMap,
    Iso.trans_hom, Category.assoc, prod.mapIso_hom,
    prod.map_fst_assoc, prod.map_snd_assoc, Preadditive.comp_add,
    PreservesLimitPair.iso_hom, prodComparison_fst_assoc,
    prodComparison_snd_assoc, globalTwistModuleLocalIso, asIso_hom]
  have hQ := ambientGlobalQuadricMul_restrict_evaluation d i
  have hC := ambientGlobalCubicMul_restrict_evaluation d i
  rw [← hQ, ← hC]
  simp only [← Category.assoc, ← Functor.map_comp]
  have hMapAdd :
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (prod.fst ≫ ambientGlobalQuadricMul d +
            prod.snd ≫ ambientGlobalCubicMul d) =
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
            (prod.fst ≫ ambientGlobalQuadricMul d) +
          (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
            (prod.snd ≫ ambientGlobalCubicMul d) := by
    rfl
  unfold shiftedGlobalMiddleMap
  rw [hMapAdd, Preadditive.add_comp]

/-- The restricted shifted global complex is the shifted local complex. -/
def shiftedRestrictedGlobalLeftComplexIso (d : ℤ) (i : Fin 4) :
    (shiftedGlobalLeftComplex d).map
        (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
      shiftedLocalLeftComplex d i :=
  ShortComplex.isoMk (globalTwistModuleLocalIso (d + 5) i)
    (shiftedRestrictedMiddleIso d i)
    (globalTwistModuleLocalIso d i)
    (shiftedGlobalTop_restrict d i)
    (shiftedGlobalMiddleMap_restrict d i)

/-- Exactness of the shifted global complex is visible on every coordinate
chart. -/
theorem shiftedRestrictedGlobalLeftComplex_exact (d : ℤ) (i : Fin 4) :
    ((shiftedGlobalLeftComplex d).map
      (Scheme.Modules.restrictFunctor (ambientChartMap i))).Exact :=
  (ShortComplex.exact_iff_of_iso
    (shiftedRestrictedGlobalLeftComplexIso d i)).mpr
      (shiftedLocalLeftComplex_exact d i)

set_option synthInstance.maxHeartbeats 200000 in
-- Restriction, sheaf forgetful functors, and stalks are composed in the same
-- proof, so categorical instance synthesis needs a local larger budget.
/-- The shifted ambient left Koszul complex is globally exact for every
integer debt. -/
theorem shiftedGlobalLeftComplex_exact (d : ℤ) :
    (shiftedGlobalLeftComplex d).Exact := by
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  letI : F.Additive := inferInstance
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
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
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftComplex i)
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftComplex_exact i)
  have hChartStalk :=
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mp hChartSheaf y
  have hChartStalk' :
      (RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftSheafComplex i).map
          G |>.Exact := by
    exact hChartStalk
  let e :
      (shiftedGlobalLeftComplex d).map
          (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
        RationalPointsN25QuotientTwoChartKoszulSheaf.chartKoszulLeftSheafComplex i :=
    shiftedRestrictedGlobalLeftComplexIso d i ≪≫
      (chartKoszulLeftSheafComplexIsoShiftedLocal d i).symm
  have hRestrictedStalk :
      (((shiftedGlobalLeftComplex d).map
          (Scheme.Modules.restrictFunctor (ambientChartMap i))).map G).Exact :=
    (ShortComplex.exact_iff_of_iso
      ((G.mapShortComplex).mapIso e)).mpr hChartStalk'
  have hAlongChart :
      ((shiftedGlobalLeftComplex d).map
        (Scheme.Modules.restrictFunctor (ambientChartMap i) ⋙ G)).Exact := by
    exact hRestrictedStalk
  have hStalkIso := (shiftedGlobalLeftComplex d).mapNatIso
    (Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y)
  have hAmbientStalk :
      ((shiftedGlobalLeftComplex d).map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y))).Exact :=
    (ShortComplex.exact_iff_of_iso hStalkIso).mp hAlongChart
  have hAmbientAtX :
      ((shiftedGlobalLeftComplex d).map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
    simpa only [hy] using hAmbientStalk
  -- Compare the two canonical forgetful routes to presheaves before taking
  -- the stalk at `x`.
  let underlyingPresheafIso :=
    SheafOfModules.toSheafCompSheafToPresheafIso
      BinaryProjectiveThreeSpace.ringCatSheaf
  letI : (SheafOfModules.forget
      BinaryProjectiveThreeSpace.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf
          BinaryProjectiveThreeSpace.ringCatSheaf.obj).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let underlyingComplexIso :=
    (shiftedGlobalLeftComplex d).mapNatIso underlyingPresheafIso
  let stalkComplexIso :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapShortComplex.mapIso
      underlyingComplexIso
  exact (ShortComplex.exact_iff_of_iso stalkComplexIso).mpr hAmbientAtX

/-! ## Shifted categorical quotient -/

/-- The terminal object of the shifted Koszul resolution, defined as the
cokernel of the shifted middle differential. -/
abbrev shiftedGlobalQuotient (d : ℤ) :
    BinaryProjectiveThreeSpace.Modules :=
  cokernel (shiftedGlobalMiddleMap d)

/-- The shifted quotient projection. -/
abbrev shiftedGlobalProjection (d : ℤ) :
    globalTwistModule d ⟶ shiftedGlobalQuotient d :=
  cokernel.π (shiftedGlobalMiddleMap d)

/-- The shifted right Koszul complex. -/
def shiftedGlobalRightComplex (d : ℤ) :
    ShortComplex BinaryProjectiveThreeSpace.Modules :=
  ShortComplex.mk (shiftedGlobalMiddleMap d) (shiftedGlobalProjection d)
    (cokernel.condition (shiftedGlobalMiddleMap d))

/-- Exactness of the shifted right complex is the cokernel universal
property. -/
theorem shiftedGlobalRightComplex_exact (d : ℤ) :
    (shiftedGlobalRightComplex d).Exact :=
  ShortComplex.exact_cokernel (shiftedGlobalMiddleMap d)

end MazurProof.RationalPointsN25QuotientTwoAmbientKoszulShifted
