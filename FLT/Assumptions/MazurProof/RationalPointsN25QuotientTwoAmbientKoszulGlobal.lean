import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistingMorphisms
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoChartKoszulSheaf

/-!
# Global ambient Koszul morphisms for the N25 complete intersection

The quadric and cubic equations define multiplication maps between ambient
twists.  Their chartwise forms were already proved compatible with the
coordinate-ratio transitions.  This file feeds those compatibility squares
through the effective Cech construction, producing honest global morphisms
`O(-5) -> O(-2) + O(-3) -> O` on binary projective three-space.

The integer parameter of `globalTwistModule d` is the degree debt: it denotes
the transition convention for `O(-d)`.  Thus multiplication by a degree-`e`
homogeneous equation lowers the debt from `d+e` to `d`.
-/

noncomputable section

-- The category of module sheaves is exposed through several reducible
-- aliases (`tilde`, the unit sheaf, and scheme-specific module categories).
-- Reassociation below must compare those aliases beyond instance opacity.
set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGlobal

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoChartKoszul
open RationalPointsN25QuotientTwoChartKoszulSheaf
open RationalPointsN25QuotientTwoKoszulTransition
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientTwistingMorphisms
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 100000 in
-- Affine tilde is additive on module categories, hence preserves the zero
-- morphisms needed to map the module-level Koszul short complex.
noncomputable local instance ambientChartTildePreservesZeroMorphisms (i : Fin 4) :
    (tilde.functor
      (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).PreservesZeroMorphisms :=
  letI : (tilde.functor
      (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor
  Functor.preservesZeroMorphisms_of_additive _

/-- The geometric first overlap projection is the explicit localization map
used by the affine Koszul transition calculation. -/
theorem ambientOverlapToLeft_eq_specMap (i j : Fin 4) :
    ambientOverlapToLeft i j = Spec.map (ambientOverlapFromLeft i j) := by
  rfl

/-- The geometric second overlap projection is the explicit localization map
used by the right-chart Koszul calculation. -/
theorem ambientOverlapToRight_eq_specMap (i j : Fin 4) :
    ambientOverlapToRight i j = Spec.map (ambientOverlapFromRight i j) := by
  rfl

/-! ## Local equation multipliers and their overlap forms -/

/-- Multiplication by the dehomogenized quadric on chart `i`, regarded as a
map between any two local twist trivializations.  The debt relation is imposed
when this map is descended globally. -/
def ambientLocalQuadricMul (sourceDebt targetDebt : ℤ) (i : Fin 4) :
    ambientLocalTwistModule sourceDebt i ⟶
      ambientLocalTwistModule targetDebt i :=
  (tilde.functor
    (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).map
    (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedQuadric i)))

/-- The right-chart expression of the quadric multiplier on an ordered
overlap.  This is the common overlap map for Cech descent. -/
def ambientOverlapQuadricMul (sourceDebt targetDebt : ℤ) (i j : Fin 4) :
    ambientOverlapTwistModule sourceDebt i j ⟶
      ambientOverlapTwistModule targetDebt i j :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientQuadricMulRight i j))

/-- Restriction from the right chart commutes with multiplication by the
quadric after both free rank-one models are identified with the explicit
overlap module. -/
theorem ambientLocalQuadricMul_restrictRight
    (sourceDebt targetDebt : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).map
          (ambientLocalQuadricMul sourceDebt targetDebt j) ≫
        (ambientRestrictRightIso targetDebt i j).hom =
      (ambientRestrictRightIso sourceDebt i j).hom ≫
        ambientOverlapQuadricMul sourceDebt targetDebt i j := by
  unfold ambientRestrictRightIso ambientLocalQuadricMul
    ambientOverlapQuadricMul
  change (Scheme.Modules.restrictFunctor
      (Spec.map (ambientOverlapFromRight i j))).map
        ((tilde.functor
          (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat j)).map
          (ModuleCat.ofHom
            (LinearMap.lsmul _ _ (dehomogenizedQuadric j)))) ≫
      (Scheme.Modules.restrictUnitIso
        (Spec.map (ambientOverlapFromRight i j))).hom =
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).hom ≫
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientQuadricMulRight i j))
  have h := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).hom ≫ z)
    (restrictRight_quadricMul i j)
  simpa only [tildeSelf, Category.assoc, Iso.hom_inv_id_assoc] using h

/-- On an ordered overlap, the degree-two multiplier intertwines the source
transition of debt `d+2` with the target transition of debt `d`. -/
theorem ambientOverlapQuadricMul_transition (d : ℤ) (i j : Fin 4) :
    (ambientOverlapTwistIso (d + 2) i j).hom ≫
        ambientOverlapQuadricMul (d + 2) d i j =
      (tilde.functor (AmbientOverlapRingCat i j)).map
          (ModuleCat.ofHom (ambientQuadricMulLeft i j)) ≫
        (ambientOverlapTwistIso d i j).hom := by
  have h := Away.homogeneousMul_comp_ratioPowerTransition standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) d 2
    (by simpa using canonicalQuadricPolynomial25Two_isHomogeneous)
  norm_num at h
  simpa only [ambientOverlapTwistIso, ambientOverlapQuadricMul,
    ambientOverlapTwistModule, tildeSelf,
    ambientQuadricMulLeft, ambientQuadricMulRight,
    Functor.mapIso_hom, LinearEquiv.toModuleIso_hom,
    ModuleCat.ofHom_comp, Functor.map_comp] using congrArg
      (fun f ↦ (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom f))
      h

/-- Restriction from the left chart and the coordinate transition commute
with the quadric multiplier.  This is the transitioned side of the Cech
naturality square. -/
theorem ambientLocalQuadricMul_restrictLeft (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map
          (ambientLocalQuadricMul (d + 2) d i) ≫
        (ambientRestrictLeftIso d i j ≪≫
          ambientOverlapTwistIso d i j).hom =
      (ambientRestrictLeftIso (d + 2) i j ≪≫
          ambientOverlapTwistIso (d + 2) i j).hom ≫
        ambientOverlapQuadricMul (d + 2) d i j := by
  unfold ambientRestrictLeftIso ambientLocalQuadricMul
    ambientOverlapQuadricMul
  change (Scheme.Modules.restrictFunctor
      (Spec.map (ambientOverlapFromLeft i j))).map
        ((tilde.functor
          (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).map
          (ModuleCat.ofHom
            (LinearMap.lsmul _ _ (dehomogenizedQuadric i)))) ≫
      (Scheme.Modules.restrictUnitIso
        (Spec.map (ambientOverlapFromLeft i j))).hom ≫
      (ambientOverlapTwistIso d i j).hom =
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫
      (ambientOverlapTwistIso (d + 2) i j).hom ≫
      ambientOverlapQuadricMul (d + 2) d i j
  have h := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫ z)
    (restrictLeft_quadricMul i j)
  have hrestrict := by
    simpa only [tildeSelf, Category.assoc, Iso.hom_inv_id_assoc] using h
  have hprefix := congrArg
    (fun z => z ≫ (ambientOverlapTwistIso d i j).hom) hrestrict
  have htransition := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫ z)
    (ambientOverlapQuadricMul_transition d i j).symm
  exact hprefix.trans (by simpa only [Category.assoc] using htransition)

/-- Multiplication by the dehomogenized cubic on one ambient chart. -/
def ambientLocalCubicMul (sourceDebt targetDebt : ℤ) (i : Fin 4) :
    ambientLocalTwistModule sourceDebt i ⟶
      ambientLocalTwistModule targetDebt i :=
  (tilde.functor
    (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).map
    (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedCubic i)))

/-- The right-chart expression of the cubic multiplier on an ordered
overlap. -/
def ambientOverlapCubicMul (sourceDebt targetDebt : ℤ) (i j : Fin 4) :
    ambientOverlapTwistModule sourceDebt i j ⟶
      ambientOverlapTwistModule targetDebt i j :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientCubicMulRight i j))

/-- Right restriction commutes with the cubic multiplier after the standard
rank-one identifications. -/
theorem ambientLocalCubicMul_restrictRight
    (sourceDebt targetDebt : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).map
          (ambientLocalCubicMul sourceDebt targetDebt j) ≫
        (ambientRestrictRightIso targetDebt i j).hom =
      (ambientRestrictRightIso sourceDebt i j).hom ≫
        ambientOverlapCubicMul sourceDebt targetDebt i j := by
  unfold ambientRestrictRightIso ambientLocalCubicMul
    ambientOverlapCubicMul
  change (Scheme.Modules.restrictFunctor
      (Spec.map (ambientOverlapFromRight i j))).map
        ((tilde.functor
          (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat j)).map
          (ModuleCat.ofHom
            (LinearMap.lsmul _ _ (dehomogenizedCubic j)))) ≫
      (Scheme.Modules.restrictUnitIso
        (Spec.map (ambientOverlapFromRight i j))).hom =
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).hom ≫
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientCubicMulRight i j))
  have h := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).hom ≫ z)
    (restrictRight_cubicMul i j)
  simpa only [tildeSelf, Category.assoc, Iso.hom_inv_id_assoc] using h

/-- On an ordered overlap, the degree-three multiplier intertwines debts
`d+3` and `d`. -/
theorem ambientOverlapCubicMul_transition (d : ℤ) (i j : Fin 4) :
    (ambientOverlapTwistIso (d + 3) i j).hom ≫
        ambientOverlapCubicMul (d + 3) d i j =
      (tilde.functor (AmbientOverlapRingCat i j)).map
          (ModuleCat.ofHom (ambientCubicMulLeft i j)) ≫
        (ambientOverlapTwistIso d i j).hom := by
  have h := Away.homogeneousMul_comp_ratioPowerTransition standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) d 3
    (by simpa using canonicalCubicPolynomial25Two_isHomogeneous)
  norm_num at h
  simpa only [ambientOverlapTwistIso, ambientOverlapCubicMul,
    ambientOverlapTwistModule, tildeSelf,
    ambientCubicMulLeft, ambientCubicMulRight,
    Functor.mapIso_hom, LinearEquiv.toModuleIso_hom,
    ModuleCat.ofHom_comp, Functor.map_comp] using congrArg
      (fun f ↦ (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom f))
      h

/-- Left restriction followed by transition commutes with the cubic
multiplier. -/
theorem ambientLocalCubicMul_restrictLeft (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map
          (ambientLocalCubicMul (d + 3) d i) ≫
        (ambientRestrictLeftIso d i j ≪≫
          ambientOverlapTwistIso d i j).hom =
      (ambientRestrictLeftIso (d + 3) i j ≪≫
          ambientOverlapTwistIso (d + 3) i j).hom ≫
        ambientOverlapCubicMul (d + 3) d i j := by
  unfold ambientRestrictLeftIso ambientLocalCubicMul
    ambientOverlapCubicMul
  change (Scheme.Modules.restrictFunctor
      (Spec.map (ambientOverlapFromLeft i j))).map
        ((tilde.functor
          (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)).map
          (ModuleCat.ofHom
            (LinearMap.lsmul _ _ (dehomogenizedCubic i)))) ≫
      (Scheme.Modules.restrictUnitIso
        (Spec.map (ambientOverlapFromLeft i j))).hom ≫
      (ambientOverlapTwistIso d i j).hom =
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫
      (ambientOverlapTwistIso (d + 3) i j).hom ≫
      ambientOverlapCubicMul (d + 3) d i j
  have h := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫ z)
    (restrictLeft_cubicMul i j)
  have hrestrict := by
    simpa only [tildeSelf, Category.assoc, Iso.hom_inv_id_assoc] using h
  have hprefix := congrArg
    (fun z => z ≫ (ambientOverlapTwistIso d i j).hom) hrestrict
  have htransition := congrArg
    (fun z => (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).hom ≫ z)
    (ambientOverlapCubicMul_transition d i j).symm
  exact hprefix.trans (by simpa only [Category.assoc] using htransition)

/-! ## Global equation multipliers -/

/-- The degree-two equation descends to a global map `O(-(d+2)) -> O(-d)`. -/
def ambientGlobalQuadricMul (d : ℤ) :
    globalTwistModule (d + 2) ⟶ globalTwistModule d :=
  ambientGlobalTwistMap (d + 2) d
    (ambientLocalQuadricMul (d + 2) d)
    (ambientOverlapQuadricMul (d + 2) d)
    (ambientLocalQuadricMul_restrictLeft d)
    (ambientLocalQuadricMul_restrictRight (d + 2) d)

/-- The degree-three equation descends to a global map `O(-(d+3)) -> O(-d)`. -/
def ambientGlobalCubicMul (d : ℤ) :
    globalTwistModule (d + 3) ⟶ globalTwistModule d :=
  ambientGlobalTwistMap (d + 3) d
    (ambientLocalCubicMul (d + 3) d)
    (ambientOverlapCubicMul (d + 3) d)
    (ambientLocalCubicMul_restrictLeft d)
    (ambientLocalCubicMul_restrictRight (d + 3) d)

/-- The quadric map followed by the target equalizer inclusion is the product
of its four chartwise multipliers. -/
@[reassoc]
theorem ambientGlobalQuadricMul_comp_ι (d : ℤ) :
    ambientGlobalQuadricMul d ≫
        equalizer.ι (twistCechLeft d) (twistCechRight d) =
      equalizer.ι (twistCechLeft (d + 2)) (twistCechRight (d + 2)) ≫
        ambientTwistCechSourceMap (d + 2) d
          (ambientLocalQuadricMul (d + 2) d) := by
  simpa only [ambientGlobalQuadricMul] using
    ambientGlobalTwistMap_comp_ι (d + 2) d
      (ambientLocalQuadricMul (d + 2) d)
      (ambientOverlapQuadricMul (d + 2) d)
      (ambientLocalQuadricMul_restrictLeft d)
      (ambientLocalQuadricMul_restrictRight (d + 2) d)

/-- The analogous equalizer formula for the cubic multiplier. -/
@[reassoc]
theorem ambientGlobalCubicMul_comp_ι (d : ℤ) :
    ambientGlobalCubicMul d ≫
        equalizer.ι (twistCechLeft d) (twistCechRight d) =
      equalizer.ι (twistCechLeft (d + 3)) (twistCechRight (d + 3)) ≫
        ambientTwistCechSourceMap (d + 3) d
          (ambientLocalCubicMul (d + 3) d) := by
  simpa only [ambientGlobalCubicMul] using
    ambientGlobalTwistMap_comp_ι (d + 3) d
      (ambientLocalCubicMul (d + 3) d)
      (ambientOverlapCubicMul (d + 3) d)
      (ambientLocalCubicMul_restrictLeft d)
      (ambientLocalCubicMul_restrictRight (d + 3) d)

/-! ## Restriction of the global multipliers -/

/-- Literal evaluation on chart `k` identifies the restriction of the
global quadric multiplier with multiplication by the dehomogenized quadric.
The statement is intentionally phrased using the evaluation isomorphism:
this removes all auxiliary Cech reconstruction normalizations from the
eventual comparison of complexes. -/
theorem ambientGlobalQuadricMul_restrict_evaluation (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (ambientGlobalQuadricMul d) ≫
        globalTwistModuleToLocal d k =
      globalTwistModuleToLocal (d + 2) k ≫
        ambientLocalQuadricMul (d + 2) d k := by
  exact ambientGlobalTwistMap_restrict_comp_evaluation (d + 2) d
    (ambientLocalQuadricMul (d + 2) d)
    (ambientOverlapQuadricMul (d + 2) d)
    (ambientLocalQuadricMul_restrictLeft d)
    (ambientLocalQuadricMul_restrictRight (d + 2) d) k

/-- The analogous restriction formula for the global cubic multiplier. -/
theorem ambientGlobalCubicMul_restrict_evaluation (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (ambientGlobalCubicMul d) ≫
        globalTwistModuleToLocal d k =
      globalTwistModuleToLocal (d + 3) k ≫
        ambientLocalCubicMul (d + 3) d k := by
  exact ambientGlobalTwistMap_restrict_comp_evaluation (d + 3) d
    (ambientLocalCubicMul (d + 3) d)
    (ambientOverlapCubicMul (d + 3) d)
    (ambientLocalCubicMul_restrictLeft d)
    (ambientLocalCubicMul_restrictRight (d + 3) d) k

/-! The Koszul complex only uses four specializations of the generic
multipliers.  Naming them with normalized debts prevents the category
instances from having to identify `2 + 3` with `3 + 2` under opaque aliases. -/

/-- Multiplication by the cubic from `O(-5)` to `O(-2)`. -/
def ambientGlobalCubicMul52 : globalTwistModule 5 ⟶ globalTwistModule 2 := by
  simpa using ambientGlobalCubicMul 2

/-- Multiplication by the quadric from `O(-5)` to `O(-3)`. -/
def ambientGlobalQuadricMul53 : globalTwistModule 5 ⟶ globalTwistModule 3 := by
  simpa using ambientGlobalQuadricMul 3

/-- Multiplication by the quadric from `O(-2)` to `O`. -/
def ambientGlobalQuadricMul20 : globalTwistModule 2 ⟶ globalTwistModule 0 := by
  simpa using ambientGlobalQuadricMul 0

/-- Multiplication by the cubic from `O(-3)` to `O`. -/
def ambientGlobalCubicMul30 : globalTwistModule 3 ⟶ globalTwistModule 0 := by
  simpa using ambientGlobalCubicMul 0

/-- On the Cech source, the normalized `5 → 2` map is the product of the
four chartwise cubic multipliers. -/
@[reassoc]
theorem ambientGlobalCubicMul52_comp_ι :
    ambientGlobalCubicMul52 ≫
        (equalizer.ι _ _ : globalTwistModule 2 ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule 5 ⟶ _) ≫
        ambientTwistCechSourceMap 5 2 (ambientLocalCubicMul 5 2) := by
  simpa [ambientGlobalCubicMul52] using ambientGlobalCubicMul_comp_ι 2

/-- On the Cech source, the normalized `5 → 3` map is the product of the
four chartwise quadric multipliers. -/
@[reassoc]
theorem ambientGlobalQuadricMul53_comp_ι :
    ambientGlobalQuadricMul53 ≫
        (equalizer.ι _ _ : globalTwistModule 3 ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule 5 ⟶ _) ≫
        ambientTwistCechSourceMap 5 3 (ambientLocalQuadricMul 5 3) := by
  simpa [ambientGlobalQuadricMul53] using ambientGlobalQuadricMul_comp_ι 3

/-- On the Cech source, the normalized `2 → 0` map is the product of the
four chartwise quadric multipliers. -/
@[reassoc]
theorem ambientGlobalQuadricMul20_comp_ι :
    ambientGlobalQuadricMul20 ≫
        (equalizer.ι _ _ : globalTwistModule 0 ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule 2 ⟶ _) ≫
        ambientTwistCechSourceMap 2 0 (ambientLocalQuadricMul 2 0) := by
  simpa [ambientGlobalQuadricMul20] using ambientGlobalQuadricMul_comp_ι 0

/-- On the Cech source, the normalized `3 → 0` map is the product of the
four chartwise cubic multipliers. -/
@[reassoc]
theorem ambientGlobalCubicMul30_comp_ι :
    ambientGlobalCubicMul30 ≫
        (equalizer.ι _ _ : globalTwistModule 0 ⟶ _) =
      (equalizer.ι _ _ : globalTwistModule 3 ⟶ _) ≫
      ambientTwistCechSourceMap 3 0 (ambientLocalCubicMul 3 0) := by
  simpa [ambientGlobalCubicMul30] using ambientGlobalCubicMul_comp_ι 0

/-- Restricting the normalized `5 → 2` cubic multiplier recovers its chosen
chartwise multiplication map. -/
theorem ambientGlobalCubicMul52_restrict_evaluation (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          ambientGlobalCubicMul52 ≫ globalTwistModuleToLocal 2 k =
      globalTwistModuleToLocal 5 k ≫ ambientLocalCubicMul 5 2 k := by
  simpa [ambientGlobalCubicMul52] using
    ambientGlobalCubicMul_restrict_evaluation 2 k

/-- Restricting the normalized `5 → 3` quadric multiplier recovers its chosen
chartwise multiplication map. -/
theorem ambientGlobalQuadricMul53_restrict_evaluation (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          ambientGlobalQuadricMul53 ≫ globalTwistModuleToLocal 3 k =
      globalTwistModuleToLocal 5 k ≫ ambientLocalQuadricMul 5 3 k := by
  simpa [ambientGlobalQuadricMul53] using
    ambientGlobalQuadricMul_restrict_evaluation 3 k

/-- Restricting the normalized `2 → 0` quadric multiplier recovers its chosen
chartwise multiplication map. -/
theorem ambientGlobalQuadricMul20_restrict_evaluation (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          ambientGlobalQuadricMul20 ≫ globalTwistModuleToLocal 0 k =
      globalTwistModuleToLocal 2 k ≫ ambientLocalQuadricMul 2 0 k := by
  simpa [ambientGlobalQuadricMul20] using
    ambientGlobalQuadricMul_restrict_evaluation 0 k

/-- Restricting the normalized `3 → 0` cubic multiplier recovers its chosen
chartwise multiplication map. -/
theorem ambientGlobalCubicMul30_restrict_evaluation (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          ambientGlobalCubicMul30 ≫ globalTwistModuleToLocal 0 k =
      globalTwistModuleToLocal 3 k ≫ ambientLocalCubicMul 3 0 k := by
  simpa [ambientGlobalCubicMul30] using
    ambientGlobalCubicMul_restrict_evaluation 0 k

/-- On every chart, multiplication by the cubic followed by the quadric
equals multiplication by the quadric followed by the cubic. -/
theorem ambientLocalCubicQuadric_comm (i : Fin 4) :
    ambientLocalCubicMul 5 2 i ≫ ambientLocalQuadricMul 2 0 i =
      ambientLocalQuadricMul 5 3 i ≫ ambientLocalCubicMul 3 0 i := by
  let R :=
    RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i
  let F := tilde.functor R
  let c : ModuleCat.of R R ⟶ ModuleCat.of R R := ModuleCat.ofHom
    (LinearMap.lsmul _ _ (dehomogenizedCubic i))
  let q : ModuleCat.of R R ⟶ ModuleCat.of R R := ModuleCat.ofHom
    (LinearMap.lsmul _ _ (dehomogenizedQuadric i))
  have hcq : c ≫ q = q ≫ c := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change dehomogenizedQuadric i * (dehomogenizedCubic i * x) =
      dehomogenizedCubic i * (dehomogenizedQuadric i * x)
    ring
  simpa only [ambientLocalCubicMul, ambientLocalQuadricMul,
    ambientLocalTwistModule, R, F, c, q, Functor.map_comp] using
      congrArg (fun f => F.map f) hcq

/-- The two global equation multipliers commute.  The proof is detected on
the product of chart extensions after cancelling the target equalizer
inclusion, where it is exactly the local commutativity theorem. -/
theorem ambientGlobalCubicQuadric_comm :
    ambientGlobalCubicMul52 ≫ ambientGlobalQuadricMul20 =
      ambientGlobalQuadricMul53 ≫ ambientGlobalCubicMul30 := by
  have hSource :
      ambientTwistCechSourceMap 5 2 (ambientLocalCubicMul 5 2) ≫
          ambientTwistCechSourceMap 2 0 (ambientLocalQuadricMul 2 0) =
        ambientTwistCechSourceMap 5 3 (ambientLocalQuadricMul 5 3) ≫
          ambientTwistCechSourceMap 3 0 (ambientLocalCubicMul 3 0) := by
    unfold ambientTwistCechSourceMap
    apply Pi.hom_ext
    intro i
    let pushforward_i := Scheme.Modules.pushforward (ambientChartMap i)
    simp only [Category.assoc, Pi.map_π, Pi.map_π_assoc]
    rw [← pushforward_i.map_comp, ← pushforward_i.map_comp,
      ambientLocalCubicQuadric_comm i]
  apply (cancel_mono
    (equalizer.ι _ _ : globalTwistModule 0 ⟶ _)).1
  calc
    (ambientGlobalCubicMul52 ≫ ambientGlobalQuadricMul20) ≫
        (equalizer.ι _ _ : globalTwistModule 0 ⟶ _) =
      ambientGlobalCubicMul52 ≫
        (ambientGlobalQuadricMul20 ≫
          (equalizer.ι _ _ : globalTwistModule 0 ⟶ _)) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => ambientGlobalCubicMul52 ≫ f)
      ambientGlobalQuadricMul20_comp_ι
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ _) ambientGlobalCubicMul52_comp_ι
    _ = _ := Category.assoc _ _ _
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun z => (equalizer.ι _ _ : globalTwistModule 5 ⟶ _) ≫ z) hSource)
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ _)
      ambientGlobalQuadricMul53_comp_ι.symm
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun f => ambientGlobalQuadricMul53 ≫ f)
      ambientGlobalCubicMul30_comp_ι.symm
    _ = (ambientGlobalQuadricMul53 ≫ ambientGlobalCubicMul30) ≫
        (equalizer.ι _ _ : globalTwistModule 0 ⟶ _) :=
      (Category.assoc _ _ _).symm

/-! ## The global Koszul differentials -/

/-- The middle term `O(-2) ⊕ O(-3)` of the ambient Koszul complex. -/
abbrev ambientGlobalKoszulMiddle : BinaryProjectiveThreeSpace.Modules :=
  Limits.prod (globalTwistModule 2) (globalTwistModule 3)

/-- The global top Koszul differential
`r |-> (C r, -Q r) : O(-5) -> O(-2) ⊕ O(-3)`. -/
def ambientGlobalKoszulTop :
    globalTwistModule 5 ⟶ ambientGlobalKoszulMiddle :=
  prod.lift ambientGlobalCubicMul52 (-ambientGlobalQuadricMul53)

/-- The global middle Koszul differential
`(a,b) |-> Q a + C b : O(-2) ⊕ O(-3) -> O`. -/
def ambientGlobalKoszulMiddleMap :
    ambientGlobalKoszulMiddle ⟶ globalTwistModule 0 :=
  prod.fst ≫ ambientGlobalQuadricMul20 +
    prod.snd ≫ ambientGlobalCubicMul30

/-- The global Koszul differentials compose to zero.  After distributing the
product projections, the two terms cancel by commutativity of the global
quadric and cubic multipliers. -/
theorem ambientGlobalKoszulMiddle_comp_top :
    ambientGlobalKoszulTop ≫ ambientGlobalKoszulMiddleMap = 0 := by
  calc
    ambientGlobalKoszulTop ≫ ambientGlobalKoszulMiddleMap =
        ambientGlobalKoszulTop ≫ prod.fst ≫ ambientGlobalQuadricMul20 +
          ambientGlobalKoszulTop ≫ prod.snd ≫ ambientGlobalCubicMul30 := by
      unfold ambientGlobalKoszulMiddleMap
      rw [Preadditive.comp_add]
    _ = ambientGlobalCubicMul52 ≫ ambientGlobalQuadricMul20 +
        (-ambientGlobalQuadricMul53) ≫ ambientGlobalCubicMul30 := by
      simp only [ambientGlobalKoszulTop, prod.lift_fst_assoc,
        prod.lift_snd_assoc]
    _ = ambientGlobalCubicMul52 ≫ ambientGlobalQuadricMul20 -
        ambientGlobalQuadricMul53 ≫ ambientGlobalCubicMul30 := by
      simp only [Preadditive.neg_comp, sub_eq_add_neg]
    _ = 0 := sub_eq_zero.mpr ambientGlobalCubicQuadric_comm

/-- The first three global terms form the left short complex of the ambient
Koszul resolution. -/
def ambientGlobalKoszulLeftComplex :
    ShortComplex BinaryProjectiveThreeSpace.Modules :=
  ShortComplex.mk ambientGlobalKoszulTop ambientGlobalKoszulMiddleMap
    ambientGlobalKoszulMiddle_comp_top

/-! ## The affine complex recovered on a standard chart -/

/-- The local middle term is the product of the two trivialized twists. -/
abbrev ambientLocalKoszulMiddle (i : Fin 4) :
    (ambientChartScheme i).Modules :=
  Limits.prod (ambientLocalTwistModule 2 i) (ambientLocalTwistModule 3 i)

/-- The chartwise top Koszul differential written in the local twist
trivializations selected by the ambient Cech descent. -/
def ambientLocalKoszulTop (i : Fin 4) :
    ambientLocalTwistModule 5 i ⟶ ambientLocalKoszulMiddle i :=
  prod.lift (ambientLocalCubicMul 5 2 i)
    (-(ambientLocalQuadricMul 5 3 i))

/-- The chartwise middle Koszul differential in those same
trivializations. -/
def ambientLocalKoszulMiddleMap (i : Fin 4) :
    ambientLocalKoszulMiddle i ⟶ ambientLocalTwistModule 0 i :=
  prod.fst ≫ ambientLocalQuadricMul 2 0 i +
    prod.snd ≫ ambientLocalCubicMul 3 0 i

/-- The local differentials compose to zero for the same commutativity
reason as their global descendants. -/
theorem ambientLocalKoszulMiddle_comp_top (i : Fin 4) :
    ambientLocalKoszulTop i ≫ ambientLocalKoszulMiddleMap i = 0 := by
  simp only [ambientLocalKoszulTop, ambientLocalKoszulMiddleMap,
    Preadditive.comp_add, Limits.prod.lift_fst_assoc,
    Limits.prod.lift_snd_assoc, Preadditive.neg_comp]
  rw [ambientLocalCubicQuadric_comm]
  simp

/-- The local-twist presentation of the left Koszul complex. -/
def ambientLocalKoszulLeftComplex (i : Fin 4) :
    ShortComplex (ambientChartScheme i).Modules :=
  ShortComplex.mk (ambientLocalKoszulTop i)
    (ambientLocalKoszulMiddleMap i)
    (ambientLocalKoszulMiddle_comp_top i)

/-- Affine tilde carries the module product in the algebraic Koszul complex
to the product of the two local free rank-one sheaves. -/
def chartKoszulLeftSheafComplexIsoLocal (i : Fin 4) :
    chartKoszulLeftSheafComplex i ≅ ambientLocalKoszulLeftComplex i := by
  let R :=
    RationalPointsN25QuotientTwoChartKoszulSheaf.AmbientChartRingCat i
  let F := tilde.functor R
  let M : ModuleCat R := ModuleCat.of R R
  let c : M ⟶ M := ModuleCat.ofHom
    (LinearMap.lsmul _ _ (dehomogenizedCubic i))
  let q : M ⟶ M := ModuleCat.ofHom
    (LinearMap.lsmul _ _ (dehomogenizedQuadric i))
  letI : F.Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor
  letI : PreservesFiniteProducts F :=
    Functor.preservesFiniteProductsOfAdditive F
  -- The affine Koszul complex uses the literal Cartesian product `R × R`,
  -- whereas the local twist complex uses Mathlib's chosen categorical
  -- product.  We pass through the chosen biproduct before applying tilde.
  let concreteProdIso : ModuleCat.of R (R × R) ≅ Limits.prod M M :=
    (ModuleCat.biprodIsoProd M M).symm ≪≫ biprod.isoProd M M
  let prodIso :
      F.obj (ModuleCat.of R (R × R)) ≅
        Limits.prod (F.obj M) (F.obj M) :=
    F.mapIso concreteProdIso ≪≫ PreservesLimitPair.iso F M M
  have moduleTop :
      ModuleCat.ofHom (chartKoszulTop i) ≫ concreteProdIso.hom =
        prod.lift c (-q) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      simp only [concreteProdIso, Iso.trans_hom, Category.assoc,
        biprod.isoProd_hom, prod.lift_fst]
      change ModuleCat.ofHom (chartKoszulTop i) ≫
          (ModuleCat.biprodIsoProd M M).inv ≫ biprod.fst = c
      rw [ModuleCat.biprodIsoProd_inv_comp_fst]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · simp only [Category.assoc, prod.lift_snd]
      simp only [concreteProdIso, Iso.trans_hom, Category.assoc,
        biprod.isoProd_hom, prod.lift_snd]
      change ModuleCat.ofHom (chartKoszulTop i) ≫
          (ModuleCat.biprodIsoProd M M).inv ≫ biprod.snd = -q
      rw [ModuleCat.biprodIsoProd_inv_comp_snd]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  have moduleMiddle :
      concreteProdIso.hom ≫
          (prod.fst ≫ q + prod.snd ≫ c) =
        ModuleCat.ofHom (chartKoszulMiddle i) := by
    simp only [Preadditive.comp_add]
    simp only [concreteProdIso, Iso.trans_hom, Category.assoc,
      biprod.isoProd_hom, prod.lift_fst_assoc, prod.lift_snd_assoc]
    change (ModuleCat.biprodIsoProd M M).inv ≫ biprod.fst ≫ q +
        (ModuleCat.biprodIsoProd M M).inv ≫ biprod.snd ≫ c = _
    rw [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      ← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have prodIso_hom_fst :
      prodIso.hom ≫
          (prod.fst : Limits.prod (F.obj M) (F.obj M) ⟶ F.obj M) =
        F.map (concreteProdIso.hom ≫
          (prod.fst : Limits.prod M M ⟶ M)) := by
    simp only [prodIso, Iso.trans_hom, Category.assoc,
      PreservesLimitPair.iso_hom, prodComparison_fst]
    change F.map concreteProdIso.hom ≫ F.map prod.fst = _
    rw [← F.map_comp]
  have prodIso_hom_snd :
      prodIso.hom ≫
          (prod.snd : Limits.prod (F.obj M) (F.obj M) ⟶ F.obj M) =
        F.map (concreteProdIso.hom ≫
          (prod.snd : Limits.prod M M ⟶ M)) := by
    simp only [prodIso, Iso.trans_hom, Category.assoc,
      PreservesLimitPair.iso_hom, prodComparison_snd]
    change F.map concreteProdIso.hom ≫ F.map prod.snd = _
    rw [← F.map_comp]
  have comm₁₂ :
      prod.lift (F.map c) (-(F.map q)) =
        F.map (ModuleCat.ofHom (chartKoszulTop i)) ≫ prodIso.hom := by
    symm
    apply prod.hom_ext
    · rw [prod.lift_fst]
      simp only [Category.assoc]
      rw [prodIso_hom_fst]
      rw [← F.map_comp]
      rw [← Category.assoc, moduleTop, prod.lift_fst]
    · rw [prod.lift_snd]
      simp only [Category.assoc]
      rw [prodIso_hom_snd]
      rw [← F.map_comp]
      rw [← Category.assoc, moduleTop, prod.lift_snd, F.map_neg]
  have comm₂₃ :
      prodIso.hom ≫
          ((prod.fst : Limits.prod (F.obj M) (F.obj M) ⟶ F.obj M) ≫ F.map q +
            (prod.snd : Limits.prod (F.obj M) (F.obj M) ⟶ F.obj M) ≫ F.map c) =
        F.map (ModuleCat.ofHom (chartKoszulMiddle i)) := by
    rw [Preadditive.comp_add]
    rw [← Category.assoc, prodIso_hom_fst]
    rw [← Category.assoc, prodIso_hom_snd]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add]
    exact congrArg F.map (by
      simpa only [Preadditive.comp_add, Category.assoc] using moduleMiddle)
  refine ShortComplex.isoMk (Iso.refl _) prodIso (Iso.refl _) ?_ ?_
  · exact comm₁₂
  · exact comm₂₃

/-- The local-twist Koszul complex is exact because it is precisely the
already verified affine tilde image of the regular-sequence complex. -/
theorem ambientLocalKoszulLeftComplex_exact (i : Fin 4) :
    (ambientLocalKoszulLeftComplex i).Exact :=
  (ShortComplex.exact_iff_of_iso
    (chartKoszulLeftSheafComplexIsoLocal i)).mp
      (chartKoszulLeftSheafComplex_exact i)

/-! ## Restriction of the global complex -/

/-- Restriction preserves the binary product in the global middle term, and
evaluation identifies its two factors with the corresponding local twists. -/
def restrictedAmbientGlobalKoszulMiddleIso (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        ambientGlobalKoszulMiddle ≅ ambientLocalKoszulMiddle i :=
  PreservesLimitPair.iso
      (Scheme.Modules.restrictFunctor (ambientChartMap i))
      (globalTwistModule 2) (globalTwistModule 3) ≪≫
    prod.mapIso (globalTwistModuleLocalIso 2 i)
      (globalTwistModuleLocalIso 3 i)

/-- After restriction to a standard chart, the global top differential is
the local Koszul top differential. -/
theorem ambientGlobalKoszulTop_restrict (i : Fin 4) :
    (globalTwistModuleLocalIso 5 i).hom ≫ ambientLocalKoszulTop i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalKoszulTop ≫
        (restrictedAmbientGlobalKoszulMiddleIso i).hom := by
  let RF := Scheme.Modules.restrictFunctor (ambientChartMap i)
  have hTopFst : ambientGlobalKoszulTop ≫ prod.fst =
      ambientGlobalCubicMul52 := by
    unfold ambientGlobalKoszulTop
    exact prod.lift_fst _ _
  have hTopSnd : ambientGlobalKoszulTop ≫ prod.snd =
      -ambientGlobalQuadricMul53 := by
    unfold ambientGlobalKoszulTop
    exact prod.lift_snd _ _
  have hC : RF.map ambientGlobalCubicMul52 ≫
      globalTwistModuleToLocal 2 i =
      globalTwistModuleToLocal 5 i ≫ ambientLocalCubicMul 5 2 i := by
    exact ambientGlobalCubicMul52_restrict_evaluation i
  have hQ : RF.map ambientGlobalQuadricMul53 ≫
      globalTwistModuleToLocal 3 i =
      globalTwistModuleToLocal 5 i ≫ ambientLocalQuadricMul 5 3 i := by
    exact ambientGlobalQuadricMul53_restrict_evaluation i
  have map_neg_Q : RF.map (-ambientGlobalQuadricMul53) =
      -(RF.map ambientGlobalQuadricMul53) := by
    rfl
  apply Limits.prod.hom_ext
  · simp only [ambientLocalKoszulTop, restrictedAmbientGlobalKoszulMiddleIso,
      Iso.trans_hom, Category.assoc, prod.mapIso_hom,
      Limits.prod.lift_fst, Limits.prod.map_fst,
      PreservesLimitPair.iso_hom, prodComparison_fst_assoc,
      globalTwistModuleLocalIso]
    change globalTwistModuleToLocal 5 i ≫
        ambientLocalCubicMul 5 2 i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalKoszulTop ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map prod.fst ≫
          globalTwistModuleToLocal 2 i
    rw [← Functor.map_comp_assoc]
    rw [hTopFst]
    exact hC.symm
  · simp only [ambientLocalKoszulTop, restrictedAmbientGlobalKoszulMiddleIso,
      Iso.trans_hom, Category.assoc, prod.mapIso_hom,
      Limits.prod.lift_snd, Limits.prod.map_snd,
      PreservesLimitPair.iso_hom, prodComparison_snd_assoc,
      globalTwistModuleLocalIso]
    change globalTwistModuleToLocal 5 i ≫
        (-(ambientLocalQuadricMul 5 3 i)) =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalKoszulTop ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map prod.snd ≫
          globalTwistModuleToLocal 3 i
    rw [← Functor.map_comp_assoc]
    rw [hTopSnd, map_neg_Q, Preadditive.neg_comp,
      Preadditive.comp_neg]
    exact congrArg Neg.neg hQ.symm

/-- After the same product comparison, restriction of the global middle
differential is the local middle differential. -/
theorem ambientGlobalKoszulMiddleMap_restrict (i : Fin 4) :
    (restrictedAmbientGlobalKoszulMiddleIso i).hom ≫
        ambientLocalKoszulMiddleMap i =
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalKoszulMiddleMap ≫
        (globalTwistModuleLocalIso 0 i).hom := by
  simp only [restrictedAmbientGlobalKoszulMiddleIso,
    ambientLocalKoszulMiddleMap, Iso.trans_hom, Category.assoc,
    prod.mapIso_hom, Limits.prod.map_fst_assoc, Limits.prod.map_snd_assoc,
    Preadditive.comp_add, PreservesLimitPair.iso_hom,
    prodComparison_fst_assoc, prodComparison_snd_assoc,
    globalTwistModuleLocalIso, asIso_hom]
  have hQ :
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalQuadricMul20 ≫ globalTwistModuleToLocal 0 i =
        globalTwistModuleToLocal 2 i ≫
          ambientLocalQuadricMul 2 0 i := by
    exact ambientGlobalQuadricMul20_restrict_evaluation i
  have hC :
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalCubicMul30 ≫ globalTwistModuleToLocal 0 i =
        globalTwistModuleToLocal 3 i ≫
          ambientLocalCubicMul 3 0 i := by
    exact ambientGlobalCubicMul30_restrict_evaluation i
  rw [← hQ, ← hC]
  simp only [← Category.assoc, ← Functor.map_comp]
  have hMapAdd :
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (prod.fst ≫ ambientGlobalQuadricMul20 +
            prod.snd ≫ ambientGlobalCubicMul30) =
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
            (prod.fst ≫ ambientGlobalQuadricMul20) +
          (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
            (prod.snd ≫ ambientGlobalCubicMul30) := by
    rfl
  unfold ambientGlobalKoszulMiddleMap
  rw [hMapAdd, Preadditive.add_comp]

/-- The global left Koszul complex restricted to chart `i` is isomorphic to
the affine local Koszul complex.  Both commutative squares are exactly the
restriction formulas for multiplication by the quadric and cubic. -/
def restrictedAmbientGlobalKoszulLeftComplexIso (i : Fin 4) :
    ambientGlobalKoszulLeftComplex.map
        (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
      ambientLocalKoszulLeftComplex i :=
  ShortComplex.isoMk (globalTwistModuleLocalIso 5 i)
    (restrictedAmbientGlobalKoszulMiddleIso i)
    (globalTwistModuleLocalIso 0 i)
    (ambientGlobalKoszulTop_restrict i)
    (ambientGlobalKoszulMiddleMap_restrict i)

/-- Exactness of the global left Koszul complex is visible after restriction
to every standard coordinate chart. -/
theorem restrictedAmbientGlobalKoszulLeftComplex_exact (i : Fin 4) :
    (ambientGlobalKoszulLeftComplex.map
      (Scheme.Modules.restrictFunctor (ambientChartMap i))).Exact :=
  (ShortComplex.exact_iff_of_iso
    (restrictedAmbientGlobalKoszulLeftComplexIso i)).mpr
      (ambientLocalKoszulLeftComplex_exact i)

/-! ## Passage from the coordinate cover to projective space -/

/-- The four coordinate away charts cover binary projective three-space.
The covering assertion is the graded-algebra fact that the four variables
generate the polynomial ring over its degree-zero part. -/
noncomputable def ambientCoordinateAffineOpenCover :
    BinaryProjectiveThreeSpace.AffineOpenCover := by
  have hcover :
      ⨆ i : Fin 4,
          Proj.basicOpen standardConePiece (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' standardConePiece
      (MvPolynomial.X : Fin 4 → BinaryHomogeneousRing)
      (fun i ↦ ⟨1, coordinate_isHomogeneous i⟩)
      standardConePiece_adjoin_coordinates
  exact
    { I₀ := Fin 4
      X := fun i =>
        RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i
      f := ambientChartMap
      idx := fun x ↦
        (TopologicalSpace.Opens.mem_iSup.mp
          (hcover.ge (Set.mem_univ x))).choose
      covers := fun x ↦ by
        change x ∈ (ambientChartMap _).opensRange
        unfold ambientChartMap ambientCoordinateChartMap
        rw [Proj.opensRange_awayι]
        exact (TopologicalSpace.Opens.mem_iSup.mp
          (hcover.ge (Set.mem_univ x))).choose_spec }

set_option synthInstance.maxHeartbeats 200000 in
-- Several composed forgetful, restriction, and stalk functors occur at
-- once; the extra budget is for categorical instance synthesis.
/-- The ambient global left Koszul complex is exact.  Exactness is checked on
stalks.  Every projective point lifts to one of the four coordinate charts;
restriction commutes with that stalk, and the restricted complex is the
affine Koszul complex already proved exact from the regular sequence. -/
theorem ambientGlobalKoszulLeftComplex_exact :
    ambientGlobalKoszulLeftComplex.Exact := by
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
  letI : G.PreservesZeroMorphisms :=
    inferInstance
  have hChartSheaf := AlgebraicGeometry.tilde_map_toSheaf_exact
    (RationalPointsN25QuotientTwoKoszulSheafTransition.AmbientChartRingCat i)
      (chartKoszulLeftComplex i)
      (chartKoszulLeftComplex_exact i)
  have hChartStalk :=
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mp hChartSheaf y
  have hChartStalk' :
      (chartKoszulLeftSheafComplex i).map G |>.Exact := by
    exact hChartStalk
  let e :
      ambientGlobalKoszulLeftComplex.map
          (Scheme.Modules.restrictFunctor (ambientChartMap i)) ≅
        chartKoszulLeftSheafComplex i :=
    restrictedAmbientGlobalKoszulLeftComplexIso i ≪≫
      (chartKoszulLeftSheafComplexIsoLocal i).symm
  have hRestrictedStalk :
      ((ambientGlobalKoszulLeftComplex.map
          (Scheme.Modules.restrictFunctor (ambientChartMap i))).map G).Exact :=
    (ShortComplex.exact_iff_of_iso
      ((G.mapShortComplex).mapIso e)).mpr hChartStalk'
  have hAlongChart :
      (ambientGlobalKoszulLeftComplex.map
        (Scheme.Modules.restrictFunctor (ambientChartMap i) ⋙ G)).Exact := by
    exact hRestrictedStalk
  have hStalkIso := ambientGlobalKoszulLeftComplex.mapNatIso
    (Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y)
  have hAmbientStalk :
      (ambientGlobalKoszulLeftComplex.map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y))).Exact :=
    (ShortComplex.exact_iff_of_iso hStalkIso).mp hAlongChart
  have hAmbientAtX :
      (ambientGlobalKoszulLeftComplex.map
        (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
    simpa only [hy] using hAmbientStalk
  -- The faithful sheaf forgetful functor lands in the underlying sheaf,
  -- while `Scheme.Modules.toPresheaf` forgets the module structure directly.
  -- Mathlib's canonical natural isomorphism identifies these two routes.
  let underlyingPresheafIso :=
    SheafOfModules.toSheafCompSheafToPresheafIso
      BinaryProjectiveThreeSpace.ringCatSheaf
  letI : (SheafOfModules.forget
      BinaryProjectiveThreeSpace.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf
          BinaryProjectiveThreeSpace.ringCatSheaf.obj).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let underlyingComplexIso :=
    ambientGlobalKoszulLeftComplex.mapNatIso underlyingPresheafIso
  let stalkComplexIso :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapShortComplex.mapIso
      underlyingComplexIso
  exact (ShortComplex.exact_iff_of_iso stalkComplexIso).mpr hAmbientAtX

/-! ## The global Koszul quotient -/

/-- The terminal sheaf in the global Koszul resolution, defined
categorically as the cokernel of the equation map.  The next geometric layer
identifies this sheaf with the direct image of the structure sheaf of the
quadric-cubic projective curve. -/
abbrev ambientGlobalKoszulQuotient :
    BinaryProjectiveThreeSpace.Modules :=
  cokernel ambientGlobalKoszulMiddleMap

/-- The quotient projection from the ambient structure twist. -/
abbrev ambientGlobalKoszulProjection :
    globalTwistModule 0 ⟶ ambientGlobalKoszulQuotient :=
  cokernel.π ambientGlobalKoszulMiddleMap

/-- The right short complex of the global Koszul resolution. -/
def ambientGlobalKoszulRightComplex :
    ShortComplex BinaryProjectiveThreeSpace.Modules :=
  ShortComplex.mk ambientGlobalKoszulMiddleMap
    ambientGlobalKoszulProjection
    (cokernel.condition ambientGlobalKoszulMiddleMap)

/-- Exactness at `O` is the universal property of the cokernel.  Together
with `ambientGlobalKoszulLeftComplex_exact`, this gives the complete exact
four-term ambient Koszul resolution up to geometric identification of its
last object. -/
theorem ambientGlobalKoszulRightComplex_exact :
    ambientGlobalKoszulRightComplex.Exact :=
  ShortComplex.exact_cokernel ambientGlobalKoszulMiddleMap

/-- The terminal projection of the Koszul resolution is an epimorphism. -/
instance ambientGlobalKoszulProjection_epi :
    Epi ambientGlobalKoszulProjection := inferInstance

end MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGlobal
