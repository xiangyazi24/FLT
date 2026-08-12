import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGeometry
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoIdealSheaf

/-!
# Geometric quotient of the N25 ambient Koszul complex

The ambient Koszul resolution ends in a categorical cokernel, whereas the
projective quotient curve supplies the geometric target `i_* O_C`.  This
file compares them without assuming the desired identification.

The argument first works on each standard coordinate chart.  The localized
quadric and cubic vanish in the quotient chart ring, so the chartwise
structure-module map kills the local Koszul differential.  The four chart
identities are then transported to stalks and hence to the global module
sheaves.  Consequently the geometric target receives a canonical morphism
from the categorical cokernel.  Its epimorphism instance is the surjective
half of the eventual identification; proving it monic is the remaining
geometric exactness step.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGeometry

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open RationalPointsN25QuotientTwoAmbientKoszulGlobal
open RationalPointsN25QuotientTwoIdealSheaf
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Graded

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate-away ring of the projective quotient curve on chart `i`.
It is the quotient of the corresponding ambient away ring by the localized
quadric and cubic equations. -/
abbrev curveChartRingCat (i : Fin 4) : CommRingCat :=
  .of (Away literalConePiece
    (canonicalConeGradedProjection (MvPolynomial.X i)))

/-- The affine standard chart of the projective quotient curve. -/
abbrev curveChartScheme (i : Fin 4) : Scheme :=
  Spec (curveChartRingCat i)

/-- The closed affine chart map induced by the localized quotient map. -/
def localCurveMap (i : Fin 4) :
    curveChartScheme i ⟶ ambientChartScheme i :=
  Spec.map (CommRingCat.ofHom (canonicalConeChartMap i))

/-- The image of the ambient affine chart is its standard projective basic
open.  Naming this equality keeps later chart-square arguments geometric. -/
theorem ambientChartMap_image_top (i : Fin 4) :
    ambientChartMap i ''ᵁ ⊤ =
      Proj.basicOpen standardConePiece (MvPolynomial.X i) := by
  unfold ambientChartMap ambientCoordinateChartMap
  rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]

/-- The canonical open immersion from the quotient away chart into the
projective quotient curve. -/
def curveChartMap (i : Fin 4) :
    curveChartScheme i ⟶ CanonicalProjectiveCurve25Two :=
  Proj.awayι literalConePiece
    (canonicalConeGradedProjection (MvPolynomial.X i))
    (map_mem canonicalConeGradedProjection (coordinate_isHomogeneous i))
    (by norm_num)

/-- Every standard quotient chart is an open subscheme of the projective
curve. -/
instance curveChartMap_isOpenImmersion (i : Fin 4) :
    IsOpenImmersion (curveChartMap i) := by
  unfold curveChartMap
  infer_instance

/-- The quotient-chart square commutes: restricting the global closed
immersion agrees with the affine map induced by the localized quotient. -/
theorem curveChartMap_comp_canonicalProjectiveCurveMap (i : Fin 4) :
    curveChartMap i ≫ canonicalProjectiveCurveMap =
      localCurveMap i ≫ ambientChartMap i := by
  simpa only [curveChartMap, canonicalProjectiveCurveMap,
    localCurveMap, ambientChartMap, ambientCoordinateChartMap,
    canonicalConeChartMap] using
      Proj.awayι_comp_map canonicalConeGradedProjection
        canonicalCone_irrelevant_le_map (by norm_num)
        (MvPolynomial.X i) (coordinate_isHomogeneous i)

/-- The standard curve chart is the scheme-theoretic pullback of the
corresponding ambient standard chart.  The equality of open ranges reduces
to functoriality of projective basic opens under the homogeneous quotient. -/
theorem curveChart_square_isPullback (i : Fin 4) :
    IsPullback (localCurveMap i) (curveChartMap i)
      (ambientChartMap i) canonicalProjectiveCurveMap := by
  apply IsOpenImmersion.isPullback
  · exact curveChartMap_comp_canonicalProjectiveCurveMap i
  · change canonicalProjectiveCurveMap ⁻¹ᵁ
        (ambientChartMap i).opensRange =
      (curveChartMap i).opensRange
    have hAmbient :
        (ambientChartMap i).opensRange =
          Proj.basicOpen standardConePiece (MvPolynomial.X i) := by
      unfold ambientChartMap ambientCoordinateChartMap
      rw [Proj.opensRange_awayι]
    rw [hAmbient, canonicalProjectiveCurveMap_preimage_coordinate]
    unfold curveChartMap
    rw [Proj.opensRange_awayι]

/-- A chart-ring element killed by the quotient map also vanishes after it
is interpreted as an ambient section and restricted to the projective
curve.  The proof uses the commutative square of the two projective away
charts; both remaining section maps are isomorphisms because the relevant
open lies in the chart image. -/
theorem canonicalProjectiveCurveMap_app_chartGenerator_eq_zero
    (i : Fin 4) (r : AmbientChartRingCat i)
    (hr : canonicalConeChartMap i r = 0) :
    canonicalProjectiveCurveMap.app (ambientChartMap i ''ᵁ ⊤)
        (((ambientChartMap i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv r)) = 0 := by
  have hLocal : (localCurveMap i).app ⊤
      ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv r) = 0 := by
    unfold localCurveMap
    change ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv ≫
      Scheme.Hom.appTop
        (Spec.map (CommRingCat.ofHom (canonicalConeChartMap i)))) r = 0
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rw [ConcreteCategory.comp_apply]
    change (Scheme.ΓSpecIso (curveChartRingCat i)).inv
      (canonicalConeChartMap i r) = 0
    rw [hr]
    simp
  have happ := IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
    (localCurveMap i) (ambientChartMap i)
    (curveChartMap i ≫ canonicalProjectiveCurveMap)
    (curveChartMap_comp_canonicalProjectiveCurveMap i) ⊤
  have happ_r := congrArg (fun q =>
    q ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv r)) happ
  simp only [CategoryTheory.comp_apply, Scheme.Hom.comp_app] at happ_r
  rw [hLocal] at happ_r
  have hsubset :
      canonicalProjectiveCurveMap ⁻¹ᵁ (ambientChartMap i ''ᵁ ⊤) ≤
        (curveChartMap i).opensRange := by
    rw [ambientChartMap_image_top,
      canonicalProjectiveCurveMap_preimage_coordinate]
    unfold curveChartMap
    rw [Proj.opensRange_awayι]
  letI : IsIso ((curveChartMap i).app
      (canonicalProjectiveCurveMap ⁻¹ᵁ
        (ambientChartMap i ''ᵁ ⊤))) :=
    (curveChartMap i).isIso_app _ hsubset
  let e : localCurveMap i ⁻¹ᵁ ⊤ =
      (curveChartMap i ≫ canonicalProjectiveCurveMap) ⁻¹ᵁ
        (ambientChartMap i ''ᵁ ⊤) :=
    IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
      (localCurveMap i) (ambientChartMap i)
      (curveChartMap i ≫ canonicalProjectiveCurveMap)
      (curveChartMap_comp_canonicalProjectiveCurveMap i) ⊤
  let eqMap := (curveChartScheme i).presheaf.map (eqToHom e).op
  letI : IsIso eqMap := by
    dsimp only [eqMap]
    change IsIso ((curveChartScheme i).presheaf.map
      (eqToIso e).hom.op)
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso
    ((curveChartMap i).app
      (canonicalProjectiveCurveMap ⁻¹ᵁ
        (ambientChartMap i ''ᵁ ⊤)))).1
  apply (ConcreteCategory.bijective_of_isIso eqMap).1
  change eqMap
      ((curveChartMap i).app
        (canonicalProjectiveCurveMap ⁻¹ᵁ
          (ambientChartMap i ''ᵁ ⊤))
        (canonicalProjectiveCurveMap.app
          (ambientChartMap i ''ᵁ ⊤)
          (((ambientChartMap i).appIso ⊤).inv
            ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv r)))) =
      eqMap ((curveChartMap i).app
        (canonicalProjectiveCurveMap ⁻¹ᵁ
          (ambientChartMap i ''ᵁ ⊤)) 0)
  rw [map_zero]
  exact happ_r.symm

/-- Restrict the global structure-module map of the projective curve to one
ambient standard chart.  The inverse unit comparison turns a local section
into the corresponding section on the chart image before applying the
closed-immersion section map. -/
def ambientLocalUnitToGlobalCurve (i : Fin 4) :
    SheafOfModules.unit (ambientChartScheme i).ringCatSheaf ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        ((Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
          (SheafOfModules.unit
            CanonicalProjectiveCurve25Two.ringCatSheaf)) :=
  (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv ≫
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
      (Scheme.Modules.unitToPushforwardUnit
        canonicalProjectiveCurveMap)

/-- Affine tilde reduces a local equation map to its value on the generator
`1`.  If its scalar vanishes under the chart quotient, that generator maps
to zero on the projective curve by the preceding chart-square calculation. -/
theorem localMul_comp_ambientLocalUnitToGlobalCurve
    (i : Fin 4) (r : AmbientChartRingCat i)
    (hr : canonicalConeChartMap i r = 0) :
    (tilde.functor (AmbientChartRingCat i)).map
          (ModuleCat.ofHom (LinearMap.lsmul _ _ r)) ≫
        (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i = 0 := by
  apply ((tilde.adjunction (R := AmbientChartRingCat i)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_apply]
  change (tilde.toTildeΓNatIso (R := AmbientChartRingCat i)).hom.app _ ≫ _ =
    (tilde.toTildeΓNatIso (R := AmbientChartRingCat i)).hom.app _ ≫ _
  apply ModuleCat.hom_ext
  change
    (((tilde.toTildeΓNatIso (R := AmbientChartRingCat i)).hom.app
          (ModuleCat.of (AmbientChartRingCat i) (AmbientChartRingCat i)) ≫
        (moduleSpecΓFunctor (R := AmbientChartRingCat i)).map
          ((tilde.functor (AmbientChartRingCat i)).map
                (ModuleCat.ofHom (LinearMap.lsmul _ _ r)) ≫
            (ambientLocalTwistUnitIso 0 i).hom ≫
            ambientLocalUnitToGlobalCurve i)).hom :
      AmbientChartRingCat i →ₗ[AmbientChartRingCat i] _) =
    (((tilde.toTildeΓNatIso (R := AmbientChartRingCat i)).hom.app
          (ModuleCat.of (AmbientChartRingCat i) (AmbientChartRingCat i)) ≫
        (moduleSpecΓFunctor (R := AmbientChartRingCat i)).map 0).hom :
      AmbientChartRingCat i →ₗ[AmbientChartRingCat i] _)
  apply LinearMap.ext_ring
  let outer := fun z :
      (ambientLocalTwistModule 0 i).presheaf.obj (.op ⊤) =>
    ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        (Scheme.Modules.unitToPushforwardUnit
          canonicalProjectiveCurveMap)).app ⊤
      ((Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv.app ⊤
        ((ambientLocalTwistUnitIso 0 i).hom.app ⊤ z))
  change outer (((tilde.functor (AmbientChartRingCat i)).map
      (ModuleCat.ofHom (LinearMap.lsmul _ _ r))).app ⊤
        ((tilde.isoTop (R := AmbientChartRingCat i)
          (ModuleCat.of (AmbientChartRingCat i)
            (AmbientChartRingCat i))).hom 1)) = 0
  simp only [tilde.isoTop, asIso_hom]
  rw [tilde.functor_map]
  calc
    outer ((tilde.map (ModuleCat.ofHom (LinearMap.lsmul _ _ r))).app ⊤
        ((tilde.toOpen (ModuleCat.of (AmbientChartRingCat i)
          (AmbientChartRingCat i)) ⊤) 1)) =
      outer ((tilde.toOpen (ModuleCat.of (AmbientChartRingCat i)
        (AmbientChartRingCat i)) ⊤) ((LinearMap.lsmul _ _ r) 1)) :=
        congrArg outer (Scheme.Modules.tildeMap_toOpen_apply
          (ModuleCat.ofHom (LinearMap.lsmul _ _ r)) ⊤ 1)
    _ = 0 := by
      simp only [LinearMap.lsmul_apply, smul_eq_mul, mul_one]
      simp only [outer, ambientLocalTwistUnitIso, tildeSelf, Iso.refl_hom]
      change canonicalProjectiveCurveMap.app (ambientChartMap i ''ᵁ ⊤)
          (((ambientChartMap i).appIso ⊤).inv
            ((Scheme.ΓSpecIso (AmbientChartRingCat i)).inv r)) = 0
      exact canonicalProjectiveCurveMap_app_chartGenerator_eq_zero i r hr

/-- The dehomogenized quadric is killed by the restricted projective-curve
structure map. -/
theorem localQuadric_comp_ambientLocalUnitToGlobalCurve (i : Fin 4) :
    ambientLocalQuadricMul 2 0 i ≫
        (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i = 0 := by
  exact localMul_comp_ambientLocalUnitToGlobalCurve i
    (dehomogenizedQuadric i)
    (canonicalConeChartMap_dehomogenizedQuadric_eq_zero i)

/-- The dehomogenized cubic is killed by the restricted projective-curve
structure map. -/
theorem localCubic_comp_ambientLocalUnitToGlobalCurve (i : Fin 4) :
    ambientLocalCubicMul 3 0 i ≫
        (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i = 0 := by
  exact localMul_comp_ambientLocalUnitToGlobalCurve i
    (dehomogenizedCubic i)
    (canonicalConeChartMap_dehomogenizedCubic_eq_zero i)

/-- Therefore the entire local middle Koszul differential is killed by the
restricted projective-curve structure map. -/
theorem localMiddle_comp_ambientLocalUnitToGlobalCurve (i : Fin 4) :
    ambientLocalKoszulMiddleMap i ≫
        (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i = 0 := by
  unfold ambientLocalKoszulMiddleMap
  rw [Preadditive.add_comp]
  simp only [Category.assoc,
    localQuadric_comp_ambientLocalUnitToGlobalCurve,
    localCubic_comp_ambientLocalUnitToGlobalCurve, comp_zero, zero_add]

/-! ## Comparison with the localized global terminal map -/

/-- After restricting `O(0) \simeq O` to a coordinate chart, its inverse is
the composite of the local trivialization with the inverse restriction-unit
comparison.  This is the inverse form of the previously proved normalization
of the zero-twist Cech equalizer. -/
theorem ambientGlobalTwistZeroIsoUnit_restrict (i : Fin 4) :
    (globalTwistModuleLocalIso 0 i).inv ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalTwistZeroIsoUnit.hom =
      (ambientLocalTwistUnitIso 0 i).hom ≫
        (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv := by
  let RF := Scheme.Modules.restrictFunctor (ambientChartMap i)
  letI := ambientUnitToGlobalTwistZero_isIso
  letI : IsIso (RF.map ambientUnitToGlobalTwistZero) :=
    Functor.map_isIso RF ambientUnitToGlobalTwistZero
  have hNormalization :
      RF.map ambientUnitToGlobalTwistZero ≫
          (globalTwistModuleLocalIso 0 i).hom ≫
          (ambientLocalTwistUnitIso 0 i).hom =
        (Scheme.Modules.restrictUnitIso (ambientChartMap i)).hom := by
    simpa only [globalTwistModuleLocalUnitIso, Iso.trans_hom,
      Category.assoc] using ambientUnitToGlobalTwistZero_restrict i
  have hInverse :
      ambientUnitToGlobalTwistZero ≫
          ambientGlobalTwistZeroIsoUnit.hom =
        𝟙 (SheafOfModules.unit
          BinaryProjectiveThreeSpace.ringCatSheaf) := by
    change (asIso ambientUnitToGlobalTwistZero).hom ≫
        (asIso ambientUnitToGlobalTwistZero).inv = 𝟙 _
    exact (asIso ambientUnitToGlobalTwistZero).hom_inv_id
  apply (cancel_epi (globalTwistModuleLocalIso 0 i).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_epi (RF.map ambientUnitToGlobalTwistZero)).1
  calc
    RF.map ambientUnitToGlobalTwistZero ≫
        RF.map ambientGlobalTwistZeroIsoUnit.hom =
      RF.map (ambientUnitToGlobalTwistZero ≫
        ambientGlobalTwistZeroIsoUnit.hom) :=
          (RF.map_comp _ _).symm
    _ = RF.map (𝟙 _) := congrArg RF.map hInverse
    _ = 𝟙 _ := RF.map_id _
    _ = (Scheme.Modules.restrictUnitIso
        (ambientChartMap i)).hom ≫
          (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv :=
      (Scheme.Modules.restrictUnitIso (ambientChartMap i)).hom_inv_id.symm
    _ = (RF.map ambientUnitToGlobalTwistZero ≫
          (globalTwistModuleLocalIso 0 i).hom ≫
          (ambientLocalTwistUnitIso 0 i).hom) ≫
        (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv :=
      congrArg (fun q => q ≫
        (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv)
        hNormalization.symm
    _ = RF.map ambientUnitToGlobalTwistZero ≫
        ((globalTwistModuleLocalIso 0 i).hom ≫
          (ambientLocalTwistUnitIso 0 i).hom ≫
          (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv) := by
      simp only [Category.assoc]

/-- The restriction of the global geometric terminal map, transported to
the free rank-one chart model. -/
def ambientLocalKoszulZeroToCurve (i : Fin 4) :
    ambientLocalTwistModule 0 i ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        ((Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
          (SheafOfModules.unit
            CanonicalProjectiveCurve25Two.ringCatSheaf)) :=
  (globalTwistModuleLocalIso 0 i).inv ≫
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
      ambientKoszulZeroToCurve

/-- In the standard chart trivialization, the localized global terminal map
is exactly the chart structure-module map constructed above. -/
theorem ambientLocalKoszulZeroToCurve_eq (i : Fin 4) :
    ambientLocalKoszulZeroToCurve i =
      (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i := by
  unfold ambientLocalKoszulZeroToCurve ambientKoszulZeroToCurve
  rw [Functor.map_comp]
  calc
    (globalTwistModuleLocalIso 0 i).inv ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalTwistZeroIsoUnit.hom ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (Scheme.Modules.unitToPushforwardUnit
            canonicalProjectiveCurveMap) =
      ((globalTwistModuleLocalIso 0 i).inv ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          ambientGlobalTwistZeroIsoUnit.hom) ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (Scheme.Modules.unitToPushforwardUnit
            canonicalProjectiveCurveMap) :=
        (Category.assoc _ _ _).symm
    _ = ((ambientLocalTwistUnitIso 0 i).hom ≫
          (Scheme.Modules.restrictUnitIso (ambientChartMap i)).inv) ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (Scheme.Modules.unitToPushforwardUnit
            canonicalProjectiveCurveMap) :=
      congrArg (fun q => q ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
          (Scheme.Modules.unitToPushforwardUnit
            canonicalProjectiveCurveMap))
        (ambientGlobalTwistZeroIsoUnit_restrict i)
    _ = (ambientLocalTwistUnitIso 0 i).hom ≫
        ambientLocalUnitToGlobalCurve i := by
      unfold ambientLocalUnitToGlobalCurve
      exact Category.assoc _ _ _

/-- The local middle Koszul differential is killed by the localization of
the global geometric terminal map. -/
theorem localMiddle_comp_ambientLocalKoszulZeroToCurve (i : Fin 4) :
    ambientLocalKoszulMiddleMap i ≫
        ambientLocalKoszulZeroToCurve i = 0 := by
  rw [ambientLocalKoszulZeroToCurve_eq]
  exact localMiddle_comp_ambientLocalUnitToGlobalCurve i

/-- Restricting the global middle differential and then evaluating in the
local twist model gives the local middle differential followed by the inverse
zero-twist comparison. -/
theorem ambientGlobalKoszulMiddleMap_restrict_inv (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        ambientGlobalKoszulMiddleMap =
      (restrictedAmbientGlobalKoszulMiddleIso i).hom ≫
        ambientLocalKoszulMiddleMap i ≫
          (globalTwistModuleLocalIso 0 i).inv := by
  apply (cancel_mono (globalTwistModuleLocalIso 0 i).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ambientGlobalKoszulMiddleMap_restrict i).symm

/-- On every standard coordinate chart, the global middle differential
followed by the geometric terminal map is zero. -/
theorem ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve_restrict
    (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve) = 0 := by
  rw [Functor.map_comp, ambientGlobalKoszulMiddleMap_restrict_inv]
  simp only [Category.assoc]
  change (restrictedAmbientGlobalKoszulMiddleIso i).hom ≫
      (ambientLocalKoszulMiddleMap i ≫
        ambientLocalKoszulZeroToCurve i) = 0
  rw [localMiddle_comp_ambientLocalKoszulZeroToCurve]
  simp

/-! ## From the coordinate cover back to the ambient scheme -/

/-- The stalk of the global composite is zero at every ambient projective
point.  Choose a standard chart containing the point, use the chartwise
vanishing theorem, and transport it across the canonical restriction--stalk
isomorphism. -/
theorem ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve_stalk
    (x : BinaryProjectiveThreeSpace) :
    (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve) = 0 := by
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
        (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve) = 0 := by
    change G.map
      ((Scheme.Modules.restrictFunctor (ambientChartMap i)).map
        (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve)) = 0
    rw [ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve_restrict]
    exact G.map_zero _ _
  have hAtImage :
      (Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat
            (ambientChartMap i y)).map
        (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve) = 0 := by
    let e := Scheme.Modules.restrictStalkNatIso (ambientChartMap i) y
    apply (cancel_epi (e.hom.app ambientGlobalKoszulMiddle)).1
    rw [← e.hom.naturality]
    rw [hRestricted]
    simp
  rw [← hy]
  exact hAtImage

/-- The global middle Koszul differential is annihilated by the geometric
terminal map.  A morphism of module sheaves is determined sectionwise, and
two sections agree when all their germs agree; the preceding stalk theorem
makes every germ of the composite zero. -/
theorem ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve :
    ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve = 0 := by
  let target :=
    (Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
      (SheafOfModules.unit
        CanonicalProjectiveCurve25Two.ringCatSheaf)
  let F := SheafOfModules.toSheaf
    BinaryProjectiveThreeSpace.ringCatSheaf
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext (F.obj target) U
  intro x hx
  change target.presheaf.germ U x hx
      ((ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve).app U s) =
    target.presheaf.germ U x hx ((0 : ambientGlobalKoszulMiddle ⟶ target).app U s)
  have hRight :
      target.presheaf.germ U x hx
          ((0 : ambientGlobalKoszulMiddle ⟶ target).app U s) = 0 := by
    rw [Scheme.Modules.Hom.zero_app]
    change target.presheaf.germ U x hx 0 = 0
    exact map_zero _
  have hNaturality :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (ambientGlobalKoszulMiddleMap ≫
            ambientKoszulZeroToCurve).mapPresheaf)
          (ambientGlobalKoszulMiddle.presheaf.germ U x hx s) =
        target.presheaf.germ U x hx
          ((ambientGlobalKoszulMiddleMap ≫
            ambientKoszulZeroToCurve).app U s) := by
    simpa only [Scheme.Modules.mapPresheaf_app] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        (ambientGlobalKoszulMiddleMap ≫
          ambientKoszulZeroToCurve).mapPresheaf s)
  have hZero :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (ambientGlobalKoszulMiddleMap ≫
            ambientKoszulZeroToCurve).mapPresheaf)
          (ambientGlobalKoszulMiddle.presheaf.germ U x hx s) = 0 := by
    change ((Scheme.Modules.toPresheaf BinaryProjectiveThreeSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (ambientGlobalKoszulMiddleMap ≫ ambientKoszulZeroToCurve))
        (ambientGlobalKoszulMiddle.presheaf.germ U x hx s) = 0
    rw [ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve_stalk]
    rfl
  exact hNaturality.symm.trans (hZero.trans hRight.symm)

/-! ## Descent through the categorical Koszul quotient -/

/-- The geometric terminal map factors canonically through the cokernel of
the global equation map.  This is the comparison morphism from the abstract
terminal Koszul sheaf to the direct image of the projective curve's structure
sheaf. -/
def ambientGlobalKoszulQuotientToCurve :
    ambientGlobalKoszulQuotient ⟶
      (Scheme.Modules.pushforward canonicalProjectiveCurveMap).obj
        (SheafOfModules.unit
          CanonicalProjectiveCurve25Two.ringCatSheaf) :=
  cokernel.desc ambientGlobalKoszulMiddleMap ambientKoszulZeroToCurve
    ambientGlobalKoszulMiddleMap_comp_ambientKoszulZeroToCurve

/-- The quotient comparison recovers the geometric structure map after the
canonical cokernel projection. -/
theorem ambientGlobalKoszulProjection_comp_quotientToCurve :
    ambientGlobalKoszulProjection ≫ ambientGlobalKoszulQuotientToCurve =
      ambientKoszulZeroToCurve := by
  exact cokernel.π_desc _ _ _

/-- The quotient comparison is surjective because its composite with the
cokernel projection is the already surjective closed-immersion structure
map. -/
instance ambientGlobalKoszulQuotientToCurve_epi :
    Epi ambientGlobalKoszulQuotientToCurve := by
  unfold ambientGlobalKoszulQuotientToCurve
  infer_instance

end MazurProof.RationalPointsN25QuotientTwoAmbientKoszulGeometry
