import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCech
import FLT.Mathlib.AlgebraicGeometry.Modules.AffineDifferentials
import FLT.Mathlib.AlgebraicGeometry.Modules.RelativeDifferentials
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Same-site relative differentials of the N25 canonical curve

The structure morphism of the binary canonical curve defines a base-ring
map on its small Zariski site.  The resulting relative differential
presheaf evaluates objectwise to Kähler differentials.  On each standard
projective chart, the geometric base map becomes the algebra structure used
by the existing affine Kähler calculations after transport to affine
coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoRelativeDifferentials

open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoCanonicalDifferentialTilde
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
open RationalPointsN25QuotientTwoCanonicalDifferentialRestriction
open RationalPointsN25QuotientTwoCanonicalDifferentialCech
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingSheafGluing
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingTransition
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction
open HomogeneousLocalization

/-- The constant binary-base map on the small Zariski site of the canonical
projective curve. -/
def canonicalCurveConstBaseMap :
    (Functor.const CanonicalProjectiveCurve25Two.Opensᵒᵖ).obj (.of k) ⟶
      CanonicalProjectiveCurve25Two.presheaf :=
  Scheme.constBaseMap (.of k) canonicalProjectiveCurveToSpec

/-- The same-site presheaf of relative Kähler differentials of the canonical
projective curve over the binary field. -/
abbrev canonicalRelativeDifferentialsPresheaf :=
  relativeDifferentials' canonicalCurveConstBaseMap

/-- The associated sheaf of the same-site relative differential presheaf. -/
abbrev canonicalRelativeDifferentialsSheaf :
    CanonicalProjectiveCurve25Two.Modules :=
  (PresheafOfModules.sheafification
    (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)).obj
      canonicalRelativeDifferentialsPresheaf

/-- The canonical morphism from relative differential presheaf sections to
their associated sheaf. -/
def canonicalRelativeDifferentialsToSheaf :
    canonicalRelativeDifferentialsPresheaf ⟶
      (SheafOfModules.forget
        CanonicalProjectiveCurve25Two.ringCatSheaf).obj
          canonicalRelativeDifferentialsSheaf :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)).unit.app
      canonicalRelativeDifferentialsPresheaf

/-- The universal same-site derivation with values in the associated
relative differential sheaf. -/
noncomputable def canonicalRelativeDifferentialsSheafDerivation :
    ((SheafOfModules.forget
      CanonicalProjectiveCurve25Two.ringCatSheaf).obj
        canonicalRelativeDifferentialsSheaf).Derivation'
          canonicalCurveConstBaseMap :=
  (derivation' canonicalCurveConstBaseMap).postcomp
    canonicalRelativeDifferentialsToSheaf

/-- Maps from the associated differential sheaf represent compatible
same-site relative derivations. -/
noncomputable def canonicalRelativeDifferentialsSheafHomEquivDerivation
    (F : CanonicalProjectiveCurve25Two.Modules) :
    (canonicalRelativeDifferentialsSheaf ⟶ F) ≃
      ((SheafOfModules.forget
        CanonicalProjectiveCurve25Two.ringCatSheaf).obj F).Derivation'
          canonicalCurveConstBaseMap :=
  (PresheafOfModules.sheafificationHomEquiv
      (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)).trans
    (PresheafOfModules.DifferentialsConstruction.homEquiv
      canonicalCurveConstBaseMap _)

/-- The sheaf morphism represented by a compatible same-site relative
derivation. -/
noncomputable def canonicalRelativeDifferentialsSheafHomOfDerivation
    (F : CanonicalProjectiveCurve25Two.Modules)
    (d : ((SheafOfModules.forget
      CanonicalProjectiveCurve25Two.ringCatSheaf).obj F).Derivation'
        canonicalCurveConstBaseMap) :
    canonicalRelativeDifferentialsSheaf ⟶ F :=
  (canonicalRelativeDifferentialsSheafHomEquivDerivation F).symm d

@[simp]
theorem canonicalRelativeDifferentialsSheafHomEquivDerivation_homOfDerivation
    (F : CanonicalProjectiveCurve25Two.Modules)
    (d : ((SheafOfModules.forget
      CanonicalProjectiveCurve25Two.ringCatSheaf).obj F).Derivation'
        canonicalCurveConstBaseMap) :
    canonicalRelativeDifferentialsSheafHomEquivDerivation F
        (canonicalRelativeDifferentialsSheafHomOfDerivation F d) = d :=
  (canonicalRelativeDifferentialsSheafHomEquivDerivation F).apply_symm_apply d

theorem canonicalRelativeDifferentialsSheafHomEquivDerivation_comp
    {F G : CanonicalProjectiveCurve25Two.Modules}
    (a : canonicalRelativeDifferentialsSheaf ⟶ F) (b : F ⟶ G) :
    canonicalRelativeDifferentialsSheafHomEquivDerivation G (a ≫ b) =
      (canonicalRelativeDifferentialsSheafHomEquivDerivation F a).postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map b) := by
  rfl

/-! ## Descent of chart derivations through the canonical Čech equalizer -/

/-- The underlying module presheaf of a sheaf on the canonical curve. -/
abbrev canonicalModulePresheaf
    (F : CanonicalProjectiveCurve25Two.Modules) :=
  (SheafOfModules.forget.{0}
    CanonicalProjectiveCurve25Two.ringCatSheaf).obj F

noncomputable local instance : PreservesLimit
    (Discrete.functor
      (fun i : Fin 4 => coordinateKaehlerLocalPushforward i))
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf) :=
  (SheafOfModules.forgetPreservesLimitsOfShape
    (Discrete (Fin 4))
    CanonicalProjectiveCurve25Two.ringCatSheaf).preservesLimit

/-- Forgetting the sheaf product gives the product of the forgotten chart
modules. -/
def canonicalKaehlerPiComparisonIso :
    canonicalModulePresheaf kaehlerCechSource ≅
      ∏ᶜ fun i : Fin 4 => canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i) :=
  PreservesProduct.iso
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf)
    (fun i : Fin 4 => coordinateKaehlerLocalPushforward i)

/-- A family of chart derivations determines a derivation into the source of
the canonical Čech equalizer. -/
def kaehlerCechSourceDerivation
    (d : ∀ i : Fin 4,
      (canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i)).Derivation'
          canonicalCurveConstBaseMap) :
    (canonicalModulePresheaf kaehlerCechSource).Derivation'
      canonicalCurveConstBaseMap :=
  (PresheafOfModules.Derivation'.pi
      (fun i : Fin 4 => canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i)) d).postcomp
    canonicalKaehlerPiComparisonIso.inv

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem kaehlerCechSourceDerivation_postcomp_π
    (d : ∀ i : Fin 4,
      (canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i)).Derivation'
          canonicalCurveConstBaseMap) (i : Fin 4) :
    (kaehlerCechSourceDerivation d).postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (CategoryTheory.Limits.Pi.π
              (fun i : Fin 4 => coordinateKaehlerLocalPushforward i) i)) =
      d i := by
  unfold kaehlerCechSourceDerivation
  rw [PresheafOfModules.Derivation'.postcomp_comp]
  rw [← piComparison_comp_π]
  rw [← PreservesProduct.iso_hom]
  unfold canonicalKaehlerPiComparisonIso
  rw [Iso.inv_hom_id_assoc]
  exact PresheafOfModules.Derivation'.pi_postcomp_π _ d i

noncomputable local instance : PreservesLimit
    (parallelPair kaehlerCechLeft kaehlerCechRight)
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf) :=
  (SheafOfModules.forgetPreservesLimitsOfShape
    WalkingParallelPair
    CanonicalProjectiveCurve25Two.ringCatSheaf).preservesLimit

/-- Forgetting the sheaf equalizer gives the equalizer of the forgotten
Čech arrows. -/
def canonicalKaehlerEqualizerComparisonIso :
    canonicalModulePresheaf globalKaehlerDifferentialModule ≅
      equalizer
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft)
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechRight) :=
  PreservesEqualizer.iso
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf)
    kaehlerCechLeft kaehlerCechRight

/-- A compatible family of chart derivations descends through the canonical
sheaf Čech equalizer. -/
def globalKaehlerDifferentialDerivation
    (d : ∀ i : Fin 4,
      (canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i)).Derivation'
          canonicalCurveConstBaseMap)
    (h : (kaehlerCechSourceDerivation d).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft) =
        (kaehlerCechSourceDerivation d).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechRight)) :
    (canonicalModulePresheaf globalKaehlerDifferentialModule).Derivation'
      canonicalCurveConstBaseMap :=
  (PresheafOfModules.Derivation'.equalizerLift
      (kaehlerCechSourceDerivation d)
      ((SheafOfModules.forget.{0}
        CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft)
      ((SheafOfModules.forget.{0}
        CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechRight) h).postcomp
    canonicalKaehlerEqualizerComparisonIso.inv

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem globalKaehlerDifferentialDerivation_postcomp_ι
    (d : ∀ i : Fin 4,
      (canonicalModulePresheaf
        (coordinateKaehlerLocalPushforward i)).Derivation'
          canonicalCurveConstBaseMap)
    (h : (kaehlerCechSourceDerivation d).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft) =
        (kaehlerCechSourceDerivation d).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechRight)) :
    (globalKaehlerDifferentialDerivation d h).postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (equalizer.ι kaehlerCechLeft kaehlerCechRight)) =
      kaehlerCechSourceDerivation d := by
  unfold globalKaehlerDifferentialDerivation
  rw [PresheafOfModules.Derivation'.postcomp_comp]
  unfold canonicalKaehlerEqualizerComparisonIso
  rw [PreservesEqualizer.iso_inv_ι]
  exact PresheafOfModules.Derivation'.equalizerLift_postcomp_ι _ _ _ _

@[simp]
theorem canonicalRelativeDifferentialsPresheaf_obj
    (U : CanonicalProjectiveCurve25Two.Opensᵒᵖ) :
    canonicalRelativeDifferentialsPresheaf.obj U =
      CommRingCat.KaehlerDifferential (canonicalCurveConstBaseMap.app U) :=
  rfl

/-- The standard chart's section ring expressed in its affine spectrum
coordinates. -/
def canonicalCurveChartSectionIso (i : Fin 4) :
    Γ(CanonicalProjectiveCurve25Two,
        coordinateChartMap i ''ᵁ (⊤ : (coordinateChartScheme i).Opens)) ≅
      CommRingCat.of (coordinateChartRing i) :=
  (coordinateChartMap i).appIso ⊤ ≪≫
    Scheme.ΓSpecIso (.of (coordinateChartRing i))

/-- The base map seen in the affine coordinates of a standard chart. -/
def canonicalCurveChartBaseMap (i : Fin 4) :
    CommRingCat.of k ⟶ CommRingCat.of (coordinateChartRing i) :=
  canonicalCurveConstBaseMap.app
      (.op (coordinateChartMap i ''ᵁ (⊤ : (coordinateChartScheme i).Opens))) ≫
    (canonicalCurveChartSectionIso i).hom

/-- On every standard chart, the geometric structure morphism induces the
canonical binary-field algebra structure. -/
theorem canonicalCurveChartBaseMap_eq_algebraMap (i : Fin 4) :
    canonicalCurveChartBaseMap i =
      CommRingCat.ofHom (algebraMap k (coordinateChartRing i)) := by
  apply CommRingCat.hom_ext
  exact @RingHom.ext_zmod 2 (coordinateChartRing i) _ _ _

/-! ## Chart derivations -/

/-- Pulling a binary constant from the canonical curve to a standard chart
agrees with the affine algebra structure on every open. -/
theorem coordinateChart_base_compat (i : Fin 4)
    (U : CanonicalProjectiveCurve25Two.Opensᵒᵖ) (r : k) :
    (coordinateChartMap i).app U.unop
        (canonicalCurveConstBaseMap.app U r) =
      (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i))).app
        (.op (coordinateChartMap i ⁻¹ᵁ U.unop)) r := by
  rw [← CommRingCat.comp_apply]
  exact DFunLike.congr_fun
    (@RingHom.ext_zmod 2
      ((coordinateChartScheme i).presheaf.obj
        (.op (coordinateChartMap i ⁻¹ᵁ U.unop))) _ _ _) r

/-- The chart pullback square for constants, packaged as an equality of
ring morphisms for precomposition of relative derivations. -/
theorem coordinateChart_base_compat_hom (i : Fin 4)
    (U : CanonicalProjectiveCurve25Two.Opensᵒᵖ) :
    canonicalCurveConstBaseMap.app U ≫
        (coordinateChartMap i).app U.unop =
      (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i))).app
        (.op (coordinateChartMap i ⁻¹ᵁ U.unop)) := by
  apply CommRingCat.hom_ext
  ext r
  exact coordinateChart_base_compat i U r

/-! ## Restriction of the global relative differential sheaf to a chart -/

/-- The open-immersion section isomorphism transports the affine base map to
the global constant base map. -/
theorem coordinateChart_appIso_inv_base_compat (i : Fin 4)
    (U : (coordinateChartScheme i).Opensᵒᵖ) :
    (affineConstBaseMap (.of k)
        (.of (ChartCoordinateRing i))).app U ≫
      ((coordinateChartMap i).appIso U.unop).inv =
    canonicalCurveConstBaseMap.app
      (.op (coordinateChartMap i ''ᵁ U.unop)) := by
  apply CommRingCat.hom_ext
  exact @RingHom.ext_zmod 2 _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The transported global derivation commutes with restriction inside a
standard affine chart. -/
theorem coordinateChartRestrictedRelativeDerivation_naturality (i : Fin 4)
    {U V : (coordinateChartScheme i).Opensᵒᵖ} (h : U ⟶ V)
    (x : (coordinateChartScheme i).presheaf.obj U) :
    canonicalRelativeDifferentialsSheafDerivation.d
        (((coordinateChartMap i).appIso V.unop).inv
          ((coordinateChartScheme i).presheaf.map h x)) =
      (canonicalRelativeDifferentialsSheaf.presheaf.map
        ((coordinateChartMap i).opensFunctor.op.map h))
          (canonicalRelativeDifferentialsSheafDerivation.d
            (((coordinateChartMap i).appIso U.unop).inv x)) := by
  calc
    _ = canonicalRelativeDifferentialsSheafDerivation.d
        (CanonicalProjectiveCurve25Two.presheaf.map
          ((coordinateChartMap i).opensFunctor.op.map h)
            (((coordinateChartMap i).appIso U.unop).inv x)) := by
      congr 1
      exact CategoryTheory.congr_fun
        (Scheme.Hom.appIso_inv_naturality (coordinateChartMap i) h) x
    _ = _ := PresheafOfModules.Derivation.d_map
      canonicalRelativeDifferentialsSheafDerivation _ _

set_option backward.isDefEq.respectTransparency false in
/-- The global universal relative derivation transported to a standard affine
chart through the open-immersion section isomorphism. -/
def coordinateChartRestrictedRelativeDerivation (i : Fin 4) :
    ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
      canonicalRelativeDifferentialsSheaf).val.Derivation'
        (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i))) :=
  PresheafOfModules.Derivation'.mk
    (fun U => ModuleCat.Derivation.precomp
      (canonicalRelativeDifferentialsSheafDerivation.app
        (.op (coordinateChartMap i ''ᵁ U.unop)))
      ((coordinateChartMap i).appIso U.unop).inv
      (coordinateChart_appIso_inv_base_compat i U))
    (by
      intro U V h x
      exact coordinateChartRestrictedRelativeDerivation_naturality i h x)

/-- The affine relative differential presheaf maps to the restriction of the
global relative differential sheaf through the transported derivation. -/
def coordinateChartRelativeDifferentialsToRestrictedSheaf (i : Fin 4) :
    affineRelativeDifferentialsPresheaf (.of k)
        (.of (ChartCoordinateRing i)) ⟶
      ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        canonicalRelativeDifferentialsSheaf).val :=
  (isUniversal'
    (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i)))).desc
      (coordinateChartRestrictedRelativeDerivation i)

@[simp]
theorem coordinateChartRelativeDifferentialsToRestrictedSheaf_fac
    (i : Fin 4) :
    (derivation'
      (affineConstBaseMap (.of k)
        (.of (ChartCoordinateRing i)))).postcomp
          (coordinateChartRelativeDifferentialsToRestrictedSheaf i) =
      coordinateChartRestrictedRelativeDerivation i := by
  exact (isUniversal'
    (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i)))).fac _

@[simp]
theorem coordinateChartRelativeDifferentialsToRestrictedSheaf_app_d
    (i : Fin 4) (U : (coordinateChartScheme i).Opensᵒᵖ)
    (x : (coordinateChartScheme i).presheaf.obj U) :
    (coordinateChartRelativeDifferentialsToRestrictedSheaf i).app U
        (CommRingCat.KaehlerDifferential.d x) =
      canonicalRelativeDifferentialsSheafDerivation.d
        (((coordinateChartMap i).appIso U.unop).inv x) := by
  have h := congrArg (fun d ↦ d.d x)
    (coordinateChartRelativeDifferentialsToRestrictedSheaf_fac i)
  exact h

set_option maxHeartbeats 800000 in
-- The pushforward module action unfolds through the chart open immersion.
set_option backward.isDefEq.respectTransparency false in
/-- The universal affine derivation on a standard chart, extended by zero
through the chart open immersion to the canonical curve. -/
def coordinateChartDerivation (i : Fin 4) :
    (canonicalModulePresheaf
      (coordinateKaehlerLocalPushforward i)).Derivation'
        canonicalCurveConstBaseMap :=
  PresheafOfModules.Derivation'.mk
    (fun U => ModuleCat.Derivation.precomp
      ((affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing i))).app
          (.op (coordinateChartMap i ⁻¹ᵁ U.unop)))
      ((coordinateChartMap i).app U.unop)
      (coordinateChart_base_compat_hom i U))
    (by
      intro U V h x
      dsimp only [ModuleCat.Derivation.precomp]
      change (affineUniversalDerivation (.of k)
          (.of (ChartCoordinateRing i))).d
          ((coordinateChartMap i).app V.unop
            (CanonicalProjectiveCurve25Two.presheaf.map h x)) =
        (chartCoordinateKaehlerDifferentialSheaf i).presheaf.map
          (((TopologicalSpace.Opens.map
            (coordinateChartMap i).base).map h.unop).op)
          ((affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing i))).d
            ((coordinateChartMap i).app U.unop x))
      calc
        _ = (affineUniversalDerivation (.of k)
              (.of (ChartCoordinateRing i))).d
              ((coordinateChartScheme i).presheaf.map
                (((TopologicalSpace.Opens.map
                  (coordinateChartMap i).base).map h.unop).op)
                ((coordinateChartMap i).app U.unop x)) := by
            congr 1
            exact CategoryTheory.congr_fun
              ((coordinateChartMap i).naturality h) x
        _ = _ := PresheafOfModules.Derivation.d_map
          (affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing i))) _ _)

/-- The binary base map pulled to an ordered overlap agrees with its affine
base map, as an equality suitable for derivation precomposition. -/
theorem coordinateOverlap_base_compat_hom (i j : Fin 4)
    (U : CanonicalProjectiveCurve25Two.Opensᵒᵖ) :
    canonicalCurveConstBaseMap.app U ≫
        (coordinateOverlapMap i j).app U.unop =
      (affineConstBaseMap (.of k) (.of (coordinateOverlapRing i j))).app
        (.op (coordinateOverlapMap i j ⁻¹ᵁ U.unop)) := by
  apply CommRingCat.hom_ext
  exact @RingHom.ext_zmod 2
    ((Spec (.of (coordinateOverlapRing i j))).presheaf.obj
      (.op (coordinateOverlapMap i j ⁻¹ᵁ U.unop))) _ _ _

set_option maxHeartbeats 800000 in
-- The pushforward module action unfolds through the ordered overlap map.
set_option backward.isDefEq.respectTransparency false in
/-- The universal affine derivation on an ordered overlap, extended by zero
to the canonical curve. -/
def coordinateOverlapDerivation (i j : Fin 4) :
    (canonicalModulePresheaf
      (coordinateKaehlerOverlapPushforward (i, j))).Derivation'
        canonicalCurveConstBaseMap :=
  PresheafOfModules.Derivation'.mk
    (fun U => ModuleCat.Derivation.precomp
      ((affineUniversalDerivation (.of k)
        (.of (coordinateOverlapRing i j))).app
          (.op (coordinateOverlapMap i j ⁻¹ᵁ U.unop)))
      ((coordinateOverlapMap i j).app U.unop)
      (coordinateOverlap_base_compat_hom i j U))
    (by
      intro U V h x
      dsimp only [ModuleCat.Derivation.precomp]
      change (affineUniversalDerivation (.of k)
          (.of (coordinateOverlapRing i j))).d
          ((coordinateOverlapMap i j).app V.unop
            (CanonicalProjectiveCurve25Two.presheaf.map h x)) =
        (coordinateOverlapKaehlerDifferentialSheaf i j).presheaf.map
          (((TopologicalSpace.Opens.map
            (coordinateOverlapMap i j).base).map h.unop).op)
          ((affineUniversalDerivation (.of k)
            (.of (coordinateOverlapRing i j))).d
            ((coordinateOverlapMap i j).app U.unop x))
      calc
        _ = (affineUniversalDerivation (.of k)
              (.of (coordinateOverlapRing i j))).d
              ((Spec (.of (coordinateOverlapRing i j))).presheaf.map
                (((TopologicalSpace.Opens.map
                  (coordinateOverlapMap i j).base).map h.unop).op)
                ((coordinateOverlapMap i j).app U.unop x)) := by
            congr 1
            exact CategoryTheory.congr_fun
              ((coordinateOverlapMap i j).naturality h) x
        _ = _ := PresheafOfModules.Derivation.d_map
          (affineUniversalDerivation (.of k)
            (.of (coordinateOverlapRing i j))) _ _)

/-! ## Transported affine derivations on ordered overlaps -/

/-- The affine structure map of the first overlap projection respects the
binary base after the open-immersion section isomorphism. -/
theorem coordinateOverlapLeft_appIso_inv_base_compat (i j : Fin 4)
    (U : (Spec (.of (coordinateOverlapRing i j))).Opensᵒᵖ) :
    (affineConstBaseMap (.of k) (.of (coordinateOverlapRing i j))).app U ≫
        ((Spec.map (CommRingCat.ofHom
          (coordinateChartToLeftOverlapRingHom i j))).appIso U.unop).inv =
      (affineConstBaseMap (.of k) (.of (ChartCoordinateRing i))).app
        (.op (Spec.map (CommRingCat.ofHom
          (coordinateChartToLeftOverlapRingHom i j)) ''ᵁ U.unop)) := by
  apply CommRingCat.hom_ext
  exact @RingHom.ext_zmod 2 _ _ _ _

set_option maxHeartbeats 800000 in
-- Naturality crosses the open-immersion section isomorphism and restricted module sheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Transporting the affine universal derivation through the first overlap
projection commutes with restriction of sections. -/
theorem coordinateOverlapLeftTransportedDerivation_naturality (i j : Fin 4)
    {U V : (Spec (.of (coordinateOverlapRing i j))).Opensᵒᵖ}
    (h : U ⟶ V)
    (x : (Spec (.of (coordinateOverlapRing i j))).presheaf.obj U) :
    (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app V.unop
          ((affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing i))).d
              (((Spec.map (CommRingCat.ofHom
                (coordinateChartToLeftOverlapRingHom i j))).appIso
                  V.unop).inv
                    ((Spec (.of (coordinateOverlapRing i j))).presheaf.map h x))) =
      ((coordinateOverlapKaehlerDifferentialSheaf i j).val.map h).hom
        ((coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app U.unop
          ((affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing i))).d
              (((Spec.map (CommRingCat.ofHom
                (coordinateChartToLeftOverlapRingHom i j))).appIso
                  U.unop).inv x))) := by
  let g := Spec.map (CommRingCat.ofHom
    (coordinateChartToLeftOverlapRingHom i j))
  let E := (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
  let D := affineUniversalDerivation (.of k)
    (.of (ChartCoordinateRing i))
  calc
    _ = E.app V.unop
        (D.d ((coordinateChartScheme i).presheaf.map
          (g.opensFunctor.op.map h)
            ((g.appIso U.unop).inv x))) := by
      congr 2
      exact CategoryTheory.congr_fun
        (Scheme.Hom.appIso_inv_naturality g h) x
    _ = E.app V.unop
        (((chartCoordinateKaehlerDifferentialSheaf i).val.map
          (g.opensFunctor.op.map h)).hom
            (D.d ((g.appIso U.unop).inv x))) := by
      exact congrArg (fun z ↦ E.app V.unop z)
        (PresheafOfModules.Derivation.d_map D
          (g.opensFunctor.op.map h) ((g.appIso U.unop).inv x))
    _ = _ := by
      exact PresheafOfModules.naturality_apply E.val h
        (D.d ((g.appIso U.unop).inv x))

set_option maxHeartbeats 800000 in
-- The Leibniz law compares scalar actions before and after canonical Kähler base change.
set_option backward.isDefEq.respectTransparency false in
/-- The first chart universal derivation transported to the ordered overlap
through the open-immersion section isomorphism and canonical Kähler base
change. -/
def coordinateOverlapLeftTransportedDerivation (i j : Fin 4) :
    (coordinateOverlapKaehlerDifferentialSheaf i j).val.Derivation'
      (affineConstBaseMap (.of k) (.of (coordinateOverlapRing i j))) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦
      let g := Spec.map (CommRingCat.ofHom
        (coordinateChartToLeftOverlapRingHom i j))
      let D := (affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing i))).app (.op (g ''ᵁ U.unop))
      ModuleCat.Derivation.mk
        (fun x ↦
          (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app U.unop
            (D.d ((g.appIso U.unop).inv x)))
        (by simp [D])
        (by
          intro x y
          let E := (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
          let e := E.app U.unop
          let N := ((Scheme.Modules.restrictFunctor g).obj
            (chartCoordinateKaehlerDifferentialSheaf i)).val.obj U
          let P := (coordinateOverlapKaehlerDifferentialSheaf i j).val.obj U
          let a := (g.appIso U.unop).inv x
          let b := (g.appIso U.unop).inv y
          have hd := D.d_mul ((g.appIso U.unop).inv x)
            ((g.appIso U.unop).inv y)
          change (show N from D.d (a * b)) =
            x • (show N from D.d b) + y • (show N from D.d a) at hd
          rw [map_mul]
          change (show P from e (show N from D.d (a * b))) =
            x • (show P from e (show N from D.d b)) +
              y • (show P from e (show N from D.d a))
          calc
            _ = e (x • (show N from D.d b) +
                y • (show N from D.d a)) := congrArg e hd
            _ = e (x • (show N from D.d b)) +
                e (y • (show N from D.d a)) := e.hom.map_add _ _
            _ = _ := congrArg₂ (fun s t ↦ s + t)
              (E.app_smul x (show N from D.d b))
              (E.app_smul y (show N from D.d a)))
        (by
          intro r
          have hb := CategoryTheory.congr_fun
            (coordinateOverlapLeft_appIso_inv_base_compat i j U) r
          change ((g.appIso U.unop).inv
              ((affineConstBaseMap (.of k)
                (.of (coordinateOverlapRing i j))).app U r)) =
            (affineConstBaseMap (.of k)
              (.of (ChartCoordinateRing i))).app
                (.op (g ''ᵁ U.unop)) r at hb
          change (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app
              U.unop (D.d _) = 0
          calc
            _ = (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app
                U.unop
                (D.d ((affineConstBaseMap (.of k)
                  (.of (ChartCoordinateRing i))).app
                    (.op (g ''ᵁ U.unop)) r)) := congrArg
                      (fun z ↦
                        (coordinateKaehlerRestrictLeftSpecCanonicalIso
                          i j).hom.app U.unop (D.d z)) hb
            _ = (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app
                U.unop 0 := congrArg
                  (fun z ↦
                    (coordinateKaehlerRestrictLeftSpecCanonicalIso
                      i j).hom.app U.unop z) (D.d_map r)
            _ = 0 := map_zero _))
    (by
      intro U V h x
      exact coordinateOverlapLeftTransportedDerivation_naturality i j h x)

/-- The affine structure map of the second overlap projection respects the
binary base after the open-immersion section isomorphism. -/
theorem coordinateOverlapRight_appIso_inv_base_compat (i j : Fin 4)
    (U : (Spec (.of (coordinateOverlapRing i j))).Opensᵒᵖ) :
    (affineConstBaseMap (.of k) (.of (coordinateOverlapRing i j))).app U ≫
        ((Spec.map (CommRingCat.ofHom
          (coordinateChartToRightOverlapRingHom i j))).appIso U.unop).inv =
      (affineConstBaseMap (.of k) (.of (ChartCoordinateRing j))).app
        (.op (Spec.map (CommRingCat.ofHom
          (coordinateChartToRightOverlapRingHom i j)) ''ᵁ U.unop)) := by
  apply CommRingCat.hom_ext
  exact @RingHom.ext_zmod 2 _ _ _ _

set_option maxHeartbeats 800000 in
-- Naturality crosses the open-immersion section isomorphism and restricted module sheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Transporting the affine universal derivation through the second overlap
projection commutes with restriction of sections. -/
theorem coordinateOverlapRightTransportedDerivation_naturality (i j : Fin 4)
    {U V : (Spec (.of (coordinateOverlapRing i j))).Opensᵒᵖ}
    (h : U ⟶ V)
    (x : (Spec (.of (coordinateOverlapRing i j))).presheaf.obj U) :
    (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app V.unop
          ((affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing j))).d
              (((Spec.map (CommRingCat.ofHom
                (coordinateChartToRightOverlapRingHom i j))).appIso
                  V.unop).inv
                    ((Spec (.of (coordinateOverlapRing i j))).presheaf.map h x))) =
      ((coordinateOverlapKaehlerDifferentialSheaf i j).val.map h).hom
        ((coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app U.unop
          ((affineUniversalDerivation (.of k)
            (.of (ChartCoordinateRing j))).d
              (((Spec.map (CommRingCat.ofHom
                (coordinateChartToRightOverlapRingHom i j))).appIso
                  U.unop).inv x))) := by
  let g := Spec.map (CommRingCat.ofHom
    (coordinateChartToRightOverlapRingHom i j))
  let E := (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
  let D := affineUniversalDerivation (.of k)
    (.of (ChartCoordinateRing j))
  calc
    _ = E.app V.unop
        (D.d ((coordinateChartScheme j).presheaf.map
          (g.opensFunctor.op.map h)
            ((g.appIso U.unop).inv x))) := by
      congr 2
      exact CategoryTheory.congr_fun
        (Scheme.Hom.appIso_inv_naturality g h) x
    _ = E.app V.unop
        (((chartCoordinateKaehlerDifferentialSheaf j).val.map
          (g.opensFunctor.op.map h)).hom
            (D.d ((g.appIso U.unop).inv x))) := by
      exact congrArg (fun z ↦ E.app V.unop z)
        (PresheafOfModules.Derivation.d_map D
          (g.opensFunctor.op.map h) ((g.appIso U.unop).inv x))
    _ = _ := by
      exact PresheafOfModules.naturality_apply E.val h
        (D.d ((g.appIso U.unop).inv x))

set_option maxHeartbeats 800000 in
-- The Leibniz law compares scalar actions before and after canonical Kähler base change.
set_option backward.isDefEq.respectTransparency false in
/-- The second chart universal derivation transported to the ordered overlap
through the open-immersion section isomorphism and canonical Kähler base
change. -/
def coordinateOverlapRightTransportedDerivation (i j : Fin 4) :
    (coordinateOverlapKaehlerDifferentialSheaf i j).val.Derivation'
      (affineConstBaseMap (.of k) (.of (coordinateOverlapRing i j))) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦
      let g := Spec.map (CommRingCat.ofHom
        (coordinateChartToRightOverlapRingHom i j))
      let D := (affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing j))).app (.op (g ''ᵁ U.unop))
      ModuleCat.Derivation.mk
        (fun x ↦
          (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app U.unop
            (D.d ((g.appIso U.unop).inv x)))
        (by simp [D])
        (by
          intro x y
          let E := (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
          let e := E.app U.unop
          let N := ((Scheme.Modules.restrictFunctor g).obj
            (chartCoordinateKaehlerDifferentialSheaf j)).val.obj U
          let P := (coordinateOverlapKaehlerDifferentialSheaf i j).val.obj U
          let a := (g.appIso U.unop).inv x
          let b := (g.appIso U.unop).inv y
          have hd := D.d_mul ((g.appIso U.unop).inv x)
            ((g.appIso U.unop).inv y)
          change (show N from D.d (a * b)) =
            x • (show N from D.d b) + y • (show N from D.d a) at hd
          rw [map_mul]
          change (show P from e (show N from D.d (a * b))) =
            x • (show P from e (show N from D.d b)) +
              y • (show P from e (show N from D.d a))
          calc
            _ = e (x • (show N from D.d b) +
                y • (show N from D.d a)) := congrArg e hd
            _ = e (x • (show N from D.d b)) +
                e (y • (show N from D.d a)) := e.hom.map_add _ _
            _ = _ := congrArg₂ (fun s t ↦ s + t)
              (E.app_smul x (show N from D.d b))
              (E.app_smul y (show N from D.d a)))
        (by
          intro r
          have hb := CategoryTheory.congr_fun
            (coordinateOverlapRight_appIso_inv_base_compat i j U) r
          change ((g.appIso U.unop).inv
              ((affineConstBaseMap (.of k)
                (.of (coordinateOverlapRing i j))).app U r)) =
            (affineConstBaseMap (.of k)
              (.of (ChartCoordinateRing j))).app
                (.op (g ''ᵁ U.unop)) r at hb
          change (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app
              U.unop (D.d _) = 0
          calc
            _ = (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app
                U.unop
                (D.d ((affineConstBaseMap (.of k)
                  (.of (ChartCoordinateRing j))).app
                    (.op (g ''ᵁ U.unop)) r)) := congrArg
                      (fun z ↦
                        (coordinateKaehlerRestrictRightSpecCanonicalIso
                          i j).hom.app U.unop (D.d z)) hb
            _ = (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app
                U.unop 0 := congrArg
                  (fun z ↦
                    (coordinateKaehlerRestrictRightSpecCanonicalIso
                      i j).hom.app U.unop z) (D.d_map r)
            _ = 0 := map_zero _))
    (by
      intro U V h x
      exact coordinateOverlapRightTransportedDerivation_naturality i j h x)

/-! ## Universal differentials on ordered overlaps -/

/-- The canonical first-chart restriction sends a universal differential to
the differential of the localized section. -/
theorem coordinateKaehlerRestrictLeftSpecCanonicalIso_normalizedTop_D
    (i j : Fin 4) (x : ChartCoordinateRing i) :
    normalizedTildeTop
        (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
        (coordinateKaehlerLeftLocalizationGlobalMap i j
          (KaehlerDifferential.D k (ChartCoordinateRing i) x)) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToLeftOverlapRingHom i j x) := by
  rw [coordinateKaehlerRestrictLeftSpecCanonicalIso_normalizedTop_apply,
    coordinateOverlapLeftKaehlerDifferentialMap_D]

/-- The canonical second-chart restriction sends a universal differential to
the differential of the localized section. -/
theorem coordinateKaehlerRestrictRightSpecCanonicalIso_normalizedTop_D
    (i j : Fin 4) (x : ChartCoordinateRing j) :
    normalizedTildeTop
        (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
        (coordinateKaehlerRightLocalizationGlobalMap i j
          (KaehlerDifferential.D k (ChartCoordinateRing j) x)) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToRightOverlapRingHom i j x) := by
  rw [coordinateKaehlerRestrictRightSpecCanonicalIso_normalizedTop_apply,
    coordinateOverlapRightKaehlerDifferentialMap_D]

/-! ## Identification of transported overlap derivations -/

/-- The normalized top component of the first transported overlap derivation. -/
def coordinateOverlapLeftNormalizedTopDerivation (i j : Fin 4) :
    (ModuleCat.of (coordinateOverlapRing i j)
      (KaehlerDifferential k (coordinateOverlapRing i j))).Derivation
        (CommRingCat.ofHom (algebraMap k (coordinateOverlapRing i j))) :=
  normalizedTopDerivation (.of k) (.of (coordinateOverlapRing i j))
    (ModuleCat.of (coordinateOverlapRing i j)
      (KaehlerDifferential k (coordinateOverlapRing i j)))
    (coordinateOverlapLeftTransportedDerivation i j)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized first transported derivation agrees with the universal
differential on chart generators. -/
theorem coordinateOverlapLeftNormalizedTopDerivation_apply_chart
    (i j : Fin 4) (x : ChartCoordinateRing i) :
    (coordinateOverlapLeftNormalizedTopDerivation i j).d
        (coordinateChartToLeftOverlapRingHom i j x) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToLeftOverlapRingHom i j x) := by
  let g := CommRingCat.ofHom (coordinateChartToLeftOverlapRingHom i j)
  let G := Spec.map g
  change (tilde.isoTop (R := .of (coordinateOverlapRing i j))
      (ModuleCat.of (coordinateOverlapRing i j)
        (KaehlerDifferential k (coordinateOverlapRing i j)))).inv
    ((coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app ⊤
      ((affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing i))).d
        ((G.appIso ⊤).inv
          ((Scheme.ΓSpecIso (.of (coordinateOverlapRing i j))).inv
            (g x))))) = _
  change (tilde.isoTop (R := .of (coordinateOverlapRing i j))
      (ModuleCat.of (coordinateOverlapRing i j)
        (KaehlerDifferential k (coordinateOverlapRing i j)))).inv
    ((coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom.app ⊤
      ((affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing i))).d
        ((G.appIso ⊤).inv
          ((tilde.toOpen (R := .of (coordinateOverlapRing i j))
            (ModuleCat.of (coordinateOverlapRing i j)
              (coordinateOverlapRing i j)) ⊤) (g x))))) = _
  rw [Scheme.Modules.specMap_appIso_inv_tildeSelf_toOpen_apply]
  have hD := affineUniversalDerivation_toOpen
    (.of k) (.of (ChartCoordinateRing i)) (G ''ᵁ ⊤) x
  change (affineUniversalDerivation (.of k)
      (.of (ChartCoordinateRing i))).d
        ((tilde.toOpen (R := .of (ChartCoordinateRing i))
          (ModuleCat.of (ChartCoordinateRing i) (ChartCoordinateRing i))
          (G ''ᵁ ⊤)) x) =
    (tilde.toOpen (R := .of (ChartCoordinateRing i))
      (ModuleCat.of (ChartCoordinateRing i)
        (KaehlerDifferential k (ChartCoordinateRing i)))
      (G ''ᵁ ⊤))
        (KaehlerDifferential.D k (ChartCoordinateRing i) x) at hD
  erw [hD]
  exact coordinateKaehlerRestrictLeftSpecCanonicalIso_normalizedTop_D i j x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Localization extensionality identifies the normalized first transported
derivation with the universal derivation on the overlap ring. -/
theorem coordinateOverlapLeftNormalizedTopDerivation_eq (i j : Fin 4) :
    coordinateOverlapLeftNormalizedTopDerivation i j =
      KaehlerDifferential.D k (coordinateOverlapRing i j) := by
  let S := ChartCoordinateRing i
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
    (coordinateClass_mem_degreeOne j)
  letI : Algebra S T := (coordinateChartToLeftOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToLeftOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  letI : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' rfl
  apply AlgebraicGeometry.Derivation.ext_of_isLocalization
    (k := k) (R := S) (T := T)
      (N := KaehlerDifferential k T) (.powers r)
  intro x
  change (coordinateOverlapLeftNormalizedTopDerivation i j).d
      (coordinateChartToLeftOverlapRingHom i j x) = _
  exact coordinateOverlapLeftNormalizedTopDerivation_apply_chart i j x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Transport through the first chart restriction recovers the affine
universal derivation on the entire ordered overlap. -/
theorem coordinateOverlapLeftTransportedDerivation_eq (i j : Fin 4) :
    coordinateOverlapLeftTransportedDerivation i j =
      affineUniversalDerivation (.of k) (.of (coordinateOverlapRing i j)) := by
  apply PresheafOfModules.Derivation'.ext_of_affine_top
  intro x
  let T := coordinateOverlapRing i j
  let e := tilde.isoTop
    (R := .of T) (ModuleCat.of T (KaehlerDifferential k T))
  let t : T := (Scheme.ΓSpecIso (.of T)).hom x
  have h := congrArg (fun D => D.d t)
    (coordinateOverlapLeftNormalizedTopDerivation_eq i j)
  have ha := affineUniversalDerivation_normalizedTop
    (.of k) (.of T) t
  change e.inv
      ((coordinateOverlapLeftTransportedDerivation i j).d
        ((Scheme.ΓSpecIso (.of T)).inv t)) =
    KaehlerDifferential.D k T t at h
  change e.inv
      ((affineUniversalDerivation (.of k) (.of T)).d
        ((Scheme.ΓSpecIso (.of T)).inv t)) =
    KaehlerDifferential.D k T t at ha
  have ht : (Scheme.ΓSpecIso (.of T)).inv t = x := by
    dsimp only [t]
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of T)) x
  rw [ht] at h ha
  have hn : e.inv
      ((coordinateOverlapLeftTransportedDerivation i j).d x) =
    e.inv ((affineUniversalDerivation (.of k) (.of T)).d x) := by
    exact h.trans ha.symm
  have := congrArg (fun z => e.hom z) hn
  simpa only [Iso.inv_hom_id_apply] using this

set_option maxHeartbeats 0 in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the first chart derivation to an ordered overlap recovers
the overlap's universal derivation. -/
theorem coordinateChartDerivation_postcomp_left (i j : Fin 4) :
    (coordinateChartDerivation i).postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (pushforwardRestrictionHom
              (coordinateOverlapToLeft i j)
              (coordinateChartMap i)
              (coordinateOverlapMap i j)
              rfl
              (chartCoordinateKaehlerDifferentialSheaf i)
              (coordinateOverlapKaehlerDifferentialSheaf i j)
              (coordinateKaehlerRestrictLeftIso i j))) =
      coordinateOverlapDerivation i j := by
  apply PresheafOfModules.Derivation.ext
  funext U
  apply AddMonoidHom.ext
  intro x
  rw [PresheafOfModules.Derivation.postcomp_d_apply]
  change (pushforwardRestrictionHom
        (coordinateOverlapToLeft i j)
        (coordinateChartMap i)
        (coordinateOverlapMap i j)
        rfl
        (chartCoordinateKaehlerDifferentialSheaf i)
        (coordinateOverlapKaehlerDifferentialSheaf i j)
        (coordinateKaehlerRestrictLeftIso i j)).app U.unop
      ((coordinateChartDerivation i).d x) =
    (coordinateOverlapDerivation i j).d x
  unfold pushforwardRestrictionHom
  unfold coordinateOverlapMap
  rw [Scheme.Modules.pushforwardRestrictionHomOfHom_app_rfl]
  change (((chartCoordinateKaehlerDifferentialSheaf i).presheaf.map
        (homOfLE ((coordinateOverlapToLeft i j).image_preimage_le
          (coordinateChartMap i ⁻¹ᵁ U.unop))).op ≫
      (coordinateKaehlerRestrictLeftIso i j).hom.app
        (coordinateOverlapToLeft i j ⁻¹ᵁ
          coordinateChartMap i ⁻¹ᵁ U.unop)).hom)
      (((coordinateChartDerivation i).app U).d x) =
    ((coordinateOverlapDerivation i j).app U).d x
  simp only [coordinateChartDerivation, coordinateOverlapDerivation,
    PresheafOfModules.Derivation'.mk_app]
  dsimp only [ModuleCat.Derivation.precomp, ModuleCat.Derivation.d,
    ModuleCat.Derivation.mk]
  unfold coordinateKaehlerRestrictLeftIso
  unfold coordinateKaehlerRestrictLeftCanonicalIso
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app]
  rw [← coordinateOverlapLeftTransportedDerivation_eq]
  simp only [coordinateOverlapLeftTransportedDerivation,
    PresheafOfModules.Derivation'.mk_app]
  dsimp only [ModuleCat.Derivation.d, ModuleCat.Derivation.mk]
  simp only [CategoryTheory.comp_apply]
  let E := (coordinateKaehlerRestrictLeftSpecCanonicalIso i j).hom
  let V := coordinateOverlapMap i j ⁻¹ᵁ U.unop
  change E.app V _ = E.app V _
  congr 1
  let D := affineUniversalDerivation (.of k)
    (.of (ChartCoordinateRing i))
  let g := Spec.map (CommRingCat.ofHom
    (coordinateChartToLeftOverlapRingHom i j))
  change ((Scheme.Modules.restrictFunctorCongr
      (coordinateOverlapToLeft_eq_specMap i j)).hom.app
        (chartCoordinateKaehlerDifferentialSheaf i)).app V
      (((chartCoordinateKaehlerDifferentialSheaf i).val.map
        (homOfLE ((coordinateOverlapToLeft i j).image_preimage_le
          (coordinateChartMap i ⁻¹ᵁ U.unop))).op).hom
        (D.d ((coordinateChartMap i).app U.unop x))) =
    D.d ((g.appIso V).inv ((coordinateOverlapMap i j).app U.unop x))
  have hg : g = coordinateOverlapToLeft i j :=
    (coordinateOverlapToLeft_eq_specMap i j).symm
  have hD := PresheafOfModules.Derivation.d_map D
    (homOfLE ((coordinateOverlapToLeft i j).image_preimage_le
      (coordinateChartMap i ⁻¹ᵁ U.unop))).op
    ((coordinateChartMap i).app U.unop x)
  erw [← hD]
  rw [Scheme.Modules.restrictFunctorCongr_hom_app_app]
  let q : Opposite.op (coordinateOverlapToLeft i j ''ᵁ V) ⟶
      Opposite.op (g ''ᵁ V) :=
    (eqToHom (by simp only [hg])).op
  have hD' := PresheafOfModules.Derivation.d_map D q
    ((coordinateChartScheme i).presheaf.map
      (homOfLE ((coordinateOverlapToLeft i j).image_preimage_le
        (coordinateChartMap i ⁻¹ᵁ U.unop))).op
      ((coordinateChartMap i).app U.unop x))
  erw [← hD']
  congr 1
  let W := coordinateChartMap i ⁻¹ᵁ U.unop
  have he : V ≤ g ⁻¹ᵁ W := by
    dsimp only [V, W]
    rw [hg]
    rfl
  have hx := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_appIso_inv g he)
    ((coordinateChartMap i).app U.unop x)
  calc
    _ = ((coordinateChartScheme i).presheaf.map
        (homOfLE ((g.image_mono he).trans
          (g.image_preimage_eq_opensRange_inf W ▸ inf_le_right))).op)
        ((coordinateChartMap i).app U.unop x) := by
          have hmaps :
              (coordinateChartScheme i).presheaf.map
                  (homOfLE ((coordinateOverlapToLeft i j).image_preimage_le
                    W)).op ≫
                (coordinateChartScheme i).presheaf.map q =
              (coordinateChartScheme i).presheaf.map
                (homOfLE ((g.image_mono he).trans
                  (g.image_preimage_eq_opensRange_inf W ▸
                    inf_le_right))).op := by
            rw [← Functor.map_comp]
            congr 1
          exact ConcreteCategory.congr_hom hmaps
            ((coordinateChartMap i).app U.unop x)
    _ = (g.appLE W V he ≫ (g.appIso V).inv)
        ((coordinateChartMap i).app U.unop x) := hx.symm
    _ = (g.appIso V).inv
        ((coordinateOverlapMap i j).app U.unop x) := by
          rw [ConcreteCategory.comp_apply]
          have hgle :
              g.appLE W V he =
                (coordinateOverlapToLeft i j).appLE W V
                  (by rw [← hg]; exact he) := by
            unfold Scheme.Hom.appLE
            rw [Scheme.Hom.congr_app hg W]
            simp only [Category.assoc, ← Functor.map_comp]
            congr 1
          have happ :
              (coordinateChartMap i).app U.unop ≫ g.appLE W V he =
                (coordinateOverlapMap i j).app U.unop := by
            rw [hgle, Scheme.Hom.app_eq_appLE,
              Scheme.Hom.appLE_comp_appLE]
            rfl
          exact congrArg (fun y ↦ (g.appIso V).inv y)
            (ConcreteCategory.congr_hom happ x)

/-- The normalized top component of the second transported overlap derivation. -/
def coordinateOverlapRightNormalizedTopDerivation (i j : Fin 4) :
    (ModuleCat.of (coordinateOverlapRing i j)
      (KaehlerDifferential k (coordinateOverlapRing i j))).Derivation
        (CommRingCat.ofHom (algebraMap k (coordinateOverlapRing i j))) :=
  normalizedTopDerivation (.of k) (.of (coordinateOverlapRing i j))
    (ModuleCat.of (coordinateOverlapRing i j)
      (KaehlerDifferential k (coordinateOverlapRing i j)))
    (coordinateOverlapRightTransportedDerivation i j)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized second transported derivation agrees with the universal
differential on chart generators. -/
theorem coordinateOverlapRightNormalizedTopDerivation_apply_chart
    (i j : Fin 4) (x : ChartCoordinateRing j) :
    (coordinateOverlapRightNormalizedTopDerivation i j).d
        (coordinateChartToRightOverlapRingHom i j x) =
      KaehlerDifferential.D k (coordinateOverlapRing i j)
        (coordinateChartToRightOverlapRingHom i j x) := by
  let g := CommRingCat.ofHom (coordinateChartToRightOverlapRingHom i j)
  let G := Spec.map g
  change (tilde.isoTop (R := .of (coordinateOverlapRing i j))
      (ModuleCat.of (coordinateOverlapRing i j)
        (KaehlerDifferential k (coordinateOverlapRing i j)))).inv
    ((coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app ⊤
      ((affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing j))).d
        ((G.appIso ⊤).inv
          ((Scheme.ΓSpecIso (.of (coordinateOverlapRing i j))).inv
            (g x))))) = _
  change (tilde.isoTop (R := .of (coordinateOverlapRing i j))
      (ModuleCat.of (coordinateOverlapRing i j)
        (KaehlerDifferential k (coordinateOverlapRing i j)))).inv
    ((coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom.app ⊤
      ((affineUniversalDerivation (.of k)
        (.of (ChartCoordinateRing j))).d
        ((G.appIso ⊤).inv
          ((tilde.toOpen (R := .of (coordinateOverlapRing i j))
            (ModuleCat.of (coordinateOverlapRing i j)
              (coordinateOverlapRing i j)) ⊤) (g x))))) = _
  rw [Scheme.Modules.specMap_appIso_inv_tildeSelf_toOpen_apply]
  have hD := affineUniversalDerivation_toOpen
    (.of k) (.of (ChartCoordinateRing j)) (G ''ᵁ ⊤) x
  change (affineUniversalDerivation (.of k)
      (.of (ChartCoordinateRing j))).d
        ((tilde.toOpen (R := .of (ChartCoordinateRing j))
          (ModuleCat.of (ChartCoordinateRing j) (ChartCoordinateRing j))
          (G ''ᵁ ⊤)) x) =
    (tilde.toOpen (R := .of (ChartCoordinateRing j))
      (ModuleCat.of (ChartCoordinateRing j)
        (KaehlerDifferential k (ChartCoordinateRing j)))
      (G ''ᵁ ⊤))
        (KaehlerDifferential.D k (ChartCoordinateRing j) x) at hD
  erw [hD]
  exact coordinateKaehlerRestrictRightSpecCanonicalIso_normalizedTop_D i j x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Localization extensionality identifies the normalized second transported
derivation with the universal derivation on the overlap ring. -/
theorem coordinateOverlapRightNormalizedTopDerivation_eq (i j : Fin 4) :
    coordinateOverlapRightNormalizedTopDerivation i j =
      KaehlerDifferential.D k (coordinateOverlapRing i j) := by
  let S := ChartCoordinateRing j
  let T := coordinateOverlapRing i j
  let r := Away.isLocalizationElem (coordinateClass_mem_degreeOne j)
    (coordinateClass_mem_degreeOne i)
  letI : Algebra S T := (coordinateChartToRightOverlapRingHom i j).toAlgebra
  letI : SMul S T :=
    ((coordinateChartToRightOverlapRingHom i j).toAlgebra).toSMul
  letI : IsLocalization.Away r T :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne i) (mul_comm _ _) (by norm_num)
  letI : IsScalarTower k S T :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  apply AlgebraicGeometry.Derivation.ext_of_isLocalization
    (k := k) (R := S) (T := T)
      (N := KaehlerDifferential k T) (.powers r)
  intro x
  change (coordinateOverlapRightNormalizedTopDerivation i j).d
      (coordinateChartToRightOverlapRingHom i j x) = _
  exact coordinateOverlapRightNormalizedTopDerivation_apply_chart i j x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Transport through the second chart restriction recovers the affine
universal derivation on the entire ordered overlap. -/
theorem coordinateOverlapRightTransportedDerivation_eq (i j : Fin 4) :
    coordinateOverlapRightTransportedDerivation i j =
      affineUniversalDerivation (.of k) (.of (coordinateOverlapRing i j)) := by
  apply PresheafOfModules.Derivation'.ext_of_affine_top
  intro x
  let T := coordinateOverlapRing i j
  let e := tilde.isoTop
    (R := .of T) (ModuleCat.of T (KaehlerDifferential k T))
  let t : T := (Scheme.ΓSpecIso (.of T)).hom x
  have h := congrArg (fun D => D.d t)
    (coordinateOverlapRightNormalizedTopDerivation_eq i j)
  have ha := affineUniversalDerivation_normalizedTop
    (.of k) (.of T) t
  change e.inv
      ((coordinateOverlapRightTransportedDerivation i j).d
        ((Scheme.ΓSpecIso (.of T)).inv t)) =
    KaehlerDifferential.D k T t at h
  change e.inv
      ((affineUniversalDerivation (.of k) (.of T)).d
        ((Scheme.ΓSpecIso (.of T)).inv t)) =
    KaehlerDifferential.D k T t at ha
  have ht : (Scheme.ΓSpecIso (.of T)).inv t = x := by
    dsimp only [t]
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of T)) x
  rw [ht] at h ha
  have hn : e.inv
      ((coordinateOverlapRightTransportedDerivation i j).d x) =
    e.inv ((affineUniversalDerivation (.of k) (.of T)).d x) := by
    exact h.trans ha.symm
  have := congrArg (fun z => e.hom z) hn
  simpa only [Iso.inv_hom_id_apply] using this

set_option maxHeartbeats 0 in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the second chart derivation through the named composite
overlap map recovers the overlap's universal derivation. -/
theorem coordinateChartDerivation_postcomp_right (i j : Fin 4) :
    (coordinateChartDerivation j).postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (pushforwardRestrictionHom
              (coordinateOverlapToRight i j)
              (coordinateChartMap j)
              (coordinateOverlapMap i j)
              (coordinateOverlapMap_eq_right i j)
              (chartCoordinateKaehlerDifferentialSheaf j)
              (coordinateOverlapKaehlerDifferentialSheaf i j)
              (coordinateKaehlerRestrictRightIso i j))) =
      coordinateOverlapDerivation i j := by
  apply PresheafOfModules.Derivation.ext
  funext U
  apply AddMonoidHom.ext
  intro x
  rw [PresheafOfModules.Derivation.postcomp_d_apply]
  change (pushforwardRestrictionHom
        (coordinateOverlapToRight i j)
        (coordinateChartMap j)
        (coordinateOverlapMap i j)
        (coordinateOverlapMap_eq_right i j)
        (chartCoordinateKaehlerDifferentialSheaf j)
        (coordinateOverlapKaehlerDifferentialSheaf i j)
        (coordinateKaehlerRestrictRightIso i j)).app U.unop
      ((coordinateChartDerivation j).d x) =
    (coordinateOverlapDerivation i j).d x
  unfold pushforwardRestrictionHom
  rw [Scheme.Modules.pushforwardRestrictionHomOfHom_app]
  simp only [coordinateChartDerivation, coordinateOverlapDerivation]
  dsimp only [ModuleCat.Derivation.precomp, ModuleCat.Derivation.d,
    ModuleCat.Derivation.mk]
  have ht := congrArg
    (fun D ↦ D.d ((coordinateOverlapMap i j).app U.unop x))
    (coordinateOverlapRightTransportedDerivation_eq i j)
  change _ = _ at ht
  change _ = (affineUniversalDerivation (.of k)
    (.of (coordinateOverlapRing i j))).d
      ((coordinateOverlapMap i j).app U.unop x)
  rw [← ht]
  unfold coordinateKaehlerRestrictRightIso
  unfold coordinateKaehlerRestrictRightCanonicalIso
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply]
  simp only [coordinateOverlapRightTransportedDerivation]
  dsimp only [ModuleCat.Derivation.d, ModuleCat.Derivation.mk]
  let V₀ := coordinateOverlapToRight i j ⁻¹ᵁ
    coordinateChartMap j ⁻¹ᵁ U.unop
  let V := coordinateOverlapMap i j ⁻¹ᵁ U.unop
  let g := Spec.map (CommRingCat.ofHom
    (coordinateChartToRightOverlapRingHom i j))
  let D := affineUniversalDerivation (.of k)
    (.of (ChartCoordinateRing j))
  let E := (coordinateKaehlerRestrictRightSpecCanonicalIso i j).hom
  have hV : V = V₀ := by
    dsimp only [V₀, V]
    rw [← coordinateOverlapMap_eq_right i j]
    rfl
  let q : Opposite.op V₀ ⟶ Opposite.op V :=
    (eqToHom hV).op
  change ((coordinateOverlapKaehlerDifferentialSheaf i j).val.map q).hom
      (E.app V₀
        (((Scheme.Modules.restrictFunctorCongr
          (coordinateOverlapToRight_eq_specMap i j)).hom.app
            (chartCoordinateKaehlerDifferentialSheaf j)).app V₀
          (((chartCoordinateKaehlerDifferentialSheaf j).val.map
            (homOfLE ((coordinateOverlapToRight i j).image_preimage_le
              (coordinateChartMap j ⁻¹ᵁ U.unop))).op).hom
            (D.d ((coordinateChartMap j).app U.unop x))))) =
    E.app V (D.d ((g.appIso V).inv
      ((coordinateOverlapMap i j).app U.unop x)))
  let z :=
    ((Scheme.Modules.restrictFunctorCongr
      (coordinateOverlapToRight_eq_specMap i j)).hom.app
        (chartCoordinateKaehlerDifferentialSheaf j)).app V₀
      (((chartCoordinateKaehlerDifferentialSheaf j).val.map
        (homOfLE ((coordinateOverlapToRight i j).image_preimage_le
          (coordinateChartMap j ⁻¹ᵁ U.unop))).op).hom
        (D.d ((coordinateChartMap j).app U.unop x)))
  have hE := PresheafOfModules.naturality_apply E.val q z
  calc
    _ = E.app V
        ((((Scheme.Modules.restrictFunctor g).obj
          (chartCoordinateKaehlerDifferentialSheaf j)).val.map q).hom z) :=
      hE.symm
    _ = E.app V (D.d ((g.appIso V).inv
        ((coordinateOverlapMap i j).app U.unop x))) := by
      congr 1
      dsimp only [z]
      rw [Scheme.Modules.restrictFunctorCongr_hom_app_app]
      let W := coordinateChartMap j ⁻¹ᵁ U.unop
      have hg : g = coordinateOverlapToRight i j :=
        (coordinateOverlapToRight_eq_specMap i j).symm
      have he : V ≤ g ⁻¹ᵁ W := by
        dsimp only [V, W]
        rw [hg]
        exact le_of_eq hV
      let a : Opposite.op W ⟶
          Opposite.op (coordinateOverlapToRight i j ''ᵁ V₀) :=
        (homOfLE ((coordinateOverlapToRight i j).image_preimage_le W)).op
      let b : Opposite.op (coordinateOverlapToRight i j ''ᵁ V₀) ⟶
          Opposite.op (g ''ᵁ V₀) :=
        (eqToHom (by simp only [hg])).op
      let c : Opposite.op (g ''ᵁ V₀) ⟶ Opposite.op (g ''ᵁ V) :=
        g.opensFunctor.op.map q
      let m : Opposite.op W ⟶ Opposite.op (g ''ᵁ V) :=
        (homOfLE ((g.image_mono he).trans
          (g.image_preimage_eq_opensRange_inf W ▸ inf_le_right))).op
      let y := (coordinateChartMap j).app U.unop x
      have hDa := PresheafOfModules.Derivation.d_map D a y
      erw [← hDa]
      have hDb := PresheafOfModules.Derivation.d_map D b
        ((coordinateChartScheme j).presheaf.map a y)
      erw [← hDb]
      have hDc := PresheafOfModules.Derivation.d_map D c
        ((coordinateChartScheme j).presheaf.map b
          ((coordinateChartScheme j).presheaf.map a y))
      erw [← hDc]
      congr 1
      have hx := ConcreteCategory.congr_hom
        (Scheme.Hom.appLE_appIso_inv g he) y
      calc
        _ = (coordinateChartScheme j).presheaf.map m y := by
          have hmaps :
              (coordinateChartScheme j).presheaf.map a ≫
                    (coordinateChartScheme j).presheaf.map b ≫
                  (coordinateChartScheme j).presheaf.map c =
                (coordinateChartScheme j).presheaf.map m := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            congr 1
          exact ConcreteCategory.congr_hom hmaps y
        _ = (g.appLE W V he ≫ (g.appIso V).inv) y := hx.symm
        _ = (g.appIso V).inv
            ((coordinateOverlapMap i j).app U.unop x) := by
          rw [ConcreteCategory.comp_apply]
          have hgle :
              g.appLE W V he =
                (coordinateOverlapToRight i j).appLE W V
                  (by rw [← hg]; exact he) := by
            unfold Scheme.Hom.appLE
            rw [Scheme.Hom.congr_app hg W]
            simp only [Category.assoc, ← Functor.map_comp]
            congr 1
          have happ :
              (coordinateChartMap j).app U.unop ≫ g.appLE W V he =
                (coordinateOverlapMap i j).app U.unop := by
            rw [hgle, Scheme.Hom.app_eq_appLE,
              Scheme.Hom.appLE_comp_appLE]
            unfold Scheme.Hom.appLE
            rw [Scheme.Hom.congr_app
              (coordinateOverlapMap_eq_right i j) U.unop]
            simp only [Category.assoc, ← Functor.map_comp]
            conv_rhs => rw [← Category.comp_id
              ((coordinateOverlapMap i j).app U.unop)]
            congr 1
          exact congrArg (fun t ↦ (g.appIso V).inv t)
            (ConcreteCategory.congr_hom happ x)

noncomputable local instance : PreservesLimit
    (Discrete.functor
      (fun p : Fin 4 × Fin 4 ↦ coordinateKaehlerOverlapPushforward p))
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf) :=
  (SheafOfModules.forgetPreservesLimitsOfShape
    (Discrete (Fin 4 × Fin 4))
    CanonicalProjectiveCurve25Two.ringCatSheaf).preservesLimit

/-- Forgetting the overlap product gives the product of the forgotten
ordered-overlap modules. -/
def canonicalKaehlerOverlapPiComparisonIso :
    canonicalModulePresheaf kaehlerCechTarget ≅
      ∏ᶜ fun p : Fin 4 × Fin 4 ↦ canonicalModulePresheaf
        (coordinateKaehlerOverlapPushforward p) :=
  PreservesProduct.iso
    (SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf)
    (fun p : Fin 4 × Fin 4 ↦ coordinateKaehlerOverlapPushforward p)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The four chart universal derivations agree on every ordered overlap. -/
theorem coordinateChartDerivations_compatible :
    (kaehlerCechSourceDerivation coordinateChartDerivation).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft) =
      (kaehlerCechSourceDerivation coordinateChartDerivation).postcomp
          ((SheafOfModules.forget.{0}
            CanonicalProjectiveCurve25Two.ringCatSheaf).map
              kaehlerCechRight) := by
  let dL := (kaehlerCechSourceDerivation coordinateChartDerivation).postcomp
    ((SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechLeft)
  let dR := (kaehlerCechSourceDerivation coordinateChartDerivation).postcomp
    ((SheafOfModules.forget.{0}
      CanonicalProjectiveCurve25Two.ringCatSheaf).map kaehlerCechRight)
  let e := canonicalKaehlerOverlapPiComparisonIso
  have h : dL.postcomp e.hom = dR.postcomp e.hom := by
    apply PresheafOfModules.Derivation'.pi_ext
    intro p
    dsimp only [dL, dR]
    repeat rw [PresheafOfModules.Derivation'.postcomp_comp]
    dsimp only [e, canonicalKaehlerOverlapPiComparisonIso]
    simp only [PreservesProduct.iso_hom, piComparison_comp_π]
    rw [← Functor.map_comp, ← Functor.map_comp]
    dsimp only [kaehlerCechLeft, kaehlerCechRight]
    rw [Pi.lift_π, Pi.lift_π]
    rw [Functor.map_comp, Functor.map_comp]
    rw [← PresheafOfModules.Derivation'.postcomp_comp,
      ← PresheafOfModules.Derivation'.postcomp_comp]
    rw [kaehlerCechSourceDerivation_postcomp_π,
      kaehlerCechSourceDerivation_postcomp_π]
    rw [coordinateChartDerivation_postcomp_left,
      coordinateChartDerivation_postcomp_right]
  have h' := congrArg (fun d ↦ d.postcomp e.inv) h
  simpa only [PresheafOfModules.Derivation'.postcomp_comp,
    Iso.hom_inv_id, Category.comp_id,
    PresheafOfModules.Derivation'.postcomp_id] using h'

/-- The descended universal derivation with values in the actual global
Kähler differential module. -/
def canonicalGlobalKaehlerDifferentialDerivation :
    (canonicalModulePresheaf globalKaehlerDifferentialModule).Derivation'
      canonicalCurveConstBaseMap :=
  globalKaehlerDifferentialDerivation coordinateChartDerivation
    coordinateChartDerivations_compatible

set_option backward.isDefEq.respectTransparency false in
/-- The descended derivation restricts to the universal derivation on each
standard affine chart. -/
@[simp]
theorem canonicalGlobalKaehlerDifferentialDerivation_postcomp_chart
    (i : Fin 4) :
    canonicalGlobalKaehlerDifferentialDerivation.postcomp
        ((SheafOfModules.forget.{0}
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
              Pi.π (fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i)
                i)) =
      coordinateChartDerivation i := by
  rw [Functor.map_comp]
  change (canonicalGlobalKaehlerDifferentialDerivation.postcomp
      ((SheafOfModules.forget.{0}
        CanonicalProjectiveCurve25Two.ringCatSheaf).map
          (equalizer.ι kaehlerCechLeft kaehlerCechRight))).postcomp
      ((SheafOfModules.forget.{0}
        CanonicalProjectiveCurve25Two.ringCatSheaf).map
          (Pi.π (fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i)
            i)) = coordinateChartDerivation i
  unfold canonicalGlobalKaehlerDifferentialDerivation
  rw [globalKaehlerDifferentialDerivation_postcomp_ι,
    kaehlerCechSourceDerivation_postcomp_π]

/-- The universal property of relative differentials gives the canonical
map to the Čech-descended Kähler differential sheaf. -/
def canonicalRelativeDifferentialsToGlobalKaehler :
    canonicalRelativeDifferentialsSheaf ⟶ globalKaehlerDifferentialModule :=
  canonicalRelativeDifferentialsSheafHomOfDerivation
    globalKaehlerDifferentialModule
    canonicalGlobalKaehlerDifferentialDerivation

/-- The universal chart derivation transposes to a morphism from the
relative differential sheaf to the corresponding extended chart module. -/
def canonicalRelativeDifferentialsToChart (i : Fin 4) :
    canonicalRelativeDifferentialsSheaf ⟶
      coordinateKaehlerLocalPushforward i :=
  canonicalRelativeDifferentialsSheafHomOfDerivation
    (coordinateKaehlerLocalPushforward i) (coordinateChartDerivation i)

/-- The presheaf adjunct of the chart comparison is the universal morphism
represented by the extended affine derivation. -/
theorem canonicalRelativeDifferentialsToChart_adjunct (i : Fin 4) :
    PresheafOfModules.sheafificationHomEquiv
        (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)
        (canonicalRelativeDifferentialsToChart i) =
      (isUniversal' canonicalCurveConstBaseMap).desc
        (coordinateChartDerivation i) := by
  let e := PresheafOfModules.DifferentialsConstruction.homEquiv
    canonicalCurveConstBaseMap
      (canonicalModulePresheaf (coordinateKaehlerLocalPushforward i))
  change PresheafOfModules.sheafificationHomEquiv
      (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)
        (canonicalRelativeDifferentialsToChart i) =
    e.symm (coordinateChartDerivation i)
  apply e.injective
  rw [e.apply_symm_apply]
  change canonicalRelativeDifferentialsSheafHomEquivDerivation
    (coordinateKaehlerLocalPushforward i)
      (canonicalRelativeDifferentialsToChart i) = coordinateChartDerivation i
  unfold canonicalRelativeDifferentialsToChart
  exact canonicalRelativeDifferentialsSheafHomEquivDerivation_homOfDerivation
    (coordinateKaehlerLocalPushforward i) (coordinateChartDerivation i)

/-- The chart comparison sends the sheafification unit to the objectwise
universal morphism represented by the chart derivation. -/
theorem canonicalRelativeDifferentialsToSheaf_comp_chart (i : Fin 4) :
    canonicalRelativeDifferentialsToSheaf ≫
        (SheafOfModules.forget
          CanonicalProjectiveCurve25Two.ringCatSheaf).map
            (canonicalRelativeDifferentialsToChart i) =
      (isUniversal' canonicalCurveConstBaseMap).desc
        (coordinateChartDerivation i) := by
  change PresheafOfModules.sheafificationHomEquiv
      (𝟙 CanonicalProjectiveCurve25Two.ringCatSheaf.obj)
        (canonicalRelativeDifferentialsToChart i) = _
  exact canonicalRelativeDifferentialsToChart_adjunct i

set_option backward.isDefEq.respectTransparency false in
/-- The global comparison followed by a Čech chart projection is the
universal chart comparison. -/
@[simp]
theorem canonicalRelativeDifferentialsToGlobalKaehler_comp_chart
    (i : Fin 4) :
    canonicalRelativeDifferentialsToGlobalKaehler ≫
        (equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
          Pi.π (fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i) i) =
      canonicalRelativeDifferentialsToChart i := by
  apply (canonicalRelativeDifferentialsSheafHomEquivDerivation
    (coordinateKaehlerLocalPushforward i)).injective
  rw [canonicalRelativeDifferentialsSheafHomEquivDerivation_comp]
  unfold canonicalRelativeDifferentialsToGlobalKaehler
  rw [canonicalRelativeDifferentialsSheafHomEquivDerivation_homOfDerivation]
  unfold canonicalRelativeDifferentialsToChart
  rw [canonicalRelativeDifferentialsSheafHomEquivDerivation_homOfDerivation]
  exact canonicalGlobalKaehlerDifferentialDerivation_postcomp_chart i

/-! ## Reduction of global invertibility to the affine charts -/

/-- The chart-local adjoint of the universal comparison to the pushed-forward
affine Kähler sheaf.  This is the precise local morphism whose invertibility
identifies sheafified relative differentials with affine tilde. -/
def canonicalRelativeDifferentialsToLocalChart (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        canonicalRelativeDifferentialsSheaf ⟶
      chartCoordinateKaehlerDifferentialSheaf i :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
      (canonicalRelativeDifferentialsToChart i) ≫
    (Scheme.Modules.restrictAdjunction
      (coordinateChartMap i)).counit.app
        (chartCoordinateKaehlerDifferentialSheaf i)

set_option backward.isDefEq.respectTransparency false in
/-- After the local effectiveness isomorphism, the global comparison is
exactly the chart-local affine comparison. -/
theorem canonicalRelativeDifferentialsToGlobalKaehler_restrict
    (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
        canonicalRelativeDifferentialsToGlobalKaehler ≫
      (globalKaehlerDifferentialLocalIso i).hom =
        canonicalRelativeDifferentialsToLocalChart i := by
  rw [← globalKaehlerDifferentialToLocal_eq]
  unfold globalKaehlerDifferentialToLocal
  unfold canonicalRelativeDifferentialsToLocalChart
  rw [← Category.assoc, ← Functor.map_comp]
  rw [canonicalRelativeDifferentialsToGlobalKaehler_comp_chart]

/-- Since literal Čech evaluation is an isomorphism, invertibility of the
restricted global comparison is equivalent to invertibility of the single
affine chart comparison. -/
theorem canonicalRelativeDifferentialsToGlobalKaehler_restrict_isIso_iff
    (i : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
        canonicalRelativeDifferentialsToGlobalKaehler) ↔
      IsIso (canonicalRelativeDifferentialsToLocalChart i) := by
  rw [← canonicalRelativeDifferentialsToGlobalKaehler_restrict]
  exact (isIso_comp_right_iff
    ((Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
      canonicalRelativeDifferentialsToGlobalKaehler)
    (globalKaehlerDifferentialLocalIso i).hom).symm

end MazurProof.RationalPointsN25QuotientTwoRelativeDifferentials
