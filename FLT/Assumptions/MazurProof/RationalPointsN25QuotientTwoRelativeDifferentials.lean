import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCech
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
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
open RationalPointsN25QuotientTwoCanonicalDifferentialRestriction
open RationalPointsN25QuotientTwoCanonicalDifferentialCech
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingSheafCharts
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction

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

end MazurProof.RationalPointsN25QuotientTwoRelativeDifferentials
