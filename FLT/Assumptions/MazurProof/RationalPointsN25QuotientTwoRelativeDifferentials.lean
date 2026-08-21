import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCech
import FLT.Mathlib.AlgebraicGeometry.Modules.RelativeDifferentials
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

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
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingSheafCharts
open AlgebraicGeometry
open CategoryTheory
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
