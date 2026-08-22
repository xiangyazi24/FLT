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
