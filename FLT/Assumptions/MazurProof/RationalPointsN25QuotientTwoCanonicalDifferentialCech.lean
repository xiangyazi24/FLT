import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialRestriction
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAdjunctionDescent
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingSheafGluing

/-!
# Čech descent of the N25 canonical differentials

The affine tilde sheaves of actual Kähler differentials restrict to the same
actual overlap differential sheaf.  Their residue frames compare these
intrinsic restriction maps with the already constructed exponent `-1` twist
diagram.  This file assembles the two parallel Čech arrows and identifies
them componentwise with the effective `O(1)` arrows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCech

open RationalPointsN25QuotientTwoCanonicalDifferentialTilde
open RationalPointsN25QuotientTwoCanonicalDifferentialRestriction
open RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps
open RationalPointsN25QuotientTwoAdjunctionDescent
open RationalPointsN25QuotientTwoAmbientKoszulPullback
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingSheafGluing
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

/-! ## Canonical restriction isomorphisms -/

/-- Restriction from the first chart to an ordered overlap, reconstructed
through the first residue frame. -/
def coordinateKaehlerRestrictLeftResidueFrameIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf i) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).mapIso
      (chartCoordinateKaehlerDifferentialTildeIso i) ≪≫
    coordinateRestrictLeftIso (-1) i j ≪≫
    (coordinateOverlapLeftKaehlerDifferentialTildeIso i j).symm

/-- Restriction from the second chart to the same ordered overlap,
reconstructed through the second residue frame. -/
def coordinateKaehlerRestrictRightResidueFrameIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf j) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).mapIso
      (chartCoordinateKaehlerDifferentialTildeIso j) ≪≫
    coordinateRestrictRightIso (-1) i j ≪≫
    (coordinateOverlapRightKaehlerDifferentialTildeIso i j).symm

/-- Canonical restriction from the first chart to an ordered overlap. -/
def coordinateKaehlerRestrictLeftIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf i) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  coordinateKaehlerRestrictLeftCanonicalIso i j

/-- Canonical restriction from the second chart to an ordered overlap. -/
def coordinateKaehlerRestrictRightIso (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).obj
        (chartCoordinateKaehlerDifferentialSheaf j) ≅
      coordinateOverlapKaehlerDifferentialSheaf i j :=
  coordinateKaehlerRestrictRightCanonicalIso i j

/-- At exponent `-1`, the first local twist restriction is the canonical
restriction of the unit module. -/
theorem coordinateRestrictLeftIso_negOne_eq_restrictUnitIso (i j : Fin 4) :
    coordinateRestrictLeftIso (-1) i j =
      Scheme.Modules.restrictUnitIso (coordinateOverlapToLeft i j) := by
  rfl

/-- At exponent `-1`, the second local twist restriction is the canonical
restriction of the unit module. -/
theorem coordinateRestrictRightIso_negOne_eq_restrictUnitIso (i j : Fin 4) :
    coordinateRestrictRightIso (-1) i j =
      Scheme.Modules.restrictUnitIso (coordinateOverlapToRight i j) := by
  rfl

/-- The canonical first restriction agrees with its residue-frame
presentation. -/
theorem coordinateKaehlerRestrictLeftIso_eq_residueFrameIso (i j : Fin 4) :
    coordinateKaehlerRestrictLeftIso i j =
      coordinateKaehlerRestrictLeftResidueFrameIso i j := by
  rw [coordinateKaehlerRestrictLeftIso,
    coordinateKaehlerRestrictLeftCanonicalIso,
    coordinateKaehlerRestrictLeftSpecCanonicalIso_eq_residueFrameIso]
  unfold coordinateKaehlerRestrictLeftSpecResidueFrameIso
  rw [coordinateKaehlerRestrictLeftResidueFrameIso,
    coordinateRestrictLeftIso_negOne_eq_restrictUnitIso]
  have h := Scheme.Modules.restrictFrameIso_congr
    (f := coordinateOverlapToLeft i j)
    (g := Spec.map (CommRingCat.ofHom
      (coordinateChartToLeftOverlapRingHom i j)))
    (coordinateOverlapToLeft_eq_specMap i j)
    (chartCoordinateKaehlerDifferentialSheaf i)
    (chartCoordinateKaehlerDifferentialTildeIso i)
  convert congrArg
    (fun z => z ≪≫
      (coordinateOverlapLeftKaehlerDifferentialTildeIso i j).symm) h using 1
  all_goals
    simp only [← Iso.trans_assoc]
    apply Iso.ext
    rfl

/-- The canonical second restriction agrees with its residue-frame
presentation. -/
theorem coordinateKaehlerRestrictRightIso_eq_residueFrameIso (i j : Fin 4) :
    coordinateKaehlerRestrictRightIso i j =
      coordinateKaehlerRestrictRightResidueFrameIso i j := by
  rw [coordinateKaehlerRestrictRightIso,
    coordinateKaehlerRestrictRightCanonicalIso,
    coordinateKaehlerRestrictRightSpecCanonicalIso_eq_residueFrameIso]
  unfold coordinateKaehlerRestrictRightSpecResidueFrameIso
  rw [coordinateKaehlerRestrictRightResidueFrameIso,
    coordinateRestrictRightIso_negOne_eq_restrictUnitIso]
  have h := Scheme.Modules.restrictFrameIso_congr
    (f := coordinateOverlapToRight i j)
    (g := Spec.map (CommRingCat.ofHom
      (coordinateChartToRightOverlapRingHom i j)))
    (coordinateOverlapToRight_eq_specMap i j)
    (chartCoordinateKaehlerDifferentialSheaf j)
    (chartCoordinateKaehlerDifferentialTildeIso j)
  convert congrArg
    (fun z => z ≪≫
      (coordinateOverlapRightKaehlerDifferentialTildeIso i j).symm) h using 1
  all_goals
    simp only [← Iso.trans_assoc]
    apply Iso.ext
    rfl

/-- In the right overlap frame, the intrinsic left restriction acquires the
exponent `-1` transition. -/
theorem coordinateKaehlerRestrictLeftIso_frame (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).map
          (chartCoordinateKaehlerDifferentialTildeIso i).hom ≫
        (coordinateRestrictLeftIso (-1) i j ≪≫
          coordinateOverlapTwistIso (-1) i j).hom =
      (coordinateKaehlerRestrictLeftIso i j).hom ≫
        (coordinateOverlapRightKaehlerDifferentialTildeIso i j).hom := by
  rw [coordinateKaehlerRestrictLeftIso_eq_residueFrameIso]
  rw [coordinateOverlapRightKaehlerDifferentialTildeIso_eq]
  simp [coordinateKaehlerRestrictLeftResidueFrameIso, Category.assoc]

/-- The intrinsic right restriction is already expressed in the chosen right
overlap frame. -/
theorem coordinateKaehlerRestrictRightIso_frame (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).map
          (chartCoordinateKaehlerDifferentialTildeIso j).hom ≫
        (coordinateRestrictRightIso (-1) i j).hom =
      (coordinateKaehlerRestrictRightIso i j).hom ≫
        (coordinateOverlapRightKaehlerDifferentialTildeIso i j).hom := by
  rw [coordinateKaehlerRestrictRightIso_eq_residueFrameIso]
  simp [coordinateKaehlerRestrictRightResidueFrameIso, Category.assoc]

/-! ## Actual Kähler Čech diagram -/

/-- A chart differential sheaf extended to the canonical projective curve. -/
abbrev coordinateKaehlerLocalPushforward (i : Fin 4) :
    CanonicalProjectiveCurve25Two.Modules :=
  (Scheme.Modules.pushforward (coordinateChartMap i)).obj
    (chartCoordinateKaehlerDifferentialSheaf i)

/-- An ordered-overlap differential sheaf extended to the projective curve. -/
abbrev coordinateKaehlerOverlapPushforward (p : Fin 4 × Fin 4) :
    CanonicalProjectiveCurve25Two.Modules :=
  (Scheme.Modules.pushforward (coordinateOverlapMap p.1 p.2)).obj
    (coordinateOverlapKaehlerDifferentialSheaf p.1 p.2)

/-- Product of the four actual chart differential sheaves. -/
abbrev kaehlerCechSource : CanonicalProjectiveCurve25Two.Modules :=
  ∏ᶜ fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i

/-- Product of the sixteen actual ordered-overlap differential sheaves. -/
abbrev kaehlerCechTarget : CanonicalProjectiveCurve25Two.Modules :=
  ∏ᶜ fun p : Fin 4 × Fin 4 ↦ coordinateKaehlerOverlapPushforward p

/-- Restrict each first-chart differential to its ordered overlap. -/
def kaehlerCechLeft : kaehlerCechSource ⟶ kaehlerCechTarget :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i) p.1 ≫
      pushforwardRestrictionHom
        (coordinateOverlapToLeft p.1 p.2)
        (coordinateChartMap p.1)
        (coordinateOverlapMap p.1 p.2)
        rfl
        (chartCoordinateKaehlerDifferentialSheaf p.1)
        (coordinateOverlapKaehlerDifferentialSheaf p.1 p.2)
        (coordinateKaehlerRestrictLeftIso p.1 p.2)

/-- Restrict each second-chart differential to the same ordered overlap. -/
def kaehlerCechRight : kaehlerCechSource ⟶ kaehlerCechTarget :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ coordinateKaehlerLocalPushforward i) p.2 ≫
      pushforwardRestrictionHom
        (coordinateOverlapToRight p.1 p.2)
        (coordinateChartMap p.2)
        (coordinateOverlapMap p.1 p.2)
        (coordinateOverlapMap_eq_right p.1 p.2)
        (chartCoordinateKaehlerDifferentialSheaf p.2)
        (coordinateOverlapKaehlerDifferentialSheaf p.1 p.2)
        (coordinateKaehlerRestrictRightIso p.1 p.2)

/-! ## Comparison with the effective positive twist -/

/-- The product of chart residue frames compares the actual Kähler source
with the exponent `-1` twist source. -/
def kaehlerCechSourceIsoTwist : kaehlerCechSource ≅ twistCechSource (-1) :=
  Pi.mapIso fun i ↦
    (Scheme.Modules.pushforward (coordinateChartMap i)).mapIso
      (chartCoordinateKaehlerDifferentialTildeIso i)

/-- The product of right residue frames compares the actual overlap target
with the exponent `-1` twist target. -/
def kaehlerCechTargetIsoTwist : kaehlerCechTarget ≅ twistCechTarget (-1) :=
  Pi.mapIso fun p ↦
    (Scheme.Modules.pushforward (coordinateOverlapMap p.1 p.2)).mapIso
      (coordinateOverlapRightKaehlerDifferentialTildeIso p.1 p.2)

/-- The chart and overlap residue frames intertwine the first Čech arrows. -/
theorem kaehlerCechSourceIsoTwist_hom_comp_left :
    kaehlerCechSourceIsoTwist.hom ≫ twistCechLeft (-1) =
      kaehlerCechLeft ≫ kaehlerCechTargetIsoTwist.hom := by
  apply Pi.hom_ext
  intro p
  dsimp only [kaehlerCechSourceIsoTwist, kaehlerCechTargetIsoTwist,
    twistCechLeft, kaehlerCechLeft]
  rw [Category.assoc, Pi.lift_π]
  rw [Pi.mapIso_hom_π_assoc]
  rw [Category.assoc, Pi.mapIso_hom_π]
  rw [Pi.lift_π_assoc]
  simpa only [pushforwardRestrictionHom, Functor.mapIso_hom,
    Category.assoc] using congrArg
      (fun z => Pi.π (fun i : Fin 4 ↦
        coordinateKaehlerLocalPushforward i) p.1 ≫ z)
      (Scheme.Modules.pushforwardRestrictionHomOfHom_naturality
        (f := coordinateChartMap p.1)
        (k := coordinateOverlapToLeft p.1 p.2)
        (h := coordinateOverlapMap p.1 p.2) rfl
        (coordinateKaehlerRestrictLeftIso p.1 p.2).hom
        (coordinateRestrictLeftIso (-1) p.1 p.2 ≪≫
          coordinateOverlapTwistIso (-1) p.1 p.2).hom
        (chartCoordinateKaehlerDifferentialTildeIso p.1).hom
        (coordinateOverlapRightKaehlerDifferentialTildeIso p.1 p.2).hom
        (coordinateKaehlerRestrictLeftIso_frame p.1 p.2))

/-- The chart and overlap residue frames intertwine the second Čech arrows. -/
theorem kaehlerCechSourceIsoTwist_hom_comp_right :
    kaehlerCechSourceIsoTwist.hom ≫ twistCechRight (-1) =
      kaehlerCechRight ≫ kaehlerCechTargetIsoTwist.hom := by
  apply Pi.hom_ext
  intro p
  dsimp only [kaehlerCechSourceIsoTwist, kaehlerCechTargetIsoTwist,
    twistCechRight, kaehlerCechRight]
  rw [Category.assoc, Pi.lift_π]
  rw [Pi.mapIso_hom_π_assoc]
  rw [Category.assoc, Pi.mapIso_hom_π]
  rw [Pi.lift_π_assoc]
  simpa only [pushforwardRestrictionHom, Functor.mapIso_hom,
    Category.assoc] using congrArg
      (fun z => Pi.π (fun i : Fin 4 ↦
        coordinateKaehlerLocalPushforward i) p.2 ≫ z)
      (Scheme.Modules.pushforwardRestrictionHomOfHom_naturality
        (f := coordinateChartMap p.2)
        (k := coordinateOverlapToRight p.1 p.2)
        (h := coordinateOverlapMap p.1 p.2)
        (coordinateOverlapMap_eq_right p.1 p.2)
        (coordinateKaehlerRestrictRightIso p.1 p.2).hom
        (coordinateRestrictRightIso (-1) p.1 p.2).hom
        (chartCoordinateKaehlerDifferentialTildeIso p.2).hom
        (coordinateOverlapRightKaehlerDifferentialTildeIso p.1 p.2).hom
        (coordinateKaehlerRestrictRightIso_frame p.1 p.2))

/-! ## The global descended differential module -/

set_option backward.isDefEq.respectTransparency false

/-- The global module sheaf obtained by enforcing compatibility of the actual
affine Kähler differential sheaves. -/
def globalKaehlerDifferentialModule :
    CanonicalProjectiveCurve25Two.Modules :=
  equalizer kaehlerCechLeft kaehlerCechRight

/-- The inverse source comparison converts the twist left arrow back to the
actual Kähler left arrow. -/
theorem kaehlerCechSourceIsoTwist_inv_comp_left :
    kaehlerCechSourceIsoTwist.inv ≫ kaehlerCechLeft =
      twistCechLeft (-1) ≫ kaehlerCechTargetIsoTwist.inv := by
  rw [← cancel_mono kaehlerCechTargetIsoTwist.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← kaehlerCechSourceIsoTwist_hom_comp_left]
  simp

/-- The inverse source comparison converts the twist right arrow back to the
actual Kähler right arrow. -/
theorem kaehlerCechSourceIsoTwist_inv_comp_right :
    kaehlerCechSourceIsoTwist.inv ≫ kaehlerCechRight =
      twistCechRight (-1) ≫ kaehlerCechTargetIsoTwist.inv := by
  rw [← cancel_mono kaehlerCechTargetIsoTwist.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← kaehlerCechSourceIsoTwist_hom_comp_right]
  simp

/-- A compatible actual Kähler family maps to the corresponding compatible
exponent `-1` twist family. -/
def globalKaehlerDifferentialToTwist :
    globalKaehlerDifferentialModule ⟶ globalTwistModule (-1) :=
  equalizer.lift
    (equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
      kaehlerCechSourceIsoTwist.hom)
    (by
      simp only [Category.assoc]
      rw [kaehlerCechSourceIsoTwist_hom_comp_left,
        kaehlerCechSourceIsoTwist_hom_comp_right]
      simp only [← Category.assoc]
      exact congrArg (fun z => z ≫ kaehlerCechTargetIsoTwist.hom)
        (equalizer.condition kaehlerCechLeft kaehlerCechRight))

/-- A compatible exponent `-1` twist family maps back to the corresponding
actual Kähler family. -/
def globalTwistToKaehlerDifferential :
    globalTwistModule (-1) ⟶ globalKaehlerDifferentialModule :=
  equalizer.lift
    (equalizer.ι (twistCechLeft (-1)) (twistCechRight (-1)) ≫
      kaehlerCechSourceIsoTwist.inv)
    (by
      simp only [Category.assoc]
      rw [kaehlerCechSourceIsoTwist_inv_comp_left,
        kaehlerCechSourceIsoTwist_inv_comp_right]
      simp only [← Category.assoc]
      exact congrArg (fun z => z ≫ kaehlerCechTargetIsoTwist.inv)
        (equalizer.condition (twistCechLeft (-1)) (twistCechRight (-1))))

/-- The actual Kähler Čech equalizer is the already effective geometric
positive twist `O(1)`, whose internal exponent is `-1`. -/
def globalKaehlerDifferentialIsoTwist :
    globalKaehlerDifferentialModule ≅ globalTwistModule (-1) where
  hom := globalKaehlerDifferentialToTwist
  inv := globalTwistToKaehlerDifferential
  hom_inv_id := by
    apply (cancel_mono
      (equalizer.ι kaehlerCechLeft kaehlerCechRight)).1
    rw [Category.id_comp]
    unfold globalKaehlerDifferentialToTwist
    unfold globalTwistToKaehlerDifferential
    rw [Category.assoc, equalizer.lift_ι]
    rw [← Category.assoc, equalizer.lift_ι]
    simp
  inv_hom_id := by
    apply (cancel_mono
      (equalizer.ι (twistCechLeft (-1)) (twistCechRight (-1)))).1
    rw [Category.id_comp]
    unfold globalKaehlerDifferentialToTwist
    unfold globalTwistToKaehlerDifferential
    rw [Category.assoc, equalizer.lift_ι]
    rw [← Category.assoc, equalizer.lift_ι]
    simp

/-! ## Local effectiveness and adjunction comparison -/

/-- Restriction of the descended global object to a standard chart recovers
the affine tilde sheaf of that chart's actual Kähler differential module. -/
def globalKaehlerDifferentialLocalIso (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        globalKaehlerDifferentialModule ≅
      chartCoordinateKaehlerDifferentialSheaf i :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap i)).mapIso
      globalKaehlerDifferentialIsoTwist ≪≫
    globalTwistModuleLocalIso (-1) i ≪≫
    (chartCoordinateKaehlerDifferentialTildeIso i).symm

/-- Literal evaluation of the Kähler Čech equalizer on a standard chart:
restrict the chart projection and then apply the open-immersion counit. -/
def globalKaehlerDifferentialToLocal (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        globalKaehlerDifferentialModule ⟶
      chartCoordinateKaehlerDifferentialSheaf i :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
      (equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
        Pi.π (fun j : Fin 4 ↦ coordinateKaehlerLocalPushforward j) i) ≫
    (Scheme.Modules.restrictAdjunction
      (coordinateChartMap i)).counit.app
        (chartCoordinateKaehlerDifferentialSheaf i)

/-- Literal Čech evaluation is the local effectiveness isomorphism.  The
proof first compares the equalizer projections before restriction and then
uses naturality of the open-immersion counit to cancel the residue frame. -/
theorem globalKaehlerDifferentialToLocal_eq (i : Fin 4) :
    globalKaehlerDifferentialToLocal i =
      (globalKaehlerDifferentialLocalIso i).hom := by
  unfold globalKaehlerDifferentialToLocal
  unfold globalKaehlerDifferentialLocalIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Functor.map_comp]
  change _ = (Scheme.Modules.restrictFunctor
      (coordinateChartMap i)).map globalKaehlerDifferentialToTwist ≫
        (globalTwistModuleLocalIso (-1) i).hom ≫
          (chartCoordinateKaehlerDifferentialTildeIso i).inv
  have hlocal : (globalTwistModuleLocalIso (-1) i).hom =
      globalTwistModuleToLocal (-1) i := rfl
  rw [hlocal, globalTwistModuleToLocal_eq]
  simp only [Functor.map_comp, Category.assoc]
  have hEqualizer :
      globalKaehlerDifferentialToTwist ≫
          equalizer.ι (twistCechLeft (-1)) (twistCechRight (-1)) =
        equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
          kaehlerCechSourceIsoTwist.hom := by
    unfold globalKaehlerDifferentialToTwist
    exact equalizer.lift_ι _ _
  have hProjection :
      kaehlerCechSourceIsoTwist.hom ≫
          Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward (-1) j) i =
        Pi.π (fun j : Fin 4 ↦ coordinateKaehlerLocalPushforward j) i ≫
          (Scheme.Modules.pushforward (coordinateChartMap i)).map
            (chartCoordinateKaehlerDifferentialTildeIso i).hom := by
    unfold kaehlerCechSourceIsoTwist
    exact Pi.mapIso_hom_π _ i
  have hSource :
      globalKaehlerDifferentialToTwist ≫
          equalizer.ι (twistCechLeft (-1)) (twistCechRight (-1)) ≫
          Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward (-1) j) i =
        equalizer.ι kaehlerCechLeft kaehlerCechRight ≫
          Pi.π (fun j : Fin 4 ↦ coordinateKaehlerLocalPushforward j) i ≫
          (Scheme.Modules.pushforward (coordinateChartMap i)).map
            (chartCoordinateKaehlerDifferentialTildeIso i).hom := by
    rw [← Category.assoc, hEqualizer, Category.assoc, hProjection]
  have hSourceMapped := congrArg
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map hSource
  simp only [Functor.map_comp] at hSourceMapped
  have hCounit :
      (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
            ((Scheme.Modules.pushforward (coordinateChartMap i)).map
              (chartCoordinateKaehlerDifferentialTildeIso i).hom) ≫
          (Scheme.Modules.restrictAdjunction
            (coordinateChartMap i)).counit.app
              (coordinateLocalTwistModule (-1) i) ≫
          (chartCoordinateKaehlerDifferentialTildeIso i).inv =
        (Scheme.Modules.restrictAdjunction
          (coordinateChartMap i)).counit.app
            (chartCoordinateKaehlerDifferentialSheaf i) := by
    rw [Adjunction.counit_naturality_assoc]
    simp
  calc
    _ = (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          (equalizer.ι kaehlerCechLeft kaehlerCechRight) ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          (Pi.π (fun j : Fin 4 ↦ coordinateKaehlerLocalPushforward j) i) ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
          ((Scheme.Modules.pushforward (coordinateChartMap i)).map
            (chartCoordinateKaehlerDifferentialTildeIso i).hom) ≫
        (Scheme.Modules.restrictAdjunction
          (coordinateChartMap i)).counit.app
            (coordinateLocalTwistModule (-1) i) ≫
        (chartCoordinateKaehlerDifferentialTildeIso i).inv := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦
          (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
              (equalizer.ι kaehlerCechLeft kaehlerCechRight) ≫
            (Scheme.Modules.restrictFunctor (coordinateChartMap i)).map
              (Pi.π (fun j : Fin 4 ↦ coordinateKaehlerLocalPushforward j) i) ≫ q)
        hCounit.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ q ≫
          (Scheme.Modules.restrictAdjunction
            (coordinateChartMap i)).counit.app
              (coordinateLocalTwistModule (-1) i) ≫
          (chartCoordinateKaehlerDifferentialTildeIso i).inv)
        hSourceMapped.symm

/-- The local effectiveness isomorphism followed by the Jacobian residue
frame trivializes the descended differential object on every chart. -/
def globalKaehlerDifferentialLocalUnitIso (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        globalKaehlerDifferentialModule ≅
      SheafOfModules.unit (coordinateChartScheme i).ringCatSheaf :=
  globalKaehlerDifferentialLocalIso i ≪≫
    chartCoordinateKaehlerDifferentialUnitIso i

/-- The descended actual Kähler object has the verified transition-defined
adjunction line.  This comparison does not identify that line with a
dualizing sheaf. -/
def globalKaehlerDifferentialIsoAdjunctionTransitionLine :
    globalKaehlerDifferentialModule ≅ adjunctionTransitionLine :=
  globalKaehlerDifferentialIsoTwist ≪≫
    adjunctionTransitionLineIsoGlobalTwist.symm

/-- The descended actual Kähler object is the pullback of the ambient
hyperplane twist through the independently verified adjunction transition
line. -/
def globalKaehlerDifferentialIsoCurvePullback :
    globalKaehlerDifferentialModule ≅ curvePullbackTwist (-1) :=
  globalKaehlerDifferentialIsoAdjunctionTransitionLine ≪≫
    adjunctionTransitionLineIsoCurvePullback

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCech
