import FLT.Assumptions.MazurProof.GlueDataClosedBaseChangeTransition
import FLT.Assumptions.MazurProof.N13ClosedFiberGlueComparison

/-!
# Compatibility of the N13 closed-fibre transition

The transition between the two ordinary overlap charts base-changes to
the transition between the corresponding special-fibre charts.  The
proof factors through the general compatibility of
`Scheme.Pullback.t` with direct overlap base change and the concrete
ring square for the two N13 overlap reductions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberGlueTransition

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

private abbrev P :=
  Scheme.Pullback.gluing
    D.openCover
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

private abbrev S :=
  N13SpecialFibreScheme.glueData

private theorem false_ne_true : false ≠ true := by
  decide

private def ordinaryTransition :
    Spec (.of N13OrdinaryCurveOverlap.AffineOverlap) ⟶
      Spec (.of N13OrdinaryCurveOverlap.InfinityOverlap) :=
  Spec.map
    (CommRingCat.ofHom
      N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom)

private def specialTransition :
    Spec (.of N13SpecialCurveOverlap.AffineOverlap) ⟶
      Spec (.of N13SpecialCurveOverlap.InfinityOverlap) :=
  Spec.map
    (CommRingCat.ofHom
      N13SpecialCurveOverlap.overlapEquiv.symm.toRingHom)

private theorem transition_toBase :
    ordinaryTransition ≫
        N13ClosedFiberOverlaps.infinityOverlapToBase =
      N13ClosedFiberOverlaps.affineOverlapToBase := by
  calc
    ordinaryTransition ≫
        N13ClosedFiberOverlaps.infinityOverlapToBase =
      ordinaryTransition ≫
        (N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom ≫
          GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false) := by
              exact congrArg
                (fun k =>
                  ordinaryTransition ≫ k)
                N13ClosedFiberGlueOverlaps.infinityOverlapIso_hom_overlapToBase.symm
    _ =
      (ordinaryTransition ≫
          N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom) ≫
        GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase true false :=
            (Category.assoc _ _ _).symm
    _ =
      (N13ClosedFiberGlueOverlaps.affineOverlapIso.hom ≫
          D.t false true) ≫
        GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase true false := by
            exact congrArg
              (fun k =>
                k ≫ GlueDataClosedBaseChange.overlapToBase
                  D N13IntegralCurveScheme.toBase true false)
              (by
                simpa only [ordinaryTransition,
                  N13ClosedFiberGlueOverlaps.affineOverlapIso,
                  N13ClosedFiberGlueOverlaps.infinityOverlapIso,
                  N13IntegralCurveScheme.transition,
                  N13IntegralCurveScheme.overlap] using
                    N13IntegralCurveScheme.affineOverlapToGlueDataIso_hom_t.symm)
    _ =
      N13ClosedFiberGlueOverlaps.affineOverlapIso.hom ≫
        (D.t false true ≫
          GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false) :=
              Category.assoc _ _ _
    _ =
      N13ClosedFiberGlueOverlaps.affineOverlapIso.hom ≫
        GlueDataClosedBaseChange.overlapToBase
          D N13IntegralCurveScheme.toBase false true := by
            apply congrArg
            simpa only [GlueDataClosedBaseChange.overlapToBase,
              Category.assoc] using
                congrArg
                  (fun k => k ≫ N13IntegralCurveScheme.toBase)
                  (D.glue_condition false true)
    _ = N13ClosedFiberOverlaps.affineOverlapToBase :=
      N13ClosedFiberGlueOverlaps.affineOverlapIso_hom_overlapToBase

/-- Direct base change of the ordinary affine-to-infinity overlap
transition. -/
def overlapTransitionBaseChange :
    pullback
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap ⟶
      pullback
        N13ClosedFiberOverlaps.infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap :=
  pullback.map
    N13ClosedFiberOverlaps.affineOverlapToBase
    N13ClosedFiberCharts.closedBaseMap
    N13ClosedFiberOverlaps.infinityOverlapToBase
    N13ClosedFiberCharts.closedBaseMap
    ordinaryTransition
    (𝟙 _)
    (𝟙 _)
    (by
      simpa only [Category.comp_id,
        N13IntegralCurveScheme.transition,
        N13IntegralCurveScheme.overlap] using transition_toBase.symm)
    (by simp)

@[reassoc]
theorem overlapTransitionBaseChange_fst :
    overlapTransitionBaseChange ≫
        pullback.fst
          N13ClosedFiberOverlaps.infinityOverlapToBase
          N13ClosedFiberCharts.closedBaseMap =
      pullback.fst
            N13ClosedFiberOverlaps.affineOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        ordinaryTransition := by
  unfold overlapTransitionBaseChange
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem overlapTransitionBaseChange_snd :
    overlapTransitionBaseChange ≫
        pullback.snd
          N13ClosedFiberOverlaps.infinityOverlapToBase
          N13ClosedFiberCharts.closedBaseMap =
      pullback.snd
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap := by
  unfold overlapTransitionBaseChange
  exact pullback.lift_snd _ _ _

private theorem specialTransition_reduce :
    specialTransition ≫
        Spec.map
          (CommRingCat.ofHom
            N13OverlapReductionCompatibility.reduceInfinityOverlap) =
      Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceAffineOverlap) ≫
        ordinaryTransition := by
  change
    Spec.map
          (CommRingCat.ofHom
            N13SpecialCurveOverlap.overlapEquiv.symm.toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            N13OverlapReductionCompatibility.reduceInfinityOverlap) =
      Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceAffineOverlap) ≫
        Spec.map
          (CommRingCat.ofHom
            N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    N13OverlapReductionCompatibility.reduceAffineOverlap_comp_infinityOverlapToAffineOverlap.symm

/-- The direct overlap base-change transition is identified with the
special-fibre transition by the two closed-fibre isomorphisms. -/
private theorem overlapTransition_closedFiber_explicit :
    overlapTransitionBaseChange ≫
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        specialTransition := by
  letI :
      IsClosedImmersion
        (Spec.map
          (CommRingCat.ofHom
            N13OverlapReductionCompatibility.reduceInfinityOverlap)) :=
    IsClosedImmersion.spec_of_surjective _
      N13ClosedFiberOverlaps.reduceInfinityOverlap_surjective
  apply (cancel_mono
    (Spec.map
      (CommRingCat.ofHom
        N13OverlapReductionCompatibility.reduceInfinityOverlap))).mp
  calc
    (overlapTransitionBaseChange ≫
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom) ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceInfinityOverlap) =
      overlapTransitionBaseChange ≫
        (N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceInfinityOverlap)) :=
                Category.assoc _ _ _
    _ =
      overlapTransitionBaseChange ≫
        pullback.fst
          N13ClosedFiberOverlaps.infinityOverlapToBase
          N13ClosedFiberCharts.closedBaseMap := by
            exact congrArg
              (fun k => overlapTransitionBaseChange ≫ k)
              N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso_hom_reduceInfinityOverlap
    _ =
      pullback.fst
            N13ClosedFiberOverlaps.affineOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        ordinaryTransition :=
          overlapTransitionBaseChange_fst
    _ =
      (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceAffineOverlap)) ≫
        ordinaryTransition := by
          exact congrArg
            (fun k =>
              k ≫ ordinaryTransition)
            N13ClosedFiberOverlaps.affineOverlapClosedFiberIso_hom_reduceAffineOverlap.symm
    _ =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (Spec.map
              (CommRingCat.ofHom
                N13OverlapReductionCompatibility.reduceAffineOverlap) ≫
          ordinaryTransition) :=
            Category.assoc _ _ _
    _ =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (specialTransition ≫
          Spec.map
            (CommRingCat.ofHom
              N13OverlapReductionCompatibility.reduceInfinityOverlap)) := by
                exact congrArg
                  (fun k =>
                    N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫ k)
                  specialTransition_reduce.symm
    _ =
      (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
          specialTransition) ≫
        Spec.map
          (CommRingCat.ofHom
            N13OverlapReductionCompatibility.reduceInfinityOverlap) :=
              (Category.assoc _ _ _).symm

/-- The direct overlap base-change transition is identified with the
special-fibre glue-data transition. -/
theorem overlapTransition_closedFiber :
    overlapTransitionBaseChange ≫
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        N13SpecialFibreScheme.transition false true false_ne_true := by
  change
    overlapTransitionBaseChange ≫
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        specialTransition
  exact overlapTransition_closedFiber_explicit

@[reassoc]
theorem affineOverlapBaseChangeTransportIso_hom_fst :
    N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        pullback.fst
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase false true)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.fst
            N13ClosedFiberOverlaps.affineOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        N13ClosedFiberGlueOverlaps.affineOverlapIso.hom := by
  unfold N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem affineOverlapBaseChangeTransportIso_hom_snd :
    N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        pullback.snd
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase false true)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.snd
        N13ClosedFiberOverlaps.affineOverlapToBase
        N13ClosedFiberCharts.closedBaseMap := by
  unfold N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso
  exact pullback.lift_snd _ _ _

@[reassoc]
theorem infinityOverlapBaseChangeTransportIso_hom_fst :
    N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom ≫
        pullback.fst
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.fst
            N13ClosedFiberOverlaps.infinityOverlapToBase
            N13ClosedFiberCharts.closedBaseMap ≫
        N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom := by
  unfold N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem infinityOverlapBaseChangeTransportIso_hom_snd :
    N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom ≫
        pullback.snd
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false)
          N13ClosedFiberCharts.closedBaseMap =
      pullback.snd
        N13ClosedFiberOverlaps.infinityOverlapToBase
        N13ClosedFiberCharts.closedBaseMap := by
  unfold N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso
  exact pullback.lift_snd _ _ _

/-- Transporting the general overlap transition through the two
explicit overlap presentations gives the concrete N13 transition base
change. -/
theorem overlapTransition_transport :
    N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        GlueDataClosedBaseChange.overlapTransitionBaseChange
          D N13IntegralCurveScheme.toBase
          N13ClosedFiberCharts.closedBaseMap false true =
      overlapTransitionBaseChange ≫
        N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom := by
  apply pullback.hom_ext
  · calc
      (N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
          GlueDataClosedBaseChange.overlapTransitionBaseChange
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap false true) ≫
        pullback.fst
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false)
          N13ClosedFiberCharts.closedBaseMap =
        N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
          (pullback.fst
                (GlueDataClosedBaseChange.overlapToBase
                  D N13IntegralCurveScheme.toBase false true)
                N13ClosedFiberCharts.closedBaseMap ≫
            D.t false true) := by
              rw [Category.assoc,
                GlueDataClosedBaseChange.overlapTransitionBaseChange_fst]
      _ =
        (pullback.fst
              N13ClosedFiberOverlaps.affineOverlapToBase
              N13ClosedFiberCharts.closedBaseMap ≫
            N13ClosedFiberGlueOverlaps.affineOverlapIso.hom) ≫
          D.t false true := by
            exact congrArg
              (fun k => k ≫ D.t false true)
              affineOverlapBaseChangeTransportIso_hom_fst
      _ =
        pullback.fst
              N13ClosedFiberOverlaps.affineOverlapToBase
              N13ClosedFiberCharts.closedBaseMap ≫
          (N13ClosedFiberGlueOverlaps.affineOverlapIso.hom ≫
            D.t false true) := Category.assoc _ _ _
      _ =
        pullback.fst
              N13ClosedFiberOverlaps.affineOverlapToBase
              N13ClosedFiberCharts.closedBaseMap ≫
          (ordinaryTransition ≫
            N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom) := by
              apply congrArg
              simpa only [ordinaryTransition,
                N13ClosedFiberGlueOverlaps.affineOverlapIso,
                N13ClosedFiberGlueOverlaps.infinityOverlapIso,
                N13IntegralCurveScheme.transition,
                N13IntegralCurveScheme.overlap] using
                  N13IntegralCurveScheme.affineOverlapToGlueDataIso_hom_t
      _ =
        (pullback.fst
              N13ClosedFiberOverlaps.affineOverlapToBase
              N13ClosedFiberCharts.closedBaseMap ≫
            ordinaryTransition) ≫
          N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom :=
            (Category.assoc _ _ _).symm
      _ =
        (overlapTransitionBaseChange ≫
            pullback.fst
              N13ClosedFiberOverlaps.infinityOverlapToBase
              N13ClosedFiberCharts.closedBaseMap) ≫
          N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom := by
            exact congrArg
              (fun k =>
                k ≫ N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom)
              overlapTransitionBaseChange_fst.symm
      _ =
        overlapTransitionBaseChange ≫
          (pullback.fst
                N13ClosedFiberOverlaps.infinityOverlapToBase
                N13ClosedFiberCharts.closedBaseMap ≫
            N13ClosedFiberGlueOverlaps.infinityOverlapIso.hom) :=
              Category.assoc _ _ _
      _ =
        overlapTransitionBaseChange ≫
          (N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom ≫
            pullback.fst
              (GlueDataClosedBaseChange.overlapToBase
                D N13IntegralCurveScheme.toBase true false)
              N13ClosedFiberCharts.closedBaseMap) := by
                exact congrArg
                  (fun k => overlapTransitionBaseChange ≫ k)
                  infinityOverlapBaseChangeTransportIso_hom_fst.symm
      _ =
        (overlapTransitionBaseChange ≫
          N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom) ≫
          pullback.fst
            (GlueDataClosedBaseChange.overlapToBase
              D N13IntegralCurveScheme.toBase true false)
            N13ClosedFiberCharts.closedBaseMap :=
              (Category.assoc _ _ _).symm
  · calc
      (N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
          GlueDataClosedBaseChange.overlapTransitionBaseChange
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap false true) ≫
        pullback.snd
          (GlueDataClosedBaseChange.overlapToBase
            D N13IntegralCurveScheme.toBase true false)
          N13ClosedFiberCharts.closedBaseMap =
        N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
          pullback.snd
            (GlueDataClosedBaseChange.overlapToBase
              D N13IntegralCurveScheme.toBase false true)
            N13ClosedFiberCharts.closedBaseMap := by
              rw [Category.assoc,
                GlueDataClosedBaseChange.overlapTransitionBaseChange_snd]
      _ =
        pullback.snd
          N13ClosedFiberOverlaps.affineOverlapToBase
          N13ClosedFiberCharts.closedBaseMap :=
            affineOverlapBaseChangeTransportIso_hom_snd
      _ =
        overlapTransitionBaseChange ≫
          pullback.snd
            N13ClosedFiberOverlaps.infinityOverlapToBase
            N13ClosedFiberCharts.closedBaseMap :=
              overlapTransitionBaseChange_snd.symm
      _ =
        overlapTransitionBaseChange ≫
          (N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom ≫
            pullback.snd
              (GlueDataClosedBaseChange.overlapToBase
                D N13IntegralCurveScheme.toBase true false)
              N13ClosedFiberCharts.closedBaseMap) := by
                exact congrArg
                  (fun k => overlapTransitionBaseChange ≫ k)
                  infinityOverlapBaseChangeTransportIso_hom_snd.symm
      _ =
        (overlapTransitionBaseChange ≫
          N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom) ≫
          pullback.snd
            (GlueDataClosedBaseChange.overlapToBase
              D N13IntegralCurveScheme.toBase true false)
            N13ClosedFiberCharts.closedBaseMap :=
              (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The concrete overlap transition is the transition of the pullback
gluing under the two explicit overlap presentations. -/
theorem affinePullbackGluingOverlapIso_hom_t :
    N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
        P.t false true =
      overlapTransitionBaseChange ≫
        N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom := by
  rw [N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso,
    N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso,
    Iso.trans_hom, Iso.trans_hom]
  calc
    (N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        (GlueDataClosedBaseChange.overlapBaseChangeIso
          D N13IntegralCurveScheme.toBase
          N13ClosedFiberCharts.closedBaseMap false true).hom) ≫
        P.t false true =
      N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        ((GlueDataClosedBaseChange.overlapBaseChangeIso
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap false true).hom ≫
          P.t false true) := Category.assoc _ _ _
    _ =
      N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        (GlueDataClosedBaseChange.overlapTransitionBaseChange
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap false true ≫
          (GlueDataClosedBaseChange.overlapBaseChangeIso
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap true false).hom) := by
              apply congrArg
              simpa only [P, Scheme.Pullback.gluing_t] using
                GlueDataClosedBaseChange.overlapBaseChangeIso_hom_t
                  D N13IntegralCurveScheme.toBase
                  N13ClosedFiberCharts.closedBaseMap false true
    _ =
      (N13ClosedFiberGlueOverlaps.affineOverlapBaseChangeTransportIso.hom ≫
        GlueDataClosedBaseChange.overlapTransitionBaseChange
          D N13IntegralCurveScheme.toBase
          N13ClosedFiberCharts.closedBaseMap false true) ≫
        (GlueDataClosedBaseChange.overlapBaseChangeIso
          D N13IntegralCurveScheme.toBase
          N13ClosedFiberCharts.closedBaseMap true false).hom :=
            (Category.assoc _ _ _).symm
    _ =
      (overlapTransitionBaseChange ≫
        N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom) ≫
        (GlueDataClosedBaseChange.overlapBaseChangeIso
          D N13IntegralCurveScheme.toBase
          N13ClosedFiberCharts.closedBaseMap true false).hom := by
            exact congrArg
              (fun k =>
                k ≫
                  (GlueDataClosedBaseChange.overlapBaseChangeIso
                    D N13IntegralCurveScheme.toBase
                    N13ClosedFiberCharts.closedBaseMap
                    true false).hom)
              overlapTransition_transport
    _ =
      overlapTransitionBaseChange ≫
        (N13ClosedFiberGlueOverlaps.infinityOverlapBaseChangeTransportIso.hom ≫
          (GlueDataClosedBaseChange.overlapBaseChangeIso
            D N13IntegralCurveScheme.toBase
            N13ClosedFiberCharts.closedBaseMap true false).hom) :=
              Category.assoc _ _ _

/-- Naturality of the `false,true` transition under the overlap
closed-fibre isomorphisms. -/
theorem affinePullback_t :
    P.t false true ≫
        N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom =
      N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom ≫
        S.t false true := by
  apply (cancel_epi
    N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom).mp
  calc
    N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
        (P.t false true ≫
          N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom) =
      (N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
        P.t false true) ≫
          N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom :=
              (Category.assoc _ _ _).symm
    _ =
      (overlapTransitionBaseChange ≫
        N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom) ≫
          N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom := by
              exact congrArg
                (fun k =>
                  k ≫ N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom)
                affinePullbackGluingOverlapIso_hom_t
    _ =
      overlapTransitionBaseChange ≫
        (N13ClosedFiberGlueOverlaps.infinityPullbackGluingOverlapIso.hom ≫
          N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom) :=
              Category.assoc _ _ _
    _ =
      overlapTransitionBaseChange ≫
        (N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom ≫
          N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom) := by
              apply congrArg
              simp [N13ClosedFiberGlueComparison.infinityPullbackOverlapIso,
                Iso.trans_hom]
    _ =
      (overlapTransitionBaseChange ≫
        N13ClosedFiberOverlaps.infinityOverlapClosedFiberIso.hom) ≫
          N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom :=
              (Category.assoc _ _ _).symm
    _ =
      (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        N13SpecialFibreScheme.transition
          false true false_ne_true) ≫
          N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom := by
              exact congrArg
                (fun k =>
                  k ≫ N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom)
                overlapTransition_closedFiber
    _ =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (N13SpecialFibreScheme.transition
            false true false_ne_true ≫
          N13SpecialFibreScheme.infinityOverlapToGlueDataIso.hom) :=
              Category.assoc _ _ _
    _ =
      N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        (N13SpecialFibreScheme.affineOverlapToGlueDataIso.hom ≫
          S.t false true) := by
            exact congrArg
              (fun k =>
                N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫ k)
              N13SpecialFibreScheme.affineOverlapToGlueDataIso_hom_t.symm
    _ =
      (N13ClosedFiberOverlaps.affineOverlapClosedFiberIso.hom ≫
        N13SpecialFibreScheme.affineOverlapToGlueDataIso.hom) ≫
          S.t false true :=
            (Category.assoc _ _ _).symm
    _ =
      (N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
        N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom) ≫
          S.t false true := by
            exact congrArg
              (fun k => k ≫ S.t false true)
              (by
                symm
                simp [N13ClosedFiberGlueComparison.affinePullbackOverlapIso,
                  Iso.trans_hom])
    _ =
      N13ClosedFiberGlueOverlaps.affinePullbackGluingOverlapIso.hom ≫
        (N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom ≫
          S.t false true) :=
            Category.assoc _ _ _

/-- Naturality of the reverse `true,false` transition follows formally
from the forward square and the two transition inverse laws. -/
theorem infinityPullback_t :
    P.t true false ≫
        N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom =
      N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom ≫
        S.t true false := by
  apply (cancel_epi (P.t false true)).mp
  calc
    P.t false true ≫
        (P.t true false ≫
          N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom) =
      (P.t false true ≫ P.t true false) ≫
        N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom :=
            (Category.assoc _ _ _).symm
    _ =
      N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom := by
          rw [P.t_inv, Category.id_comp]
    _ =
      (N13ClosedFiberGlueComparison.affinePullbackOverlapIso.hom ≫
        S.t false true) ≫ S.t true false := by
          rw [Category.assoc, S.t_inv, Category.comp_id]
    _ =
      (P.t false true ≫
        N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom) ≫
            S.t true false := by
              exact congrArg
                (fun k => k ≫ S.t true false)
                affinePullback_t.symm
    _ =
      P.t false true ≫
        (N13ClosedFiberGlueComparison.infinityPullbackOverlapIso.hom ≫
          S.t true false) :=
            Category.assoc _ _ _

end MazurProof.N13ClosedFiberGlueTransition
