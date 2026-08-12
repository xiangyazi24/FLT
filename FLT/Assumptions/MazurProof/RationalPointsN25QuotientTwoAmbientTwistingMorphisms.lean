import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafGluing

/-!
# Morphisms between effective ambient twists

The ambient twists are defined as Cech equalizers.  A compatible family of
maps on the four chart models, together with its common map on every ordered
overlap, therefore descends to a global morphism.  This file isolates that
categorical mechanism from the N25 equations; the quadric and cubic
multipliers will instantiate it in the global Koszul file.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAmbientTwistingMorphisms

open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

/-! ## Maps of the two ambient Cech diagrams -/

/-- Extend a family of local chart morphisms to the product of their
extensions by zero. -/
def ambientTwistCechSourceMap (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i) :
    twistCechSource d ⟶ twistCechSource e :=
  Limits.Pi.map fun i ↦
    (Scheme.Modules.pushforward (ambientChartMap i)).map (φ i)

/-- Extend a family of overlap morphisms to the product of all ordered
overlap extensions by zero. -/
def ambientTwistCechTargetMap (d e : ℤ)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j) :
    twistCechTarget d ⟶ twistCechTarget e :=
  Limits.Pi.map fun p ↦
    (Scheme.Modules.pushforward (ambientOverlapMap p.1 p.2)).map
      (ψ p.1 p.2)

/-- Compatibility with the transitioned left restriction makes the local
product map commute with the left Cech arrow. -/
theorem ambientTwistCechSourceMap_comp_left (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j)
    (hleft : ∀ i j,
      (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map (φ i) ≫
          (ambientRestrictLeftIso e i j ≪≫
            ambientOverlapTwistIso e i j).hom =
        (ambientRestrictLeftIso d i j ≪≫
            ambientOverlapTwistIso d i j).hom ≫ ψ i j) :
    ambientTwistCechSourceMap d e φ ≫ twistCechLeft e =
      twistCechLeft d ≫ ambientTwistCechTargetMap d e ψ := by
  apply Pi.hom_ext
  intro p
  dsimp only [ambientTwistCechSourceMap, ambientTwistCechTargetMap,
    twistCechLeft]
  rw [Category.assoc, Pi.lift_π]
  rw [Pi.map_π_assoc]
  rw [Category.assoc, Pi.map_π]
  rw [Pi.lift_π_assoc]
  simpa only [pushforwardRestrictionHom, Category.assoc] using congrArg
    (fun z => Pi.π (fun i : Fin 4 ↦ ambientLocalPushforward d i) p.1 ≫ z)
    (Scheme.Modules.pushforwardRestrictionHomOfHom_naturality
      (f := ambientChartMap p.1)
      (k := ambientOverlapToLeft p.1 p.2)
      (h := ambientOverlapMap p.1 p.2) rfl
      (ambientRestrictLeftIso d p.1 p.2 ≪≫
        ambientOverlapTwistIso d p.1 p.2).hom
      (ambientRestrictLeftIso e p.1 p.2 ≪≫
        ambientOverlapTwistIso e p.1 p.2).hom
      (φ p.1) (ψ p.1 p.2) (hleft p.1 p.2))

/-- Compatibility with the untransitioned right restriction gives the
corresponding square for the right Cech arrow. -/
theorem ambientTwistCechSourceMap_comp_right (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j)
    (hright : ∀ i j,
      (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).map (φ j) ≫
          (ambientRestrictRightIso e i j).hom =
        (ambientRestrictRightIso d i j).hom ≫ ψ i j) :
    ambientTwistCechSourceMap d e φ ≫ twistCechRight e =
      twistCechRight d ≫ ambientTwistCechTargetMap d e ψ := by
  apply Pi.hom_ext
  intro p
  dsimp only [ambientTwistCechSourceMap, ambientTwistCechTargetMap,
    twistCechRight]
  rw [Category.assoc, Pi.lift_π]
  rw [Pi.map_π_assoc]
  rw [Category.assoc, Pi.map_π]
  rw [Pi.lift_π_assoc]
  simpa only [pushforwardRestrictionHom, Category.assoc] using congrArg
    (fun z => Pi.π (fun i : Fin 4 ↦ ambientLocalPushforward d i) p.2 ≫ z)
    (Scheme.Modules.pushforwardRestrictionHomOfHom_naturality
      (f := ambientChartMap p.2)
      (k := ambientOverlapToRight p.1 p.2)
      (h := ambientOverlapMap p.1 p.2)
      (ambientOverlapMap_eq_right p.1 p.2)
      (ambientRestrictRightIso d p.1 p.2).hom
      (ambientRestrictRightIso e p.1 p.2).hom
      (φ p.2) (ψ p.1 p.2) (hright p.1 p.2))

/-! ## The induced global morphism -/

/-- A pairwise compatible family of local morphisms descends through the two
Cech equalizers to a morphism of effective ambient twists. -/
def ambientGlobalTwistMap (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j)
    (hleft : ∀ i j,
      (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).map (φ i) ≫
          (ambientRestrictLeftIso e i j ≪≫
            ambientOverlapTwistIso e i j).hom =
        (ambientRestrictLeftIso d i j ≪≫
            ambientOverlapTwistIso d i j).hom ≫ ψ i j)
    (hright : ∀ i j,
      (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).map (φ j) ≫
          (ambientRestrictRightIso e i j).hom =
        (ambientRestrictRightIso d i j).hom ≫ ψ i j) :
    globalTwistModule d ⟶ globalTwistModule e :=
  equalizer.lift
    (equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
      ambientTwistCechSourceMap d e φ)
    (by
      simp only [Category.assoc]
      rw [ambientTwistCechSourceMap_comp_left d e φ ψ hleft]
      rw [ambientTwistCechSourceMap_comp_right d e φ ψ hright]
      simpa only [globalTwistModule, Category.assoc] using congrArg
        (fun z => z ≫ ambientTwistCechTargetMap d e ψ)
        (globalTwistModule_compatibility d))

/-- Forgetting the target equalizer condition recovers the componentwise
local product map used to define the global morphism. -/
@[reassoc]
theorem ambientGlobalTwistMap_comp_ι (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j)
    (hleft) (hright) :
    ambientGlobalTwistMap d e φ ψ hleft hright ≫
        equalizer.ι (twistCechLeft e) (twistCechRight e) =
      equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
        ambientTwistCechSourceMap d e φ :=
  equalizer.lift_ι _ _

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a descended morphism on chart `k` is the original local
coefficient morphism.  This is the precise effectivity statement needed to
transport local exactness: the Cech equalizer does not merely produce some
global arrow, but produces the unique arrow whose restriction is the given
chartwise family. -/
theorem ambientGlobalTwistMap_restrict_comp_evaluation (d e : ℤ)
    (φ : ∀ i : Fin 4,
      ambientLocalTwistModule d i ⟶ ambientLocalTwistModule e i)
    (ψ : ∀ i j : Fin 4,
      ambientOverlapTwistModule d i j ⟶ ambientOverlapTwistModule e i j)
    (hleft) (hright) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (ambientGlobalTwistMap d e φ ψ hleft hright) ≫
        globalTwistModuleToLocal e k =
      globalTwistModuleToLocal d k ≫ φ k := by
  apply ((Scheme.Modules.restrictAdjunction
    (ambientChartMap k)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [globalTwistModuleToLocal, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  rw [ambientGlobalTwistMap_comp_ι_assoc]
  unfold ambientTwistCechSourceMap
  rw [Category.assoc, Pi.map_π]

end MazurProof.RationalPointsN25QuotientTwoAmbientTwistingMorphisms
