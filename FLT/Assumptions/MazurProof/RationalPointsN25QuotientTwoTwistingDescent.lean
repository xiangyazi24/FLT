import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingSheafCharts
import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Categorical overlaps for the N25 twisting descent datum

The local twisting sheaves live on the four standard affine charts of the
canonical projective curve.  Descent theory requires their pair overlaps to
be actual categorical pullbacks, rather than merely affine schemes carrying
the expected localization rings.

Mathlib identifies the pullback of two standard `Proj` charts with the
spectrum of the degree-zero localization away from the product of their
coordinates.  This file specializes that theorem to the N25 curve and records
both pullback projections as the expected localization morphisms.  It also
packages the standard categorical pullback as a `ChosenPullback`, which is the
input shape used by Mathlib's descent-data API.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoTwistingDescent

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoTwistingTransition
open RationalPointsN25QuotientTwoTwistingSheafCharts
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

/-! ## The contravariant pseudofunctor of scheme-module pullbacks -/

/-- The pseudofunctor sending a scheme to its category of module sheaves and
a scheme morphism to pullback.  It is obtained by forgetting the right
adjoints from Mathlib's pullback-pushforward pseudofunctor. -/
def coordinateModulesPseudofunctor :
  Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat :=
  Pseudofunctor.comp Scheme.Modules.pseudofunctor Bicategory.Adj.forget₁

/-! ## Pair overlaps as categorical pullbacks -/

/-- The categorical intersection of the `i`-th and `j`-th coordinate charts
is the affine homogeneous localization away from `x_i x_j`. -/
def coordinateOverlapPullbackIso (i j : Fin 4) :
    pullback (coordinateChartMap i) (coordinateChartMap j) ≅
      Spec (.of (coordinateOverlapRing i j)) :=
  Proj.pullbackAwayιIso literalConePiece
    (coordinateClass_mem_degreeOne i) (by norm_num)
    (coordinateClass_mem_degreeOne j) (by norm_num) rfl

/-- The first projection from the affine overlap is induced contravariantly
by localizing the `i`-th chart ring at the `j`-th coordinate. -/
theorem coordinateOverlapPullbackIso_inv_fst (i j : Fin 4) :
    (coordinateOverlapPullbackIso i j).inv ≫
        pullback.fst (coordinateChartMap i) (coordinateChartMap j) =
      Spec.map (CommRingCat.ofHom
        (awayMap literalConePiece
          (coordinateClass_mem_degreeOne j) rfl)) := by
  apply Proj.pullbackAwayιIso_inv_fst

/-- The second projection from the affine overlap is induced contravariantly
by localizing the `j`-th chart ring at the `i`-th coordinate. -/
theorem coordinateOverlapPullbackIso_inv_snd (i j : Fin 4) :
    (coordinateOverlapPullbackIso i j).inv ≫
        pullback.snd (coordinateChartMap i) (coordinateChartMap j) =
      Spec.map (CommRingCat.ofHom
        (awayMap literalConePiece
          (coordinateClass_mem_degreeOne i) (mul_comm _ _))) := by
  apply Proj.pullbackAwayιIso_inv_snd

/-! ## The chosen pullbacks used by categorical descent -/

/-- The standard categorical pullback of two scheme morphisms, packaged as a
chosen pullback without changing its underlying limit object. -/
def standardChosenPullback {X₁ X₂ S : Scheme} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    ChosenPullback f₁ f₂ where
  pullback := pullback f₁ f₂
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := PullbackCone.mkSelfIsLimit (pullback.isLimit _ _)

/-- The canonical categorical pullback of two N25 coordinate charts,
packaged in the form expected by Mathlib's descent-data construction. -/
def coordinateChosenPullback (i j : Fin 4) :
    ChosenPullback (coordinateChartMap i) (coordinateChartMap j) :=
  standardChosenPullback (coordinateChartMap i) (coordinateChartMap j)

/-- Because a coordinate-chart map is a monomorphism, the two projections
from its self-pullback agree.  Categorically, an open chart intersected with
itself is the same open chart. -/
theorem coordinateChosenPullback_self_p₁_eq_p₂ (i : Fin 4) :
    (coordinateChosenPullback i i).p₁ =
      (coordinateChosenPullback i i).p₂ := by
  rw [← cancel_mono (coordinateChartMap i)]
  exact (coordinateChosenPullback i i).condition

/-- The first projection of a coordinate-chart pullback is an open immersion,
as it is the base change of the second coordinate-chart open immersion. -/
instance coordinateChosenPullbackP₁IsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (coordinateChosenPullback i j).p₁ := by
  change IsOpenImmersion
    (pullback.fst (coordinateChartMap i) (coordinateChartMap j))
  infer_instance

/-- The second projection of a coordinate-chart pullback is an open immersion,
as it is the base change of the first coordinate-chart open immersion. -/
instance coordinateChosenPullbackP₂IsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (coordinateChosenPullback i j).p₂ := by
  change IsOpenImmersion
    (pullback.snd (coordinateChartMap i) (coordinateChartMap j))
  infer_instance

/-- The chosen pullback object is identified with the explicit affine pair
overlap used to define the twisting transition. -/
def coordinateChosenPullbackIso (i j : Fin 4) :
    (coordinateChosenPullback i j).pullback ≅
      Spec (.of (coordinateOverlapRing i j)) :=
  coordinateOverlapPullbackIso i j

/-- Under the affine identification, the first projection of the chosen
pullback is the expected localization morphism. -/
theorem coordinateChosenPullbackIso_inv_p₁ (i j : Fin 4) :
    (coordinateChosenPullbackIso i j).inv ≫
        (coordinateChosenPullback i j).p₁ =
      Spec.map (CommRingCat.ofHom
        (awayMap literalConePiece
          (coordinateClass_mem_degreeOne j) rfl)) := by
  exact coordinateOverlapPullbackIso_inv_fst i j

/-- Under the affine identification, the second projection of the chosen
pullback is the expected localization morphism. -/
theorem coordinateChosenPullbackIso_inv_p₂ (i j : Fin 4) :
    (coordinateChosenPullbackIso i j).inv ≫
        (coordinateChosenPullback i j).p₂ =
      Spec.map (CommRingCat.ofHom
        (awayMap literalConePiece
          (coordinateClass_mem_degreeOne i) (mul_comm _ _))) := by
  exact coordinateOverlapPullbackIso_inv_snd i j

/-! ## Twisting transitions on the categorical pair overlaps -/

/-- Pulling the local twist on the first chart back to the categorical pair
overlap gives the unit module sheaf there. -/
def coordinateFirstTwistPullbackUnitIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (coordinateChosenPullback i j).p₁).obj
        (coordinateLocalTwistModule d i) ≅
      SheafOfModules.unit
        (coordinateChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (coordinateChosenPullback i j).p₁).mapIso
      (coordinateLocalTwistUnitIso d i) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- Pulling the local twist on the second chart back to the categorical pair
overlap gives the unit module sheaf there. -/
def coordinateSecondTwistPullbackUnitIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (coordinateChosenPullback i j).p₂).obj
        (coordinateLocalTwistModule d j) ≅
      SheafOfModules.unit
        (coordinateChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (coordinateChosenPullback i j).p₂).mapIso
      (coordinateLocalTwistUnitIso d j) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- The explicit affine overlap module, transported to the categorical
pullback through the proved scheme isomorphism. -/
def coordinateTransportedOverlapTwistModule (d : ℤ) (i j : Fin 4) :
    (coordinateChosenPullback i j).pullback.Modules :=
  (Scheme.Modules.pullback (coordinateChosenPullbackIso i j).hom).obj
    (coordinateOverlapTwistModule d i j)

/-- Transport of the explicit coordinate-ratio transition from the affine
overlap to the actual categorical pullback. -/
def coordinateTransportedOverlapTwistIso (d : ℤ) (i j : Fin 4) :
    coordinateTransportedOverlapTwistModule d i j ≅
      coordinateTransportedOverlapTwistModule d i j :=
  (Scheme.Modules.pullback (coordinateChosenPullbackIso i j).hom).mapIso
    (coordinateOverlapTwistIso d i j)

/-- Transporting a self-overlap transition through the categorical overlap
identification preserves its identity character. -/
theorem coordinateTransportedOverlapTwistIso_self (d : ℤ) (i : Fin 4) :
    (coordinateTransportedOverlapTwistIso d i i).hom = 𝟙 _ := by
  change (Scheme.Modules.pullback
      (coordinateChosenPullbackIso i i).hom).map
        (coordinateOverlapTwistIso d i i).hom = 𝟙 _
  rw [coordinateOverlapTwistIso_self]
  exact (Scheme.Modules.pullback
    (coordinateChosenPullbackIso i i).hom).map_id _

/-- The transported affine overlap module is the unit module sheaf on the
categorical pair overlap. -/
def coordinateTransportedOverlapUnitIso (d : ℤ) (i j : Fin 4) :
    coordinateTransportedOverlapTwistModule d i j ≅
      SheafOfModules.unit
        (coordinateChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (coordinateChosenPullbackIso i j).hom).mapIso
      (coordinateOverlapTwistUnitIso d i j) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- The coordinate-ratio transition, conjugated to an automorphism of the
unit module sheaf on the categorical pair overlap. -/
def coordinatePullbackUnitTransitionIso (d : ℤ) (i j : Fin 4) :
    SheafOfModules.unit
        (coordinateChosenPullback i j).pullback.ringCatSheaf ≅
      SheafOfModules.unit
        (coordinateChosenPullback i j).pullback.ringCatSheaf :=
  (coordinateTransportedOverlapUnitIso d i j).symm ≪≫
    coordinateTransportedOverlapTwistIso d i j ≪≫
    coordinateTransportedOverlapUnitIso d i j

/-- After conjugating to the unit sheaf, the transition on a self-overlap
remains the identity. -/
theorem coordinatePullbackUnitTransitionIso_self (d : ℤ) (i : Fin 4) :
    (coordinatePullbackUnitTransitionIso d i i).hom = 𝟙 _ := by
  change (coordinateTransportedOverlapUnitIso d i i).inv ≫
      (coordinateTransportedOverlapTwistIso d i i).hom ≫
      (coordinateTransportedOverlapUnitIso d i i).hom = 𝟙 _
  rw [coordinateTransportedOverlapTwistIso_self, Category.id_comp]
  exact (coordinateTransportedOverlapUnitIso d i i).inv_hom_id

/-- The pair-overlap morphism in the exact form required by categorical
descent: it maps the pullback of the first chart's local twist to the pullback
of the second chart's local twist. -/
def coordinateTwistDescentHom (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (coordinateChosenPullback i j).p₁).obj
        (coordinateLocalTwistModule d i) ⟶
      (Scheme.Modules.pullback (coordinateChosenPullback i j).p₂).obj
        (coordinateLocalTwistModule d j) :=
  (coordinateFirstTwistPullbackUnitIso d i j).hom ≫
    (coordinatePullbackUnitTransitionIso d i j).hom ≫
    (coordinateSecondTwistPullbackUnitIso d i j).inv

/-- The local twist on one chart, regarded as an object of the module-sheaf
pseudofunctor used by categorical descent. -/
def coordinateTwistDescentObj (d : ℤ) (i : Fin 4) :
    coordinateModulesPseudofunctor.obj
      (.mk (.op (coordinateChartScheme i))) :=
  coordinateLocalTwistModule d i

/-- The coordinate-ratio transition in the precise pseudofunctorial type of
the pair-overlap field of `Pseudofunctor.DescentData'`. -/
def coordinateTwistDescentHom' (d : ℤ) (i j : Fin 4) :
    (coordinateModulesPseudofunctor.map
        (coordinateChosenPullback i j).p₁.op.toLoc).toFunctor.obj
          (coordinateTwistDescentObj d i) ⟶
      (coordinateModulesPseudofunctor.map
        (coordinateChosenPullback i j).p₂.op.toLoc).toFunctor.obj
          (coordinateTwistDescentObj d j) :=
  coordinateTwistDescentHom d i j

/-! ## Chosen triple pullbacks -/

/-- The canonical wide pullback of three coordinate charts.  Its underlying
scheme is the pullback of the `(i,j)` and `(j,l)` pair overlaps over the
middle chart, and its map to the `(i,l)` overlap is supplied by the universal
property. -/
def coordinateChosenTriplePullback (i j l : Fin 4) :
    ChosenPullback₃ (coordinateChosenPullback i j)
      (coordinateChosenPullback j l) (coordinateChosenPullback i l) where
  chosenPullback := standardChosenPullback
    (coordinateChosenPullback i j).p₂
    (coordinateChosenPullback j l).p₁
  l := by
    apply Nonempty.some
    apply ChosenPullback.LiftStruct.nonempty
    · simp only [Category.assoc]
      rw [(coordinateChosenPullback i j).hp₁,
        (coordinateChosenPullback j l).hp₂,
        ← (coordinateChosenPullback i j).hp₂,
        ← (coordinateChosenPullback j l).hp₁]
      simpa only [Category.assoc] using congrArg
        (fun q ↦ q ≫ coordinateChartMap j)
        (standardChosenPullback
          (coordinateChosenPullback i j).p₂
          (coordinateChosenPullback j l).p₁).condition
    · rfl

end MazurProof.RationalPointsN25QuotientTwoTwistingDescent
