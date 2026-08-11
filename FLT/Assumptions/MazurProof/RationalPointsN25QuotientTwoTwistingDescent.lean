import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingSheafCharts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

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
