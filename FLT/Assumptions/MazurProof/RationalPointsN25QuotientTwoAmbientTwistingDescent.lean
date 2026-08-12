import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Categorical ambient overlaps for the N25 twisting descent datum

The sheafified Koszul resolution is a complex on binary projective
three-space, so its twisting terms must be descended on the ambient standard
cover.  The affine overlap schemes constructed previously are now identified
with the actual categorical pullbacks of ambient coordinate charts.  This
turns each coordinate-ratio automorphism into a morphism between the two
categorical pullbacks of the local rank-one twist.

This layer deliberately mirrors the already verified quotient-curve descent
interface, but all rings, schemes, and maps here belong to ambient `P^3`.
That separation prevents the quotient curve's effective twist from being
silently reused as an ambient sheaf.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAmbientTwistingDescent

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoKoszulTransition
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The unbundled degree-zero homogeneous localization underlying the `i`-th
ambient chart.  This short alias keeps the geometric gluing formulas legible. -/
abbrev ambientChartRing (i : Fin 4) :=
  Away standardConePiece (MvPolynomial.X i)

/-- Short name for the ambient affine coordinate chart used throughout the
Cech reconstruction argument. -/
abbrev ambientChartScheme (i : Fin 4) := ambientCoordinateChartScheme i

/-- Short name for the open immersion of an ambient coordinate chart. -/
abbrev ambientChartMap (i : Fin 4) := ambientCoordinateChartMap i

/-- The unbundled ring of an ordered ambient pair intersection. -/
abbrev ambientOverlapRing (i j : Fin 4) := AmbientOverlapRing i j

/-- The unbundled ring of an ordered ambient triple intersection. -/
abbrev ambientTripleOverlapRing (i j l : Fin 4) :=
  AmbientTripleOverlapRing i j l

/-! ## The module-sheaf pseudofunctor and chosen ambient intersections -/

/-- The contravariant pseudofunctor of module sheaves used by ambient
descent.  It forgets the right-adjoint component of Mathlib's pullback and
pushforward pseudofunctor. -/
def ambientModulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat :=
  Pseudofunctor.comp Scheme.Modules.pseudofunctor Bicategory.Adj.forget₁

/-- Package the standard categorical pullback without changing its limit
object or projections.  Keeping the standard pullback makes the ambient
`Proj` overlap theorem apply definitionally. -/
def ambientStandardChosenPullback {X₁ X₂ S : Scheme}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) : ChosenPullback f₁ f₂ where
  pullback := pullback f₁ f₂
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := PullbackCone.mkSelfIsLimit (pullback.isLimit _ _)

/-- The chosen categorical intersection of two ambient coordinate charts. -/
def ambientChosenPullback (i j : Fin 4) :
    ChosenPullback (ambientCoordinateChartMap i)
      (ambientCoordinateChartMap j) :=
  ambientStandardChosenPullback (ambientCoordinateChartMap i)
    (ambientCoordinateChartMap j)

/-- The two projections from the self-intersection of an ambient open chart
coincide because its chart map is a monomorphism. -/
theorem ambientChosenPullback_self_p₁_eq_p₂ (i : Fin 4) :
    (ambientChosenPullback i i).p₁ = (ambientChosenPullback i i).p₂ := by
  rw [← cancel_mono (ambientCoordinateChartMap i)]
  exact (ambientChosenPullback i i).condition

/-- The first chosen projection is the base change of an ambient coordinate
open immersion. -/
instance ambientChosenPullbackP₁IsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (ambientChosenPullback i j).p₁ := by
  change IsOpenImmersion
    (pullback.fst (ambientCoordinateChartMap i) (ambientCoordinateChartMap j))
  infer_instance

/-- The second chosen projection is the symmetric base change of an ambient
coordinate open immersion. -/
instance ambientChosenPullbackP₂IsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (ambientChosenPullback i j).p₂ := by
  change IsOpenImmersion
    (pullback.snd (ambientCoordinateChartMap i) (ambientCoordinateChartMap j))
  infer_instance

/-- Identify the chosen categorical pullback with the explicit ambient
homogeneous localization away from `X_i X_j`. -/
def ambientChosenPullbackIso (i j : Fin 4) :
    (ambientChosenPullback i j).pullback ≅
      Spec (AmbientOverlapRingCat i j) :=
  ambientOverlapPullbackIso i j

/-- Under the affine overlap identification, the first chosen projection is
the localization map from the `i`-chart. -/
theorem ambientChosenPullbackIso_inv_p₁ (i j : Fin 4) :
    (ambientChosenPullbackIso i j).inv ≫
        (ambientChosenPullback i j).p₁ =
      Spec.map (ambientOverlapFromLeft i j) := by
  exact Proj.pullbackAwayιIso_inv_fst standardConePiece
    (coordinate_isHomogeneous i) (by norm_num)
    (coordinate_isHomogeneous j) (by norm_num) rfl

/-- Under the affine overlap identification, the second chosen projection is
the localization map from the `j`-chart. -/
theorem ambientChosenPullbackIso_inv_p₂ (i j : Fin 4) :
    (ambientChosenPullbackIso i j).inv ≫
        (ambientChosenPullback i j).p₂ =
      Spec.map (ambientOverlapFromRight i j) := by
  exact Proj.pullbackAwayιIso_inv_snd standardConePiece
    (coordinate_isHomogeneous i) (by norm_num)
    (coordinate_isHomogeneous j) (by norm_num) rfl

/-! ## Ambient twisting transitions on categorical pair overlaps -/

/-- Pullback of the local ambient twist from the first chart is the unit
module sheaf on the categorical intersection. -/
def ambientFirstTwistPullbackUnitIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (ambientChosenPullback i j).p₁).obj
        (ambientLocalTwistModule d i) ≅
      SheafOfModules.unit
        (ambientChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (ambientChosenPullback i j).p₁).mapIso
      (ambientLocalTwistUnitIso d i) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- Pullback of the local ambient twist from the second chart is the same
unit module sheaf on the categorical intersection. -/
def ambientSecondTwistPullbackUnitIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (ambientChosenPullback i j).p₂).obj
        (ambientLocalTwistModule d j) ≅
      SheafOfModules.unit
        (ambientChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (ambientChosenPullback i j).p₂).mapIso
      (ambientLocalTwistUnitIso d j) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- Transport the explicit ambient overlap twist module to the actual
categorical intersection. -/
def ambientTransportedOverlapTwistModule (d : ℤ) (i j : Fin 4) :
    (ambientChosenPullback i j).pullback.Modules :=
  (Scheme.Modules.pullback (ambientChosenPullbackIso i j).hom).obj
    (ambientOverlapTwistModule d i j)

/-- Transport the coordinate-ratio automorphism from the explicit affine
overlap to the categorical intersection. -/
def ambientTransportedOverlapTwistIso (d : ℤ) (i j : Fin 4) :
    ambientTransportedOverlapTwistModule d i j ≅
      ambientTransportedOverlapTwistModule d i j :=
  (Scheme.Modules.pullback (ambientChosenPullbackIso i j).hom).mapIso
    (ambientOverlapTwistIso d i j)

/-- The transported transition on an ambient self-overlap remains the
identity. -/
theorem ambientTransportedOverlapTwistIso_self (d : ℤ) (i : Fin 4) :
    (ambientTransportedOverlapTwistIso d i i).hom = 𝟙 _ := by
  change (Scheme.Modules.pullback
      (ambientChosenPullbackIso i i).hom).map
        (ambientOverlapTwistIso d i i).hom = 𝟙 _
  rw [ambientOverlapTwistIso_self]
  exact (Scheme.Modules.pullback
    (ambientChosenPullbackIso i i).hom).map_id _

/-- The transported affine overlap model is canonically the unit module
sheaf on the categorical intersection. -/
def ambientTransportedOverlapUnitIso (d : ℤ) (i j : Fin 4) :
    ambientTransportedOverlapTwistModule d i j ≅
      SheafOfModules.unit
        (ambientChosenPullback i j).pullback.ringCatSheaf :=
  (Scheme.Modules.pullback (ambientChosenPullbackIso i j).hom).mapIso
      (ambientOverlapTwistUnitIso d i j) ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- Conjugate the transported coordinate-ratio transition to an
automorphism of the unit sheaf on the categorical overlap. -/
def ambientPullbackUnitTransitionIso (d : ℤ) (i j : Fin 4) :
    SheafOfModules.unit
        (ambientChosenPullback i j).pullback.ringCatSheaf ≅
      SheafOfModules.unit
        (ambientChosenPullback i j).pullback.ringCatSheaf :=
  (ambientTransportedOverlapUnitIso d i j).symm ≪≫
    ambientTransportedOverlapTwistIso d i j ≪≫
    ambientTransportedOverlapUnitIso d i j

/-- Unit-sheaf conjugation preserves the identity transition on a repeated
ambient chart. -/
theorem ambientPullbackUnitTransitionIso_self (d : ℤ) (i : Fin 4) :
    (ambientPullbackUnitTransitionIso d i i).hom = 𝟙 _ := by
  change (ambientTransportedOverlapUnitIso d i i).inv ≫
      (ambientTransportedOverlapTwistIso d i i).hom ≫
      (ambientTransportedOverlapUnitIso d i i).hom = 𝟙 _
  rw [ambientTransportedOverlapTwistIso_self, Category.id_comp]
  exact (ambientTransportedOverlapUnitIso d i i).inv_hom_id

/-- The categorical pair-overlap morphism from the first local ambient twist
to the second.  This is the transition used by the ambient Cech equalizer. -/
def ambientTwistDescentHom (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.pullback (ambientChosenPullback i j).p₁).obj
        (ambientLocalTwistModule d i) ⟶
      (Scheme.Modules.pullback (ambientChosenPullback i j).p₂).obj
        (ambientLocalTwistModule d j) :=
  (ambientFirstTwistPullbackUnitIso d i j).hom ≫
    (ambientPullbackUnitTransitionIso d i j).hom ≫
    (ambientSecondTwistPullbackUnitIso d i j).inv

/-- A local ambient twist as an object of the module-sheaf pseudofunctor.
This is the object field required by Mathlib's categorical descent shape. -/
def ambientTwistDescentObj (d : ℤ) (i : Fin 4) :
    ambientModulesPseudofunctor.obj
      (.mk (.op (ambientCoordinateChartScheme i))) :=
  ambientLocalTwistModule d i

/-- The ambient coordinate-ratio transition in the exact pseudofunctorial
type expected on a chosen pair overlap. -/
def ambientTwistDescentHom' (d : ℤ) (i j : Fin 4) :
    (ambientModulesPseudofunctor.map
        (ambientChosenPullback i j).p₁.op.toLoc).toFunctor.obj
          (ambientTwistDescentObj d i) ⟶
      (ambientModulesPseudofunctor.map
        (ambientChosenPullback i j).p₂.op.toLoc).toFunctor.obj
          (ambientTwistDescentObj d j) :=
  ambientTwistDescentHom d i j

/-! ## Compatible chosen triple intersections -/

/-- The standard wide pullback of three ambient coordinate charts.  Its
underlying object first intersects `(i,j)` with `(j,l)` over the middle chart;
the universal property supplies the comparison to `(i,l)`. -/
def ambientChosenTriplePullback (i j l : Fin 4) :
    ChosenPullback₃ (ambientChosenPullback i j)
      (ambientChosenPullback j l) (ambientChosenPullback i l) where
  chosenPullback := ambientStandardChosenPullback
    (ambientChosenPullback i j).p₂
    (ambientChosenPullback j l).p₁
  l := by
    apply Nonempty.some
    apply ChosenPullback.LiftStruct.nonempty
    · simp only [Category.assoc]
      rw [(ambientChosenPullback i j).hp₁,
        (ambientChosenPullback j l).hp₂,
        ← (ambientChosenPullback i j).hp₂,
        ← (ambientChosenPullback j l).hp₁]
      simpa only [Category.assoc] using congrArg
        (fun q ↦ q ≫ ambientCoordinateChartMap j)
        (ambientStandardChosenPullback
          (ambientChosenPullback i j).p₂
          (ambientChosenPullback j l).p₁).condition
    · rfl

end MazurProof.RationalPointsN25QuotientTwoAmbientTwistingDescent
