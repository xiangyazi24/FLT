import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoKoszulTransition
import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Restriction of the N25 Koszul multipliers to projective chart overlaps

The algebraic overlap squares identify the dehomogenized quadric and cubic
after passing to the common homogeneous localization.  This file upgrades
that calculation to the actual affine-tilde module-sheaf morphisms obtained
by restricting from either coordinate chart.

Each result conjugates the restricted local morphism through the canonical
identification of the restricted rank-one sheaf with the overlap unit sheaf.
Thus the categorical restriction is exactly tilde of the corresponding
left or right overlap multiplier, with no informal quasi-coherent-sheaf
identification.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoKoszulSheafTransition

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoKoszulTransition
open RationalPointsN25QuotientTwoProj
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ambient coordinate-chart ring as a bundled commutative ring. -/
abbrev AmbientChartRingCat (i : Fin 4) : CommRingCat :=
  .of (Away standardConePiece (MvPolynomial.X i))

/-- The ordered ambient overlap ring as a bundled commutative ring. -/
abbrev AmbientOverlapRingCat (i j : Fin 4) : CommRingCat :=
  .of (AmbientOverlapRing i j)

/-- The ambient standard coordinate chart as an affine scheme. -/
abbrev ambientCoordinateChartScheme (i : Fin 4) : Scheme :=
  Spec (AmbientChartRingCat i)

/-- The standard coordinate chart embedded in binary projective
three-space. -/
def ambientCoordinateChartMap (i : Fin 4) :
    ambientCoordinateChartScheme i ⟶ BinaryProjectiveThreeSpace :=
  Proj.awayι standardConePiece (MvPolynomial.X i)
    (coordinate_isHomogeneous i) (by norm_num)

/-- Every ambient coordinate-chart map is an open immersion. -/
instance ambientCoordinateChartMap_isOpenImmersion (i : Fin 4) :
    IsOpenImmersion (ambientCoordinateChartMap i) := by
  dsimp [ambientCoordinateChartMap]
  infer_instance

/-- The categorical intersection of two ambient coordinate charts is the
explicit homogeneous localization away from their coordinate product. -/
def ambientOverlapPullbackIso (i j : Fin 4) :
    pullback (ambientCoordinateChartMap i) (ambientCoordinateChartMap j) ≅
      Spec (AmbientOverlapRingCat i j) :=
  Proj.pullbackAwayιIso standardConePiece
    (coordinate_isHomogeneous i) (by norm_num)
    (coordinate_isHomogeneous j) (by norm_num) rfl

/-- The ring map restricting functions from the `i`-chart to the ordered
`(i,j)` overlap. -/
def ambientOverlapFromLeft (i j : Fin 4) :
    AmbientChartRingCat i ⟶ AmbientOverlapRingCat i j :=
  CommRingCat.ofHom <| HomogeneousLocalization.awayMap standardConePiece
    (coordinate_isHomogeneous j) rfl

/-- The ring map restricting functions from the `j`-chart to the same
ordered overlap. -/
def ambientOverlapFromRight (i j : Fin 4) :
    AmbientChartRingCat j ⟶ AmbientOverlapRingCat i j :=
  CommRingCat.ofHom <| HomogeneousLocalization.awayMap standardConePiece
    (coordinate_isHomogeneous i) (mul_comm _ _)

/-- The first overlap projection is an open immersion because it is affine
localization at the other coordinate. -/
instance ambientOverlapFromLeft_isOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (Spec.map (ambientOverlapFromLeft i j)) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (HomogeneousLocalization.awayMap standardConePiece
      (coordinate_isHomogeneous j) rfl)))
  rw [← Proj.pullbackAwayιIso_inv_fst standardConePiece
    (coordinate_isHomogeneous i) (by norm_num)
    (coordinate_isHomogeneous j) (by norm_num) rfl]
  change IsOpenImmersion
    ((ambientOverlapPullbackIso i j).inv ≫
      pullback.fst (ambientCoordinateChartMap i) (ambientCoordinateChartMap j))
  infer_instance

/-- The second overlap projection is likewise an affine open immersion. -/
instance ambientOverlapFromRight_isOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (Spec.map (ambientOverlapFromRight i j)) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (HomogeneousLocalization.awayMap standardConePiece
      (coordinate_isHomogeneous i) (mul_comm _ _))))
  rw [← Proj.pullbackAwayιIso_inv_snd standardConePiece
    (coordinate_isHomogeneous i) (by norm_num)
    (coordinate_isHomogeneous j) (by norm_num) rfl]
  change IsOpenImmersion
    ((ambientOverlapPullbackIso i j).inv ≫
      pullback.snd (ambientCoordinateChartMap i) (ambientCoordinateChartMap j))
  infer_instance

/-- Restricting multiplication by `Q/X_i²` from the left chart gives the
left overlap multiplier after conjugating both rank-one terms to unit
sheaves. -/
theorem restrictLeft_quadricMul (i j : Fin 4) :
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).inv ≫
        (Scheme.Modules.restrictFunctor
          (Spec.map (ambientOverlapFromLeft i j))).map
          ((tilde.functor (AmbientChartRingCat i)).map
            (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedQuadric i)))) ≫
        (Scheme.Modules.restrictUnitIso
          (Spec.map (ambientOverlapFromLeft i j))).hom =
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientQuadricMulLeft i j)) := by
  simpa [ambientOverlapFromLeft, ambientQuadricMulLeft,
    Away.homogeneousMulLeft, Away.homogeneousElementLeft,
    dehomogenizedQuadric] using
    (Scheme.Modules.restrictUnitIso_conjugate_tildeMul
      (ambientOverlapFromLeft i j) (dehomogenizedQuadric i))

/-- Restricting multiplication by `Q/X_j²` from the right chart gives the
right overlap multiplier after the same unit-sheaf conjugation. -/
theorem restrictRight_quadricMul (i j : Fin 4) :
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).inv ≫
        (Scheme.Modules.restrictFunctor
          (Spec.map (ambientOverlapFromRight i j))).map
          ((tilde.functor (AmbientChartRingCat j)).map
            (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedQuadric j)))) ≫
        (Scheme.Modules.restrictUnitIso
          (Spec.map (ambientOverlapFromRight i j))).hom =
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientQuadricMulRight i j)) := by
  simpa [ambientOverlapFromRight, ambientQuadricMulRight,
    Away.homogeneousMulRight, Away.homogeneousElementRight,
    dehomogenizedQuadric] using
    (Scheme.Modules.restrictUnitIso_conjugate_tildeMul
      (ambientOverlapFromRight i j) (dehomogenizedQuadric j))

/-- Restricting multiplication by `C/X_i³` from the left chart gives the
left cubic overlap multiplier. -/
theorem restrictLeft_cubicMul (i j : Fin 4) :
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromLeft i j))).inv ≫
        (Scheme.Modules.restrictFunctor
          (Spec.map (ambientOverlapFromLeft i j))).map
          ((tilde.functor (AmbientChartRingCat i)).map
            (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedCubic i)))) ≫
        (Scheme.Modules.restrictUnitIso
          (Spec.map (ambientOverlapFromLeft i j))).hom =
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientCubicMulLeft i j)) := by
  simpa [ambientOverlapFromLeft, ambientCubicMulLeft,
    Away.homogeneousMulLeft, Away.homogeneousElementLeft,
    dehomogenizedCubic] using
    (Scheme.Modules.restrictUnitIso_conjugate_tildeMul
      (ambientOverlapFromLeft i j) (dehomogenizedCubic i))

/-- Restricting multiplication by `C/X_j³` from the right chart gives the
right cubic overlap multiplier. -/
theorem restrictRight_cubicMul (i j : Fin 4) :
    (Scheme.Modules.restrictUnitIso
      (Spec.map (ambientOverlapFromRight i j))).inv ≫
        (Scheme.Modules.restrictFunctor
          (Spec.map (ambientOverlapFromRight i j))).map
          ((tilde.functor (AmbientChartRingCat j)).map
            (ModuleCat.ofHom (LinearMap.lsmul _ _ (dehomogenizedCubic j)))) ≫
        (Scheme.Modules.restrictUnitIso
          (Spec.map (ambientOverlapFromRight i j))).hom =
      (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom (ambientCubicMulRight i j)) := by
  simpa [ambientOverlapFromRight, ambientCubicMulRight,
    Away.homogeneousMulRight, Away.homogeneousElementRight,
    dehomogenizedCubic] using
    (Scheme.Modules.restrictUnitIso_conjugate_tildeMul
      (ambientOverlapFromRight i j) (dehomogenizedCubic j))

/-! ## The two Koszul squares as overlap module-sheaf squares -/

/-- The `i`-chart top Koszul morphism after affine tilde on the overlap. -/
def ambientKoszulTopLeftSheaf (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientKoszulTopLeft i j))

/-- The `j`-chart top Koszul morphism after affine tilde on the overlap. -/
def ambientKoszulTopRightSheaf (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientKoszulTopRight i j))

/-- The `i`-chart middle Koszul morphism after affine tilde on the overlap. -/
def ambientKoszulMiddleLeftSheaf (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientKoszulMiddleLeft i j))

/-- The `j`-chart middle Koszul morphism after affine tilde on the overlap. -/
def ambientKoszulMiddleRightSheaf (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientKoszulMiddleRight i j))

/-- Affine tilde of the rank-one transition for `O(-debt)`. -/
def ambientNegativeTwistTransitionSheaf (debt : ℕ) (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientNegativeTwistTransition debt i j).toLinearMap)

/-- Affine tilde of the direct-sum transition for `O(-2) ⊕ O(-3)`. -/
def ambientMiddleTwistTransitionSheaf (i j : Fin 4) :=
  (tilde.functor (AmbientOverlapRingCat i j)).map
    (ModuleCat.ofHom (ambientMiddleTwistTransition i j))

/-- The top Koszul square commutes as a square of actual module sheaves on
every ordered affine overlap. -/
theorem ambientKoszulTopSheaf_transition (i j : Fin 4) :
    ambientNegativeTwistTransitionSheaf 5 i j ≫
        ambientKoszulTopRightSheaf i j =
      ambientKoszulTopLeftSheaf i j ≫ ambientMiddleTwistTransitionSheaf i j := by
  simpa only [ambientNegativeTwistTransitionSheaf,
    ambientKoszulTopRightSheaf, ambientKoszulTopLeftSheaf,
    ambientMiddleTwistTransitionSheaf, ModuleCat.ofHom_comp,
    Functor.map_comp] using congrArg
      (fun f ↦ (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom f)) (ambientKoszulTop_transition i j)

/-- The middle Koszul square commutes as a square of actual module sheaves on
every ordered affine overlap. -/
theorem ambientKoszulMiddleSheaf_transition (i j : Fin 4) :
    ambientMiddleTwistTransitionSheaf i j ≫
        ambientKoszulMiddleRightSheaf i j =
      ambientKoszulMiddleLeftSheaf i j ≫
        ambientNegativeTwistTransitionSheaf 0 i j := by
  simpa only [ambientMiddleTwistTransitionSheaf,
    ambientKoszulMiddleRightSheaf, ambientKoszulMiddleLeftSheaf,
    ambientNegativeTwistTransitionSheaf, ModuleCat.ofHom_comp,
    Functor.map_comp] using congrArg
      (fun f ↦ (tilde.functor (AmbientOverlapRingCat i j)).map
        (ModuleCat.ofHom f)) (ambientKoszulMiddle_transition i j)

end MazurProof.RationalPointsN25QuotientTwoKoszulSheafTransition
