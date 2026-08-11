import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoChartKoszul
import FLT.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistingTransition

/-!
# Overlap compatibility of the N25 projective Koszul maps

The affine Koszul maps on `D₊(X i)` use the local equations `Q/X_i²` and
`C/X_i³`.  To glue these maps on projective three-space, their restrictions
to `D₊(X i X j)` must commute with the coordinate-ratio transitions of the
negative twists.

This file proves the two complete overlap squares.  The top square has
source `O(-5)` and target `O(-2) ⊕ O(-3)`; the middle square has that direct
sum as source and `O` as target.  Both are structural consequences of the
generic fact that a degree-`e` homogeneous multiplier maps `O(-(d+e))` to
`O(-d)`.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoKoszulTransition

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoConormal
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ordered overlap ring of two ambient projective coordinate charts. -/
abbrev AmbientOverlapRing (i j : Fin 4) :=
  Away standardConePiece (MvPolynomial.X i * MvPolynomial.X j)

/-- Transition of the negative twist `O(-debt)` from the `i`-chart
trivialization to the `j`-chart trivialization. -/
def ambientNegativeTwistTransition (debt : ℕ) (i j : Fin 4) :
    AmbientOverlapRing i j ≃ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  Away.negativeTwistTransition standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) debt

/-- Restriction of multiplication by `Q/X_i²` to the ordered overlap. -/
def ambientQuadricMulLeft (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  Away.homogeneousMulLeft standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 2
    (by simpa using canonicalQuadricPolynomial25Two_isHomogeneous)

/-- Restriction of multiplication by `Q/X_j²` to the ordered overlap. -/
def ambientQuadricMulRight (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  Away.homogeneousMulRight standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 2
    (by simpa using canonicalQuadricPolynomial25Two_isHomogeneous)

/-- Restriction of multiplication by `C/X_i³` to the ordered overlap. -/
def ambientCubicMulLeft (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  Away.homogeneousMulLeft standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 3
    (by simpa using canonicalCubicPolynomial25Two_isHomogeneous)

/-- Restriction of multiplication by `C/X_j³` to the ordered overlap. -/
def ambientCubicMulRight (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  Away.homogeneousMulRight standardConePiece
    (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 3
    (by simpa using canonicalCubicPolynomial25Two_isHomogeneous)

/-- The transition on `O(-2) ⊕ O(-3)` is the product of the two rank-one
coordinate-ratio transitions. -/
def ambientMiddleTwistTransition (i j : Fin 4) :
    AmbientOverlapRing i j × AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j × AmbientOverlapRing i j :=
  (ambientNegativeTwistTransition 2 i j).toLinearMap.prodMap
    (ambientNegativeTwistTransition 3 i j).toLinearMap

/-- The `i`-chart form of the top Koszul map after restriction to the
ordered overlap. -/
def ambientKoszulTopLeft (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j × AmbientOverlapRing i j :=
  (ambientCubicMulLeft i j).prod (-(ambientQuadricMulLeft i j))

/-- The `j`-chart form of the top Koszul map after restriction to the
ordered overlap. -/
def ambientKoszulTopRight (i j : Fin 4) :
    AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j × AmbientOverlapRing i j :=
  (ambientCubicMulRight i j).prod (-(ambientQuadricMulRight i j))

/-- The `i`-chart form of the middle Koszul map after restriction to the
ordered overlap. -/
def ambientKoszulMiddleLeft (i j : Fin 4) :
    AmbientOverlapRing i j × AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  (ambientQuadricMulLeft i j).coprod (ambientCubicMulLeft i j)

/-- The `j`-chart form of the middle Koszul map after restriction to the
ordered overlap. -/
def ambientKoszulMiddleRight (i j : Fin 4) :
    AmbientOverlapRing i j × AmbientOverlapRing i j →ₗ[AmbientOverlapRing i j]
      AmbientOverlapRing i j :=
  (ambientQuadricMulRight i j).coprod (ambientCubicMulRight i j)

/-- The top Koszul differential commutes with the `O(-5)` source transition
and the `O(-2) ⊕ O(-3)` target transition on every ordered pair overlap. -/
theorem ambientKoszulTop_transition (i j : Fin 4) :
    (ambientKoszulTopRight i j).comp
        (ambientNegativeTwistTransition 5 i j).toLinearMap =
      (ambientMiddleTwistTransition i j).comp (ambientKoszulTopLeft i j) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simpa only [ambientKoszulTopRight, ambientKoszulTopLeft,
      ambientMiddleTwistTransition, ambientCubicMulRight, ambientCubicMulLeft,
      ambientNegativeTwistTransition, LinearMap.comp_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.prodMap_apply, Nat.reduceAdd] using
        congrArg (fun f ↦ f x)
        (Away.homogeneousMul_comp_negativeTwistTransition standardConePiece
          (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 2 3
          (by simpa using canonicalCubicPolynomial25Two_isHomogeneous))
  · have h := congrArg (fun f ↦ f x)
        (Away.homogeneousMul_comp_negativeTwistTransition standardConePiece
          (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 3 2
          (by simpa using canonicalQuadricPolynomial25Two_isHomogeneous))
    simpa only [ambientKoszulTopRight, ambientKoszulTopLeft,
      ambientMiddleTwistTransition, ambientQuadricMulRight,
      ambientQuadricMulLeft, ambientNegativeTwistTransition,
      LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.prodMap_apply,
      Function.prod_apply, LinearMap.neg_apply, map_neg, Nat.reduceAdd] using
        congrArg Neg.neg h

/-- The middle Koszul differential commutes with the direct-sum source
transition and the identity transition of `O` on every ordered pair overlap. -/
theorem ambientKoszulMiddle_transition (i j : Fin 4) :
    (ambientKoszulMiddleRight i j).comp (ambientMiddleTwistTransition i j) =
      (ambientNegativeTwistTransition 0 i j).toLinearMap.comp
        (ambientKoszulMiddleLeft i j) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hQ := congrArg (fun f ↦ f x)
    (Away.homogeneousMul_comp_negativeTwistTransition standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 0 2
      (by simpa using canonicalQuadricPolynomial25Two_isHomogeneous))
  have hC := congrArg (fun f ↦ f y)
    (Away.homogeneousMul_comp_negativeTwistTransition standardConePiece
      (coordinate_isHomogeneous i) (coordinate_isHomogeneous j) 0 3
      (by simpa using canonicalCubicPolynomial25Two_isHomogeneous))
  simpa only [ambientKoszulMiddleRight, ambientKoszulMiddleLeft,
    ambientMiddleTwistTransition, ambientQuadricMulRight,
    ambientQuadricMulLeft, ambientCubicMulRight, ambientCubicMulLeft,
    ambientNegativeTwistTransition, LinearMap.comp_apply, LinearMap.coprod_apply,
    LinearMap.prodMap_apply, Prod.fst, Prod.snd, map_add, Nat.zero_add] using
      congrArg₂ (· + ·) hQ hC

end MazurProof.RationalPointsN25QuotientTwoKoszulTransition
