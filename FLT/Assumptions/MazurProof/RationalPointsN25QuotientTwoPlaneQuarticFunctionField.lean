import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneQuarticSeparable

/-!
# The plane function field as a separable quartic

The fraction field of the integral plane model carries the compatible
`F₂(z)`-algebra structure.  Mapping the generic quartic root to the existing
plane `x` coordinate gives an algebra equivalence with the separable quartic
constructed over `F₂(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneQuarticFunctionField

open Polynomial
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneQuarticSeparable

local notation "k₂" => ZMod 2
local notation "Rz" => Polynomial k₂
local notation "Fz" => RatFunc k₂

private theorem planeSexticPolynomial_degree_ne_zero :
    planeSexticPolynomial.degree ≠ 0 := by
  rw [degree_eq_natDegree planeSexticPolynomial_monic.ne_zero,
    planeSexticPolynomial_natDegree]
  norm_num

/-- The coefficient map stays injective in the integral plane model. -/
instance planeCoordinateRing_rzFaithful :
    FaithfulSMul Rz PlaneCoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective Rz PlaneCoordinateRing).2
    (AdjoinRoot.of.injective_of_degree_ne_zero
      planeSexticPolynomial_degree_ne_zero)

/-- The rational function field acts on the plane function field through the
universal fraction map from `F₂[z]`. -/
instance planeFunctionField_fzAlgebra : Algebra Fz PlaneFunctionField :=
  RatFunc.liftAlgebra k₂ PlaneFunctionField

private instance planeCoordinateRing_finite :
    Module.Finite Rz PlaneCoordinateRing :=
  planeSexticPolynomial_monic.finite_adjoinRoot

private instance planeCoordinateRing_algebraic :
    Algebra.IsAlgebraic Rz PlaneCoordinateRing :=
  Algebra.IsAlgebraic.of_finite Rz PlaneCoordinateRing

/-- The existing plane function field has degree four over `F₂(z)`. -/
theorem planeFunctionField_finrank :
    Module.finrank Fz PlaneFunctionField = 4 := by
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing
    Rz Fz PlaneCoordinateRing PlaneFunctionField]
  change Module.finrank Rz (AdjoinRoot planeSexticPolynomial) = 4
  rw [(AdjoinRoot.powerBasis' planeSexticPolynomial_monic).finrank]
  exact planeSexticPolynomial_natDegree

/-- The two universal affine coordinates inside the plane function field. -/
def planeFunctionX : PlaneFunctionField :=
  algebraMap PlaneCoordinateRing PlaneFunctionField planeX

def planeFunctionZ : PlaneFunctionField :=
  algebraMap PlaneCoordinateRing PlaneFunctionField planeZ

theorem planeFunctionZ_eq_algebraMap_X :
    planeFunctionZ = algebraMap Rz PlaneFunctionField X := by
  rfl

/-- The plane projection coordinate is the image of the rational-function
parameter. -/
theorem planeFunctionZ_eq_algebraMap_ratFuncX :
    planeFunctionZ =
      algebraMap Fz PlaneFunctionField (RatFunc.X : Fz) := by
  rw [planeFunctionZ_eq_algebraMap_X]
  calc
    algebraMap Rz PlaneFunctionField X =
        algebraMap Fz PlaneFunctionField (algebraMap Rz Fz X) :=
      IsScalarTower.algebraMap_apply Rz Fz PlaneFunctionField X
    _ = algebraMap Fz PlaneFunctionField (RatFunc.X : Fz) := by
      rw [RatFunc.algebraMap_X]

/-- The integral defining polynomial still vanishes after entering the
fraction field. -/
theorem planeSexticPolynomial_eval_planeFunctionX :
    planeSexticPolynomial.eval₂ (algebraMap Rz PlaneFunctionField)
        planeFunctionX = 0 := by
  rw [← map_zero (algebraMap PlaneCoordinateRing PlaneFunctionField),
    ← AdjoinRoot.eval₂_root planeSexticPolynomial]
  simp only [planeFunctionX, planeX]
  rw [hom_eval₂]
  rfl

/-- After coefficient localization, the same coordinate is a root of the
generic quartic over `F₂(z)`. -/
theorem planeQuarticRatFunc_eval_planeFunctionX :
    planeQuarticRatFunc.eval₂ (algebraMap Fz PlaneFunctionField)
        planeFunctionX = 0 := by
  rw [planeQuarticRatFunc, eval₂_map]
  rw [← IsScalarTower.algebraMap_eq Rz Fz PlaneFunctionField]
  exact planeSexticPolynomial_eval_planeFunctionX

/-- Map the generic quartic field to the existing plane function field by
sending its root to the plane `x` coordinate. -/
def planeQuarticToFunctionField :
    PlaneQuarticField →ₐ[Fz] PlaneFunctionField :=
  AdjoinRoot.liftAlgHom planeQuarticRatFunc
    (Algebra.ofId Fz PlaneFunctionField) planeFunctionX
    planeQuarticRatFunc_eval_planeFunctionX

@[simp] theorem planeQuarticToFunctionField_root :
    planeQuarticToFunctionField (AdjoinRoot.root planeQuarticRatFunc) =
      planeFunctionX := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem planeQuarticToFunctionField_bijective :
    Function.Bijective planeQuarticToFunctionField := by
  letI : FiniteDimensional Fz PlaneQuarticField :=
    FiniteDimensional.of_finrank_pos (by
      rw [planeQuarticField_finrank]
      norm_num)
  letI : FiniteDimensional Fz PlaneFunctionField :=
    FiniteDimensional.of_finrank_pos (by
      rw [planeFunctionField_finrank]
      norm_num)
  have hinjective : Function.Injective planeQuarticToFunctionField :=
    RingHom.injective planeQuarticToFunctionField.toRingHom
  refine ⟨hinjective, ?_⟩
  have hfinrank : Module.finrank Fz PlaneQuarticField =
      Module.finrank Fz PlaneFunctionField := by
    rw [planeQuarticField_finrank, planeFunctionField_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := planeQuarticToFunctionField.toLinearMap) hfinrank).mp hinjective

/-- The fraction field of the integral plane model is the generic separable
quartic extension of `F₂(z)`. -/
def planeQuarticFunctionFieldEquiv :
    PlaneQuarticField ≃ₐ[Fz] PlaneFunctionField :=
  AlgEquiv.ofBijective planeQuarticToFunctionField
    planeQuarticToFunctionField_bijective

@[simp] theorem planeQuarticFunctionFieldEquiv_root :
    planeQuarticFunctionFieldEquiv (AdjoinRoot.root planeQuarticRatFunc) =
      planeFunctionX := by
  exact planeQuarticToFunctionField_root

/-- The concrete plane function field is finite-dimensional over `F₂(z)`. -/
instance planeFunctionField_finiteDimensional :
    FiniteDimensional Fz PlaneFunctionField :=
  FiniteDimensional.of_finrank_pos (by
    rw [planeFunctionField_finrank]
    norm_num)

/-- Separability transfers from the explicit quartic presentation. -/
instance planeFunctionField_isSeparable :
    Algebra.IsSeparable Fz PlaneFunctionField :=
  AlgEquiv.Algebra.isSeparable planeQuarticFunctionFieldEquiv

/-- The norm of the projection coordinate is the fourth power of the base
parameter. -/
theorem norm_planeFunctionZ :
    Algebra.norm Fz planeFunctionZ = (RatFunc.X : Fz) ^ 4 := by
  rw [planeFunctionZ_eq_algebraMap_ratFuncX, Algebra.norm_algebraMap,
    planeFunctionField_finrank]

end MazurProof.RationalPointsN25QuotientTwoPlaneQuarticFunctionField
