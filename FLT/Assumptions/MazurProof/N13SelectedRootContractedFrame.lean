import FLT.Assumptions.MazurProof.N13SpecialProductLift

/-!
# Contracted dual frames for the selected N13 root

The divisorial hull is too large to serve as the affine source of the
module-valued Čech lift: its products naturally lie in `H * H⁻¹`, whereas
the existing finite special-fibre criterion needs products in the smaller
raw contraction defect `C * C⁻¹`.

This file records the exact factor-level output required from a
branch-aware Čech construction.  It retains primal elements in the
contracted lattice and dual elements in its multiplier inverse.  Their
integral products then produce both the existing `SpecialProductLift` and
the stronger contracted dual frame without assuming that the contraction
or its hull is already invertible.
-/

open scoped BigOperators nonZeroDivisors

namespace MazurProof.N13SelectedRootContractedFrame

noncomputable section

abbrev IntegralRing : Type :=
  N13SpecialProductLift.IntegralRing

abbrev RationalRing : Type :=
  N13SpecialProductLift.RationalRing

abbrev FunctionField : Type :=
  N13SpecialProductLift.FunctionField

abbrev RationalFractionalIdeal : Type :=
  N13SpecialProductLift.RationalFractionalIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Exact factor-level output of the missing module-valued Čech lift.
Unlike a frame for the divisorial hull, the two membership fields refer
literally to the contracted generic ideal and its multiplier inverse. -/
structure FactorData (J : Ideal RationalRing) where
  primal : Fin 3 → FunctionField
  dual : Fin 3 → FunctionField
  primal_mem :
    ∀ i,
      primal i ∈
        N13IntegralFractionalHull.contractedFractional J
  dual_mem :
    ∀ i,
      dual i ∈
        (N13IntegralFractionalHull.contractedFractional J)⁻¹
  product : Fin 3 → IntegralRing
  algebraMap_product :
    ∀ i,
      algebraMap IntegralRing FunctionField (product i) =
        primal i * dual i
  reduce_product :
    ∀ i,
      N13IntegralFiberDetection.reduceCoordinate (product i) =
        N13SpecialDualFrame.product i

namespace FactorData

variable {J : Ideal RationalRing}

theorem reduce_sum (D : FactorData J) :
    ∑ i,
        N13IntegralFiberDetection.reduceCoordinate (D.product i) =
      1 := by
  calc
    ∑ i,
          N13IntegralFiberDetection.reduceCoordinate (D.product i) =
        ∑ i, N13SpecialDualFrame.product i := by
      exact Finset.sum_congr rfl
        (fun i _ ↦ D.reduce_product i)
    _ = 1 :=
      N13SpecialDualFrame.sum_product

/-- Forget the individual factors after verifying that each integral
product lies in the raw contraction defect. -/
def toSpecialProductLift
    (D : FactorData J) :
    N13SpecialProductLift.Data J where
  product := D.product
  product_mem := by
    intro i
    rw [D.algebraMap_product i]
    exact
      FractionalIdeal.mul_mem_mul
        (D.primal_mem i) (D.dual_mem i)
  reduce_product := D.reduce_product

/-- Retain the factors as the stronger contracted dual frame consumed by
the generic--special fibre criterion. -/
def toContractedDualFrame
    (D : FactorData J) :
    N13IntegralFiberDetection.ContractedDualFrame J :=
  N13IntegralFiberDetection.ContractedDualFrame.ofProductLifts
    D.primal D.dual D.primal_mem D.dual_mem
    D.product D.algebraMap_product D.reduce_sum

/-- The factor-level Čech output closes the affine divisorial-hull
invertibility seam. -/
theorem isUnit_divisorialHull
    (D : FactorData J)
    (hJ : J ≠ ⊥)
    (hGeneric : IsUnit (J : RationalFractionalIdeal)) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull J) :=
  N13IntegralFiberDetection.isUnit_divisorialHull_of_contractedDualFrame
    hJ hGeneric D.toContractedDualFrame

end FactorData

end

end MazurProof.N13SelectedRootContractedFrame
