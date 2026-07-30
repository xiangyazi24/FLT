import FLT.Assumptions.MazurProof.N13IntegralFiberDetection
import FLT.Assumptions.MazurProof.N13SpecialDualFrame

/-!
# The finite N13 product-lift seam

The special affine dual frame has three evaluations whose sum is one.
For the integral argument it is unnecessary to lift the six factors
separately.  It suffices to lift each evaluation into the product of the
contracted lattice with its multiplier inverse.  This is a weaker interface
than factorwise dual base change, but it is still the full special trace-unit
certificate and does not follow formally from contraction.

This file records exactly that weaker geometric obligation and connects it
to the generic--special fibre criterion.
-/

open scoped BigOperators nonZeroDivisors

namespace MazurProof.N13SpecialProductLift

noncomputable section

abbrev IntegralRing : Type :=
  N13IntegralFiberDetection.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralFiberDetection.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFiberDetection.FunctionField

abbrev RationalFractionalIdeal : Type :=
  N13IntegralFiberDetection.RationalFractionalIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- The remaining finite affine input: integral representatives of the
three special evaluations, already known to lie in `L * L⁻¹`. -/
structure Data (J : Ideal RationalRing) where
  product : Fin 3 → IntegralRing
  product_mem :
    ∀ i,
      algebraMap IntegralRing FunctionField (product i) ∈
        N13IntegralFractionalHull.contractedFractional J *
          (N13IntegralFractionalHull.contractedFractional J)⁻¹
  reduce_product :
    ∀ i,
      N13IntegralFiberDetection.reduceCoordinate (product i) =
        N13SpecialDualFrame.product i

namespace Data

variable {J : Ideal RationalRing}

/-- The three lifted evaluations have trace one on the special fibre. -/
theorem reduce_sum (D : Data J) :
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

/-- Product-level lifting is enough to make the integral divisorial hull a
unit.  No integral lift of an individual primal or dual factor is used. -/
theorem isUnit_divisorialHull
    (D : Data J)
    (hJ : J ≠ ⊥)
    (hGeneric : IsUnit (J : RationalFractionalIdeal)) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull J) :=
  N13IntegralFiberDetection.isUnit_divisorialHull_of_productWitnesses
      hJ hGeneric D.product D.product_mem D.reduce_sum

end Data

end

end MazurProof.N13SpecialProductLift
