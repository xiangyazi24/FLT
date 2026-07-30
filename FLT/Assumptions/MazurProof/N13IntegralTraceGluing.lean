import FLT.Assumptions.MazurProof.N13IntegralFiberDetection
import FLT.Assumptions.MazurProof.N13TraceGluing

/-!
# Trace gluing on the N13 integral model

This specializes the generic fractional-ideal trace lemma to the divisorial
hull of a contracted generic ideal.  The remaining geometric input is only
an aggregate trace congruent to one modulo two, rather than six separately
chosen raw factors.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralTraceGluing

noncomputable section

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- On the N13 model, generic invertibility and one element of the defect
ideal reducing to one are the complete invertibility criterion. -/
theorem divisorialHull_isUnit_of_modTwoTrace
    {J : Ideal RationalRing}
    (hJ : J ≠ ⊥)
    (hGeneric :
      IsUnit
        (J :
          N13IntegralFractionalHull.RationalFractionalIdeal))
    (hTrace :
      ∃ z : IntegralRing,
        z ∈
            N13IntegralFractionalHull.defectIdeal
              (N13IntegralFractionalHull.divisorialHull J) ∧
          N13IntegralFiberDetection.reduceCoordinate z = 1) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  have hHull :
      N13IntegralFractionalHull.divisorialHull J ≠ 0 := by
    intro hzero
    have hle :=
      N13IntegralFractionalHull.contractedFractional_le_divisorialHull
        hJ
    rw [hzero] at hle
    exact
      N13IntegralFractionalHull.contractedFractional_ne_zero hJ
        (bot_unique hle)
  have hExtended :
      IsUnit
        (N13IntegralFractionalHull.extendFractional
          (N13IntegralFractionalHull.divisorialHull J)) := by
    rw [N13IntegralFractionalHull.extendFractional_divisorialHull_eq
      hJ hGeneric]
    exact hGeneric
  exact
    N13IntegralFiberDetection.isUnit_of_exists_defect_reduces_one
      hHull hExtended hTrace

/-- Generic trace gluing specialized to one N13 divisorial hull. -/
theorem divisorialHull_isUnit_of_genericPower_and_modTrace
    (J : Ideal RationalRing)
    {f : IntegralRing}
    (hpow :
      ∃ n : ℕ,
        algebraMap IntegralRing FunctionField (f ^ n) ∈
          N13IntegralFractionalHull.divisorialHull J *
            (N13IntegralFractionalHull.divisorialHull J)⁻¹)
    (hmod :
      ∃ a : IntegralRing,
        algebraMap IntegralRing FunctionField (1 - f * a) ∈
          N13IntegralFractionalHull.divisorialHull J *
            (N13IntegralFractionalHull.divisorialHull J)⁻¹) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) :=
  N13TraceGluing.isUnit_of_genericPower_and_modUniformizerTrace
    (M := N13IntegralFractionalHull.divisorialHull J)
    (f := f) hpow hmod

/-- Mixed-characteristic form with uniformizer two. -/
theorem divisorialHull_isUnit_of_twoPower_and_modTwoTrace
    (J : Ideal RationalRing)
    (hpow :
      ∃ n : ℕ,
        algebraMap IntegralRing FunctionField
            ((2 : IntegralRing) ^ n) ∈
          N13IntegralFractionalHull.divisorialHull J *
            (N13IntegralFractionalHull.divisorialHull J)⁻¹)
    (hmod :
      ∃ a : IntegralRing,
        algebraMap IntegralRing FunctionField
            (1 - (2 : IntegralRing) * a) ∈
          N13IntegralFractionalHull.divisorialHull J *
            (N13IntegralFractionalHull.divisorialHull J)⁻¹) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) :=
  divisorialHull_isUnit_of_genericPower_and_modTrace
    (J := J) (f := (2 : IntegralRing)) hpow hmod

end

end MazurProof.N13IntegralTraceGluing
