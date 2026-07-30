import FLT.Assumptions.MazurProof.N13IntegralFractionalHull
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# Membership criteria for the contracted N13 lattice

The raw contraction is literally an ordinary integral ideal embedded in the
common function field.  This file exposes that definition through reusable
membership criteria.  In particular, inverse membership is reduced to the
non-circular multiplier condition on integral representatives.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13ContractedFractionalMembership

noncomputable section

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- An element of the common function field lies in the raw contraction
exactly when it has an integral representative whose rational image lies in
the original generic ideal. -/
theorem mem_contractedFractional_iff
    {J : Ideal RationalRing} {x : FunctionField} :
    x ∈ N13IntegralFractionalHull.contractedFractional J ↔
      ∃ a : IntegralRing,
        N13IntegralFractionalHull.integralToRational a ∈ J ∧
          algebraMap IntegralRing FunctionField a = x := by
  change
    x ∈
        ((N13IntegralModelContraction.contractIdeal J :
            Ideal IntegralRing) :
          IntegralFractionalIdeal) ↔ _
  rw [FractionalIdeal.mem_coeIdeal IntegralRing⁰]
  rfl

/-- For an already integral element, raw-contraction membership is exactly
generic-ideal membership after rational base change. -/
theorem algebraMap_mem_contractedFractional_iff
    {J : Ideal RationalRing} (a : IntegralRing) :
    algebraMap IntegralRing FunctionField a ∈
        N13IntegralFractionalHull.contractedFractional J ↔
      N13IntegralFractionalHull.integralToRational a ∈ J := by
  change
    algebraMap IntegralRing FunctionField a ∈
        ((N13IntegralModelContraction.contractIdeal J :
            Ideal IntegralRing) :
          IntegralFractionalIdeal) ↔ _
  rw [FractionalIdeal.mem_coeIdeal IntegralRing⁰]
  rw [FractionalIdeal.exists_mem_algebraMap_eq FunctionField
    (show IntegralRing⁰ ≤ nonZeroDivisors IntegralRing from le_rfl)]
  rfl

/-- Multiplier-inverse membership can be checked only on integral
representatives of the contraction.  No invertibility hypothesis on the
contraction is used. -/
theorem mem_inv_contractedFractional_iff
    {J : Ideal RationalRing}
    (hC :
      N13IntegralFractionalHull.contractedFractional J ≠ 0)
    {x : FunctionField} :
    x ∈
        (N13IntegralFractionalHull.contractedFractional J)⁻¹ ↔
      ∀ a : IntegralRing,
        N13IntegralFractionalHull.integralToRational a ∈ J →
          ∃ b : IntegralRing,
            algebraMap IntegralRing FunctionField b =
              x * algebraMap IntegralRing FunctionField a := by
  constructor
  · intro hx a ha
    have hprod :
        x * algebraMap IntegralRing FunctionField a ∈
          (1 : IntegralFractionalIdeal) :=
      (FractionalIdeal.mem_inv_iff hC).mp hx
        (algebraMap IntegralRing FunctionField a)
        ((algebraMap_mem_contractedFractional_iff a).mpr ha)
    exact
      (FractionalIdeal.mem_one_iff IntegralRing⁰).mp hprod
  · intro hx
    apply (FractionalIdeal.mem_inv_iff hC).mpr
    intro y hy
    obtain ⟨a, ha, rfl⟩ :=
      mem_contractedFractional_iff.mp hy
    exact
      (FractionalIdeal.mem_one_iff IntegralRing⁰).mpr
        (hx a ha)

/-- Every integral function is a multiplier of a nonzero raw contraction. -/
theorem algebraMap_mem_inv_contractedFractional
    {J : Ideal RationalRing}
    (hC :
      N13IntegralFractionalHull.contractedFractional J ≠ 0)
    (b : IntegralRing) :
    algebraMap IntegralRing FunctionField b ∈
      (N13IntegralFractionalHull.contractedFractional J)⁻¹ := by
  apply (mem_inv_contractedFractional_iff hC).mpr
  intro a ha
  exact ⟨b * a, by simp⟩

/-- The ordinary ideal of integral elements whose product with `x` remains
integral. -/
def integralMultiplierIdeal
    (x : FunctionField) : Ideal IntegralRing where
  carrier :=
    {a |
      x * algebraMap IntegralRing FunctionField a ∈
        (1 : IntegralFractionalIdeal)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change
      x * algebraMap IntegralRing FunctionField (a + b) ∈
        ((1 : IntegralFractionalIdeal) :
          Submodule IntegralRing FunctionField)
    have hsum :=
      ((1 : IntegralFractionalIdeal) :
        Submodule IntegralRing FunctionField).add_mem ha hb
    simpa only [map_add, mul_add] using hsum
  smul_mem' := by
    intro r a ha
    change
      x * algebraMap IntegralRing FunctionField (r • a) ∈
        ((1 : IntegralFractionalIdeal) :
          Submodule IntegralRing FunctionField)
    have hsmul :=
      ((1 : IntegralFractionalIdeal) :
        Submodule IntegralRing FunctionField).smul_mem r ha
    simpa only [Algebra.smul_def, map_mul,
      Algebra.algebraMap_self, RingHom.id_apply, mul_assoc, mul_comm,
      mul_left_comm] using hsmul

/-- Inverse membership is equivalent to containment of the contracted
ordinary ideal in the integral multiplier ideal. -/
theorem mem_inv_contractedFractional_iff_le_multiplierIdeal
    {J : Ideal RationalRing}
    (hC :
      N13IntegralFractionalHull.contractedFractional J ≠ 0)
    {x : FunctionField} :
    x ∈
        (N13IntegralFractionalHull.contractedFractional J)⁻¹ ↔
      N13IntegralModelContraction.contractIdeal J ≤
        integralMultiplierIdeal x := by
  constructor
  · intro hx a ha
    exact
      (FractionalIdeal.mem_inv_iff hC).mp hx
        (algebraMap IntegralRing FunctionField a)
        ((algebraMap_mem_contractedFractional_iff a).mpr ha)
  · intro hx
    apply (FractionalIdeal.mem_inv_iff hC).mpr
    intro y hy
    obtain ⟨a, ha, rfl⟩ :=
      mem_contractedFractional_iff.mp hy
    exact hx ha

/-- It is enough to check an inverse multiplier on any explicit spanning
set dominating the contracted ordinary ideal. -/
theorem mem_inv_contractedFractional_of_le_span
    {J : Ideal RationalRing}
    (hC :
      N13IntegralFractionalHull.contractedFractional J ≠ 0)
    {x : FunctionField} {s : Set IntegralRing}
    (hspan :
      N13IntegralModelContraction.contractIdeal J ≤ Ideal.span s)
    (hgen :
      ∀ a ∈ s,
        x * algebraMap IntegralRing FunctionField a ∈
          (1 : IntegralFractionalIdeal)) :
    x ∈
      (N13IntegralFractionalHull.contractedFractional J)⁻¹ := by
  apply
    (mem_inv_contractedFractional_iff_le_multiplierIdeal hC).mpr
  exact hspan.trans (Ideal.span_le.mpr hgen)

end

end MazurProof.N13ContractedFractionalMembership
