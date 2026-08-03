import FLT.Assumptions.MazurProof.N13IntegralCurveProperties
import FLT.Assumptions.MazurProof.N13ClosedFiberCharts

/-!
# Principal Cartier equations for the N13 closed fibre

On each ordinary chart, the closed fibre is cut out by the image of `2`.
That element is regular because both chart rings are domains and the
coefficient embeddings are injective.  The existing reduction maps are
surjective with precisely this principal kernel.

This is a project-specific effective-Cartier interface, avoiding dependence
on divisor APIs not present at the pinned Mathlib revision.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13VerticalCartierCharts

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

universe u v

/-- Local algebraic data for a principal effective Cartier closed fibre. -/
structure PrincipalChartData
    (A : Type u) (A₀ : Type v)
    [CommRing A] [CommRing A₀] where
  parameter : A
  parameter_regular : parameter ∈ nonZeroDivisors A
  reduction : A →+* A₀
  reduction_surjective : Function.Surjective reduction
  reduction_ker :
    RingHom.ker reduction =
      Ideal.span ({parameter} : Set A)

namespace PrincipalChartData

variable {A : Type u} {A₀ : Type v}
variable [CommRing A] [CommRing A₀]

/-- Reduction identifies the Cartier quotient with the special chart. -/
def quotientEquiv (D : PrincipalChartData A A₀) :
    A ⧸ Ideal.span ({D.parameter} : Set A) ≃+* A₀ :=
  ClosedFiberAffineCore.quotientEquivOfSurjectiveKerEq
    D.reduction D.reduction_surjective
    (Ideal.span ({D.parameter} : Set A))
    D.reduction_ker

@[simp] theorem quotientEquiv_mk
    (D : PrincipalChartData A A₀) (a : A) :
    D.quotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({D.parameter} : Set A)) a) =
      D.reduction a :=
  ClosedFiberAffineCore.quotientEquivOfSurjectiveKerEq_mk
    D.reduction D.reduction_surjective
    (Ideal.span ({D.parameter} : Set A))
    D.reduction_ker a

end PrincipalChartData

private abbrev R₂ :=
  N13OrdinaryCurveOverlap.R₂

private abbrev Affine :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev SpecialAffine :=
  N13GeneralizedMumfordReduction.SpecialRing

private abbrev Infinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev SpecialInfinity :=
  N13IntegralInfinityReduction.SpecialRing

def affineParameter : Affine :=
  algebraMap R₂ Affine (2 : R₂)

def infinityParameter : Infinity :=
  algebraMap R₂ Infinity (2 : R₂)

theorem affineParameter_ne_zero :
    affineParameter ≠ 0 := by
  change
    N13GeneralizedMumfordIntegral.xClass
        (R := R₂) (C (2 : R₂)) ≠ 0
  intro h
  have h0 := congrArg
    (N13GeneralizedMumfordIntegral.coeff0 (R := R₂)) h
  simp at h0

theorem infinityParameter_ne_zero :
    infinityParameter ≠ 0 := by
  have hC :
      (C (2 : R₂) : N13IntegralInfinityChart.Base) ≠ 0 := by
    exact C_ne_zero.mpr (by norm_num)
  have hmap :
      algebraMap N13IntegralInfinityChart.Base Infinity
          (C (2 : R₂)) ≠ 0 :=
    by
      simpa using
        (FaithfulSMul.algebraMap_injective
          N13IntegralInfinityChart.Base Infinity).ne hC
  change
    AdjoinRoot.of N13IntegralInfinityChart.infinityCurvePoly
        (C (2 : R₂)) ≠ 0
  exact hmap

theorem affineParameter_regular :
    affineParameter ∈ nonZeroDivisors Affine :=
  IsRegular.mem_nonZeroDivisors
    (IsRegular.of_ne_zero affineParameter_ne_zero)

theorem infinityParameter_regular :
    infinityParameter ∈ nonZeroDivisors Infinity :=
  IsRegular.mem_nonZeroDivisors
    (IsRegular.of_ne_zero infinityParameter_ne_zero)

/-- The affine chart with its principal closed-fibre equation. -/
def affineData :
    PrincipalChartData Affine SpecialAffine where
  parameter := affineParameter
  parameter_regular := affineParameter_regular
  reduction :=
    N13GeneralizedMumfordReduction.reduceCoordinate
  reduction_surjective :=
    N13GeneralizedMumfordReduction.reduceCoordinate_surjective
  reduction_ker := by
    simpa [affineParameter] using
      N13GeneralizedMumfordReduction.ker_reduceCoordinate

/-- The infinity chart with its principal closed-fibre equation. -/
def infinityData :
    PrincipalChartData Infinity SpecialInfinity where
  parameter := infinityParameter
  parameter_regular := infinityParameter_regular
  reduction :=
    N13IntegralInfinityReduction.reduceCoordinate
  reduction_surjective :=
    N13IntegralInfinityReduction.reduceCoordinate_surjective
  reduction_ker := by
    simpa [infinityParameter] using
      N13IntegralInfinityReduction.ker_reduceCoordinate

end

end MazurProof.N13VerticalCartierCharts
