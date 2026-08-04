import FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis
import FLT.Assumptions.MazurProof.N13IntegralGraphJacobian
import FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery
import FLT.Assumptions.MazurProof.N13VerticalGraphJacobian

open Module
open Polynomial
open scoped nonZeroDivisors

/-!
# Invertibility of finite quadratic N13 contractions

A finite quadratic contraction admits a literal integral basis `{1,x}` or
`{1,y}`.  The first basis recovers a horizontal integral semigraph; the
second recovers a vertical graph.  The two structural Jacobian frames prove
invertibility in the respective cases.
-/

namespace MazurProof.N13FiniteContractIdealInvertible

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type := N13IntegralGraphJacobian.FunctionField
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev Model : SexticMumford.Model N13IntegralModelContraction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

theorem contractIdeal_isUnit_of_finite_quadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    IsUnit
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) := by
  rcases
      N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
        D hdeg hfinite with hx | hy
  · obtain ⟨b, hb⟩ := hx
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13TwoFiberNoEscape.pairFamily
            1
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13CanonicalContractionQuotient.integralX) := by
      simpa [N13FiniteFlatBasisLift.oneX,
        N13TwoFiberNoEscape.pairFamily] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
        D b hb'
    rw [hI]
    exact N13IntegralGraphJacobian.mumfordIdeal_isUnit E
  · obtain ⟨b, hb⟩ := hy
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13FiniteFlatBasisLift.oneX
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13ConcreteGraphRecovery.integralY) := by
      simpa [N13ContractQuotientXYBasis.integralY,
        N13ConcreteGraphRecovery.integralY] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
        D b hb'
    rw [hI]
    exact N13VerticalGraphJacobian.verticalIdeal_isUnit E

/-- A finite quadratic contraction therefore has an invertible canonical
divisorial hull. -/
theorem divisorialHull_graphIdeal_isUnit_of_finite_quadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D)) := by
  have hI :=
    contractIdeal_isUnit_of_finite_quadratic D hdeg hfinite
  rw [N13IntegralFractionalHull.divisorialHull]
  have hmul :
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) *
          ((N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D) :
            Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹ =
        1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mpr hI
  have hinvinv :
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹⁻¹ =
        ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) :=
    (FractionalIdeal.right_inverse_eq
      FunctionField
      (((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹)
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)
      (by simpa [mul_comm] using hmul)).symm
  change
    IsUnit
      (((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal)⁻¹⁻¹)
  rw [hinvinv]
  exact hI

end

end MazurProof.N13FiniteContractIdealInvertible
