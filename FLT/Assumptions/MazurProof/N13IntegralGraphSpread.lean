import FLT.Assumptions.MazurProof.N13IntegralGraphContraction
import FLT.Assumptions.MazurProof.N13IntegralGraphJacobian

/-!
# Invertible integral spreads of N13 Mumford graphs

A smooth integral generalized Mumford graph already gives an invertible
fractional ideal on the integral affine model: this is the explicit global
Jacobian dual-frame theorem.  Exact graph contraction then identifies the
canonical contraction of its generic sextic graph with that same integral
ideal.

Consequently the divisorial-hull construction makes no change at all on an
integral graph.  This is the representative-level adapter needed by the
proper-spread construction; it uses neither local factoriality nor a special
fibre classification.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphSpread

noncomputable section

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev SmoothMumford₂ : Type :=
  N13IntegralGraphContraction.SmoothMumford₂

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Exact contraction of a smooth integral graph is already an invertible
fractional ideal on the integral affine model. -/
theorem contractedFractional_sexticIdeal_isUnit
    (D : SmoothMumford₂) (nInf : ℤ) :
    IsUnit
      (N13IntegralFractionalHull.contractedFractional
        (N13IntegralGraphContraction.sexticIdeal D nInf)) := by
  rw [N13IntegralGraphContraction.contractedFractional_sexticIdeal]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

/-- Double multiplier inverse fixes an invertible integral fractional
ideal. -/
private theorem inv_inv_eq_of_isUnit
    {I : IntegralFractionalIdeal} (hI : IsUnit I) :
    I⁻¹⁻¹ = I := by
  have hmul : I * I⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mpr hI
  exact
    (FractionalIdeal.right_inverse_eq
      FunctionField I⁻¹ I
        (by simpa [mul_comm] using hmul)).symm

/-- Any generic ideal whose canonical contraction is an integral graph has
that graph itself as its divisorial hull. -/
theorem divisorialHull_eq_graphIdeal_of_contractIdeal_eq
    (J : Ideal RationalRing)
    (D : SmoothMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13IntegralGraphContraction.graphIdeal D) :
    N13IntegralFractionalHull.divisorialHull J =
      (N13IntegralGraphContraction.graphIdeal D :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralFractionalHull.contractedFractional,
    hcontract]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford)

/-- Thus exact recovery of an integral graph is already enough to prove
invertibility of the canonical divisorial spread. -/
theorem divisorialHull_isUnit_of_contractIdeal_eq
    (J : Ideal RationalRing)
    (D : SmoothMumford₂)
    (hcontract :
      N13IntegralModelContraction.contractIdeal J =
        N13IntegralGraphContraction.graphIdeal D) :
    IsUnit (N13IntegralFractionalHull.divisorialHull J) := by
  rw [divisorialHull_eq_graphIdeal_of_contractIdeal_eq J D hcontract]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

/-- The divisorial hull of the canonical contraction of an integral graph
is literally the original integral graph fractional ideal. -/
theorem divisorialHull_sexticIdeal_eq_graphIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticIdeal D nInf) =
      (N13IntegralGraphContraction.graphIdeal D :
        IntegralFractionalIdeal) := by
  rw [N13IntegralFractionalHull.divisorialHull,
    N13IntegralGraphContraction.contractedFractional_sexticIdeal]
  exact inv_inv_eq_of_isUnit
    (N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford)

/-- Every smooth integral Mumford graph therefore supplies an honest
invertible integral spread of its generic sextic graph. -/
theorem divisorialHull_sexticIdeal_isUnit
    (D : SmoothMumford₂) (nInf : ℤ) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13IntegralGraphContraction.sexticIdeal D nInf)) := by
  rw [divisorialHull_sexticIdeal_eq_graphIdeal]
  exact
    N13IntegralGraphJacobian.mumfordIdeal_isUnit
      D.toSemiMumford

end

end MazurProof.N13IntegralGraphSpread
