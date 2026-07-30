import FLT.Assumptions.MazurProof.N13IntegralModelContraction
import FLT.Assumptions.MazurProof.N13QuotientReduction
import FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis

/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/

open Polynomial

namespace MazurProof.N13CanonicalContractionQuotient

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient map from a canonical contraction to its generic ideal. -/
def genericQuotientMap (J : Ideal RationalRing) :
    IntegralRing ⧸ N13IntegralModelContraction.contractIdeal J →+*
      RationalRing ⧸ J :=
  N13QuotientReduction.inducedQuotientMap
    N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13IntegralModelContraction.contractIdeal J)
    J
    (N13IntegralModelContraction.map_contractIdeal J)

@[simp] theorem genericQuotientMap_mk
    (J : Ideal RationalRing) (a : IntegralRing) :
    genericQuotientMap J
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal J) a) =
      Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) :=
  rfl

/-- No element is lost when passing from the contracted quotient to the
generic quotient. -/
theorem genericQuotientMap_injective
    (J : Ideal RationalRing) :
    Function.Injective (genericQuotientMap J) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  calc
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) =
        genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a) := rfl
    _ = genericQuotientMap J (z - w) :=
      congrArg (genericQuotientMap J) ha
    _ = genericQuotientMap J z -
        genericQuotientMap J w := map_sub _ z w
    _ = 0 := by rw [hzw, sub_self]

/-- The generic quotient map respects the two-adic coefficient action. -/
theorem genericQuotientMap_comp_algebraMap
    (J : Ideal RationalRing) :
    (genericQuotientMap J).comp
        (algebraMap R₂
          (IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal J)) =
      algebraMap R₂ (RationalRing ⧸ J) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J (algebraMap R₂ RationalRing r)
  congr 1
  change
    N13GoodSexticCoordinateEquiv.toSextic
        (N13IntegralModelContraction.integralToGood
          (algebraMap R₂ IntegralRing r)) =
      algebraMap R₂ RationalRing r
  rw [N13IntegralModelContraction.integralToGood_algebraMap,
    N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
  exact
    (IsScalarTower.algebraMap_apply R₂ Q₂ RationalRing r).symm

/-- The integral affine `x` coordinate. -/
def integralX : IntegralRing :=
  N13GeneralizedMumfordIntegral.xClass (R := R₂) X

@[simp] theorem integralToSextic_integralX :
    N13TwoAdicCoordinateBaseChange.integralToSextic integralX =
      SexticMumford.xClass Model X := by
  simp [integralX,
    N13TwoAdicCoordinateBaseChange.integralToSextic]

/-- The generic graph ideal of sextic Mumford data. -/
abbrev graphIdeal
    (D : SexticMumford.SemiMumford Model) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal Model D.u D.v

/-- The canonical contraction map sends `1` to the zero-th literal generic
basis vector. -/
theorem genericQuotientMap_one_eq_basis_zero
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (1 :
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (graphIdeal D)) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 0 := by
  simp

/-- The canonical contraction map sends the integral class of `x` to the
first literal generic basis vector. -/
theorem genericQuotientMap_x_eq_basis_one
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    genericQuotientMap (graphIdeal D)
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal
            (graphIdeal D))
          integralX) =
      SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg 1 := by
  rw [genericQuotientMap_mk,
    integralToSextic_integralX,
    SexticMumfordQuotientBasis.quotientBasis_one]

end

end MazurProof.N13CanonicalContractionQuotient
