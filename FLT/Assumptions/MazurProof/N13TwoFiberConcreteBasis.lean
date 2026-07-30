import FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient
import FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness
import FLT.Assumptions.MazurProof.N13SpecialQuotientBasis
import FLT.Assumptions.MazurProof.N13TwoFiberNoEscape

/-!
# The concrete two-fibre basis for an N13 contraction

Assume only the remaining representative-level statement that the canonical
contraction reduces to the fixed special graph ideal.  The generic and special
quotient frames are then both literally `{1,x}`.  The two-fibre no-escape
theorem therefore makes the same pair an integral basis, without any prior
finiteness assumption.
-/

open Polynomial
open Module

namespace MazurProof.N13TwoFiberConcreteBasis

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev k : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

abbrev SpecialQuotient : Type :=
  SpecialRing ⧸ N13SpecialQuotientBasis.specialIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13GeneralizedMumfordReduction.reduceBase.toAlgebra

local instance baseSpecialQuotientTower :
    IsScalarTower R₂ k SpecialQuotient :=
  IsScalarTower.of_algebraMap_eq
    (R := R₂) (S := k) (A := SpecialQuotient)
    fun _ => rfl

theorem ker_baseSpecial :
    RingHom.ker (algebraMap R₂ k) =
      Ideal.span ({(2 : R₂)} : Set R₂) := by
  change RingHom.ker PadicInt.toZMod =
    Ideal.span ({(2 : R₂)} : Set R₂)
  rw [PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  congr 2

@[simp] theorem baseSpecial_two :
    algebraMap R₂ k (2 : R₂) = 0 :=
  N13GeneralizedMumfordReduction.reduceBase_two

/-- The descended reduction map respects the chosen composite
`R₂ → k → SpecialQuotient` scalar structure. -/
theorem specialQuotientMap_comp_algebraMap
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k SpecialQuotient).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (algebraMap k SpecialRing
          (N13GeneralizedMumfordReduction.reduceBase r))
  congr 1
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C r)) =
      N13GoodCoordinateRingTwo.xClass
        (C (N13GeneralizedMumfordReduction.reduceBase r))
  rw [N13GeneralizedMumfordReduction.reduce_xClass]
  simp [N13GeneralizedMumfordReduction.reducePoly]

/-- Reduction sends the integral class of `x` to the first fixed special
basis vector. -/
theorem specialQuotientMap_x_eq_basis_one
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) =
      N13SpecialQuotientBasis.quotientBasis 1 := by
  rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
    N13CanonicalContractionQuotient.integralX,
    N13GeneralizedMumfordReduction.reduce_xClass,
    N13SpecialQuotientBasis.quotientBasis_one]
  simp [N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]

/-- Once the canonical contraction has the fixed literal special fibre, the
integral quotient has the literal basis `{1,x}`. -/
theorem exists_contractQuotient_basis
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
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
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let G :=
    RationalRing ⧸
      N13CanonicalContractionQuotient.graphIdeal D
  letI : Module.IsTorsionFree R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_isTorsionFree
      (N13CanonicalContractionQuotient.graphIdeal D)
  exact
    N13TwoFiberNoEscape.exists_basis_of_two_fibres
      (R := R₂) (k := k) (K := Q₂)
      (B := B) (C := SpecialQuotient) (G := G)
      (π := (2 : R₂))
      (hπ := PadicInt.irreducible_p)
      (g := N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap)
      (hfactorSpecial :=
        specialQuotientMap_comp_algebraMap I hmap)
      (hπ_zero := baseSpecial_two)
      (hkerSpecial := ker_baseSpecial)
      (q := N13CanonicalContractionQuotient.genericQuotientMap
        (N13CanonicalContractionQuotient.graphIdeal D))
      (hfactorGeneric :=
        N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
          (N13CanonicalContractionQuotient.graphIdeal D))
      (hq :=
        N13CanonicalContractionQuotient.genericQuotientMap_injective
          (N13CanonicalContractionQuotient.graphIdeal D))
      (e₀ := 1)
      (e₁ := Ideal.Quotient.mk I
        N13CanonicalContractionQuotient.integralX)
      (bC := N13SpecialQuotientBasis.quotientBasis)
      (hg₀ := by simp)
      (hg₁ := specialQuotientMap_x_eq_basis_one I hmap)
      (bG := SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)
      (hq₀ :=
        N13CanonicalContractionQuotient.genericQuotientMap_one_eq_basis_zero
          D hdeg)
      (hq₁ :=
        N13CanonicalContractionQuotient.genericQuotientMap_x_eq_basis_one
          D hdeg)

end

end MazurProof.N13TwoFiberConcreteBasis
