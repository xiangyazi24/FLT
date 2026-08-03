import FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient
import FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness
import FLT.Assumptions.MazurProof.N13QuotientReduction
import FLT.Assumptions.MazurProof.N13SpecialGraphQuotientBasis
import FLT.Assumptions.MazurProof.N13TwoFiberNoEscape
import FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis

/-!
# Two-fibre bases over arbitrary quadratic N13 special graphs

The no-escape theorem only needs the literal basis `{1,x}` on the generic
and special quotients.  The special basis is available for every monic
quadratic generalized Mumford graph, not merely the fixed base graph.

Therefore, whenever the canonical contraction maps to any such special
graph ideal, `{1,x}` is already a basis of the integral quotient.
-/

open Polynomial
open Module

namespace MazurProof.N13TwoFiberGraphBasis

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

abbrev SpecialData : Type :=
  N13GoodCoordinateRingTwo.SemiMumford

def specialIdeal (E : SpecialData) : Ideal SpecialRing :=
  N13GoodCoordinateRingTwo.mumfordIdeal E.u E.v

abbrev SpecialQuotient (E : SpecialData) : Type :=
  SpecialRing ⧸ specialIdeal E

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13GeneralizedMumfordReduction.reduceBase.toAlgebra

local instance baseSpecialQuotientTower (E : SpecialData) :
    IsScalarTower R₂ k (SpecialQuotient E) :=
  IsScalarTower.of_algebraMap_eq
    (R := R₂) (S := k) (A := SpecialQuotient E)
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

/-- The descended reduction map respects the composite scalar structure
on every special graph quotient. -/
theorem specialQuotientMap_comp_algebraMap
    (E : SpecialData)
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        specialIdeal E) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I (specialIdeal E) hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k (SpecialQuotient E)).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk (specialIdeal E)
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk (specialIdeal E)
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

/-- Reduction carries the integral class of `x` to the second vector in
the special graph quotient basis. -/
theorem specialQuotientMap_x_eq_basis_one
    (E : SpecialData)
    (hEdeg : E.u.natDegree = 2)
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        specialIdeal E) :
    N13QuotientReduction.reduceCoordinateQuotient
        I (specialIdeal E) hmap
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) =
      N13SpecialGraphQuotientBasis.quotientBasis E hEdeg 1 := by
  rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
    N13CanonicalContractionQuotient.integralX,
    N13GeneralizedMumfordReduction.reduce_xClass,
    N13SpecialGraphQuotientBasis.quotientBasis_one]
  simp [N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase,
    specialIdeal]
  rfl

/-- If the generic and special graph quotients are both quadratic, the
integral quotient has the literal basis `{1,x}`. -/
theorem exists_contractQuotient_basis
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (E : SpecialData)
    (hEdeg : E.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        specialIdeal E) :
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
      (B := B) (C := SpecialQuotient E) (G := G)
      (π := (2 : R₂))
      (hπ := PadicInt.irreducible_p)
      (g := N13QuotientReduction.reduceCoordinateQuotient
        I (specialIdeal E) hmap)
      (hfactorSpecial :=
        specialQuotientMap_comp_algebraMap E I hmap)
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
      (bC := N13SpecialGraphQuotientBasis.quotientBasis E hEdeg)
      (hg₀ := by
        rw [map_one]
        change
          (1 :
              N13GoodCoordinateRingTwo.CoordinateRing ⧸
                N13GoodCoordinateRingTwo.mumfordIdeal E.u E.v) =
            N13SpecialGraphQuotientBasis.quotientBasis E hEdeg 0
        exact
          (N13SpecialGraphQuotientBasis.quotientBasis_zero
            E hEdeg).symm)
      (hg₁ := specialQuotientMap_x_eq_basis_one
        E hEdeg I hmap)
      (bG := SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)
      (hq₀ :=
        N13CanonicalContractionQuotient.genericQuotientMap_one_eq_basis_zero
          D hdeg)
      (hq₁ :=
        N13CanonicalContractionQuotient.genericQuotientMap_x_eq_basis_one
          D hdeg)

end

end MazurProof.N13TwoFiberGraphBasis
