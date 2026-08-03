import FLT.Assumptions.MazurProof.N13IntegralGraphSpread
import FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery
import FLT.Assumptions.MazurProof.N13TwoFiberGraphBasis

/-!
# Integral N13 spreads over arbitrary quadratic special graphs

Assume that the canonical contraction of a quadratic generic Mumford graph
maps to the graph ideal of any quadratic special Mumford datum.  Both
quotients then have the literal basis `{1,x}`.  Two-fibre no-escape lifts
that basis integrally, rank-two graph recovery reconstructs an integral
semigraph, and the global Jacobian dual frame proves invertibility.

No fixed special Picard class, contracted factor frame, or local
factoriality theorem is used.
-/

namespace MazurProof.N13ArbitrarySpecialGraphSpread

noncomputable section

abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13TwoFiberGraphBasis.Model

abbrev SpecialData : Type :=
  N13TwoFiberGraphBasis.SpecialData

abbrev IntegralSemiMumford : Type :=
  N13RankTwoSemiGraphRecovery.SemiMumford₂

/-- Intrinsic remaining properness datum for a quadratic generic graph:
its canonical contraction has some quadratic special Mumford graph as
special fibre. -/
structure SpecialGraphModel
    (D : SexticMumford.SemiMumford Model) where
  special : SpecialData
  special_degree : special.u.natDegree = 2
  map_contract :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)) =
      N13TwoFiberGraphBasis.specialIdeal special

/-- Two matching quadratic fibres recover a literal integral semigraph. -/
theorem exists_integral_semiGraph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (E : SpecialData)
    (hEdeg : E.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13TwoFiberGraphBasis.specialIdeal E) :
    ∃ F : IntegralSemiMumford,
      F.u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal F.u F.v := by
  obtain ⟨b, hb⟩ :=
    N13TwoFiberGraphBasis.exists_contractQuotient_basis
      D hdeg E hEdeg hmap
  exact
    N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
      D b hb

/-- A generic quadratic graph whose contraction has any quadratic special
graph fibre has an invertible canonical divisorial spread. -/
theorem divisorialHull_graphIdeal_isUnit
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (E : SpecialData)
    (hEdeg : E.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13TwoFiberGraphBasis.specialIdeal E) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D)) := by
  obtain ⟨F, _hFdeg, hcontract⟩ :=
    exists_integral_semiGraph D hdeg E hEdeg hmap
  exact
    N13IntegralGraphSpread.divisorialHull_isUnit_of_contractIdeal_eq_semiGraph
      (N13CanonicalContractionQuotient.graphIdeal D)
      F hcontract

/-- The semantic properness package above is exactly enough for
invertibility; no choice of a fixed special class remains. -/
theorem SpecialGraphModel.divisorialHull_graphIdeal_isUnit
    {D : SexticMumford.SemiMumford Model}
    (M : SpecialGraphModel D)
    (hdeg : D.u.natDegree = 2) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D)) :=
  N13ArbitrarySpecialGraphSpread.divisorialHull_graphIdeal_isUnit
    D hdeg M.special M.special_degree M.map_contract

end

end MazurProof.N13ArbitrarySpecialGraphSpread
