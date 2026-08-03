import FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery
import FLT.Assumptions.MazurProof.N13IntegralGraphSpread

/-!
# Integral spreads recovered from the N13 special graph

The two-fibre recovery theorem turns a balanced generic quadratic graph
whose canonical contraction has the fixed special fibre into a literal
smooth integral Mumford graph.  The global Jacobian dual frame then makes
that contraction invertible.

Thus, after the fixed mapped-special-ideal equality, no additional
contracted-frame or local-factoriality input is needed.
-/

namespace MazurProof.N13RecoveredGraphSpread

noncomputable section

abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model

/-- A balanced quadratic graph with the fixed literal special fibre has an
invertible canonical divisorial spread. -/
theorem divisorialHull_graphIdeal_isUnit
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D)) := by
  obtain ⟨E, _hEdeg, hcontract⟩ :=
    N13ConcreteGraphRecovery.exists_integral_smoothGraph
      D hdeg hmap
  exact
    N13IntegralGraphSpread.divisorialHull_isUnit_of_contractIdeal_eq
      (N13CanonicalContractionQuotient.graphIdeal D) E
      (by
        simpa [N13IntegralGraphContraction.graphIdeal] using
          hcontract)

end

end MazurProof.N13RecoveredGraphSpread
