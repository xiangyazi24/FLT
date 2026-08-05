import FLT.Assumptions.MazurProof.N13DegreeOneFractionalSpread
import FLT.Assumptions.MazurProof.N13QuadraticFractionalSpread

/-!
# Integral fractional spreads for every selected N13 graph

The Padé half-root construction produces a nonzero horizontal graph
polynomial of degree at most two.  The degree-zero graph is the unit ideal,
while the linear and quadratic cases are supplied by their proper two-chart
analyses.  This file joins those three cases into the single spread theorem
needed by the reduction classifier.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13LowDegreeFractionalSpread

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The quadratic two-adic coefficient field used by the N13 model. -/
abbrev Q₂ : Type :=
  N13InfinityBaseChange.Q₂

/-- The N13 Mumford model over the quadratic two-adic coefficient field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂

/-- The rational N13 Picard group whose elements receive selected graphs. -/
abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- Fractional ideals over the integral two-adic coordinate ring. -/
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

/-- Fractional ideals over the rational two-adic coordinate ring. -/
abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

/-! ## Exhausting the Padé degree bound

The finite half-root data records the uniform degree bound.  Its three
possible natural-number values match the unit, linear-point, and quadratic
spread constructions exactly.
-/

/-- Every Padé-selected N13 graph has an invertible integral fractional
spread whose generic extension is exactly its normalized Mumford graph.

For degree zero, the selected root and both of its orientations are the unit,
so the unit integral ideal has the required generic fibre.  Degree one uses
the affine-or-infinity point-line dichotomy, and degree two uses the
reducible-or-irreducible quadratic dichotomy.  This removes all geometric
case splits from the classifier-facing spread interface. -/
theorem selectedGraph_has_integralFractionalSpread
    (P : G) :
    ∃ H : IntegralFractionalIdeal,
      IsUnit H ∧
        N13IntegralFractionalHull.extendFractional H =
          (SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v :
            RationalFractionalIdeal) := by
  have hdegree :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree ≤ 2 :=
    (N13MumfordFullKummerTwoSurjective.constructedHalfData
      P).finite.graphU_degree_le_two
  have hcases :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 0 ∨
        (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1 ∨
          (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · refine
      ⟨N13ConstructedHalfIntegralSpread.degreeZeroIntegralRootHull,
        N13ConstructedHalfIntegralSpread.degreeZeroIntegralRootHull_isUnit,
        ?_⟩
    have hgraph :
        (1 : RationalFractionalIdeal) =
          (SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v :
            RationalFractionalIdeal) := by
      simpa [
        N13ConstructedHalfIntegralSpread.twoAdicIdealRoot_eq_one_of_graphU_natDegree_eq_zero
          P hzero] using
        (N13ConstructedHalfIntegralSpread.twoAdicIdealRoot_normalizedGraph_eq
          P)
    calc
      N13IntegralFractionalHull.extendFractional
          N13ConstructedHalfIntegralSpread.degreeZeroIntegralRootHull =
        (N13ConstructedHalfIntegralSpread.twoAdicIdealRoot P :
          RationalFractionalIdeal) :=
            N13ConstructedHalfIntegralSpread.extend_degreeZeroIntegralRootHull
              P hzero
      _ = 1 := by
        rw [
          N13ConstructedHalfIntegralSpread.twoAdicIdealRoot_eq_one_of_graphU_natDegree_eq_zero
            P hzero]
        rfl
      _ = _ := hgraph
  · exact
      N13DegreeOneFractionalSpread.selectedLinear_has_integralFractionalSpread
        P hone
  · exact
      N13QuadraticFractionalSpread.selectedQuadratic_has_integralFractionalSpread
        P htwo

end

end MazurProof.N13LowDegreeFractionalSpread
