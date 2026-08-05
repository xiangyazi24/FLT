import FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread
import FLT.Assumptions.MazurProof.N13QuadraticSpreadDichotomy

/-!
# Uniform fractional spreads for quadratic N13 graphs

The reducible quadratic branches produce an invertible ordinary ideal,
whereas the irreducible branch naturally produces the canonical divisorial
fractional ideal.  This file erases that representational distinction.

Every degree-two Mumford graph receives one invertible integral fractional
ideal whose generic extension is exactly the original graph ideal.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13QuadraticFractionalSpread

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The quadratic two-adic coefficient field used by the N13 model. -/
abbrev Q₂ : Type :=
  N13QuadraticSpreadDichotomy.Q₂

/-- The N13 Mumford model over the quadratic two-adic coefficient field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13QuadraticSpreadDichotomy.Model

/-- The rational N13 Picard group used by the selected graph construction. -/
abbrev G : Type :=
  N13QuadraticSpreadDichotomy.G

/-- The integral two-adic coordinate ring from which spreads are extended. -/
abbrev IntegralRing : Type :=
  N13QuadraticSpreadDichotomy.IntegralRing

/-- The rational two-adic coordinate ring containing the generic graphs. -/
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

/-- The common fraction field of the integral and rational coordinate rings. -/
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

/-- Fractional ideals over the integral two-adic coordinate ring. -/
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

/-- Fractional ideals over the rational two-adic coordinate ring. -/
abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-! ## Unifying the quadratic branches

The quadratic factorization dichotomy produces two representations of the
same arithmetic object.  Reducible polynomials give ordinary integral graph
ideals, while an irreducible polynomial gives the reflexive divisorial hull
of the contracted generic graph.  Passing both representations to fractional
ideals yields one interface for the later spread classifier.
-/

/-- Every quadratic Mumford graph has an invertible integral fractional
spread whose generic fibre is exactly its Mumford graph ideal.

The proof splits the horizontal polynomial into the reducible and irreducible
cases.  In the reducible case the existing ordinary ideal is coerced to a
fractional ideal and its coefficient-extension identity is reused.  In the
irreducible case the canonical divisorial hull is invertible by the completed
finite/reciprocal/vertical analysis, and the divisorial extension theorem
recovers the graph.  This is the uniform degree-two input expected by the
eventual N13 spread classifier. -/
theorem mumfordGraph_has_integralFractionalSpread
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ H : IntegralFractionalIdeal,
      IsUnit H ∧
        N13IntegralFractionalHull.extendFractional H =
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi :
            RationalFractionalIdeal) := by
  rcases
      N13QuadraticSpreadDichotomy.mumfordGraph_has_affineSpread_or_irreducible
        D hdeg with
    hsplit | hirr
  · obtain ⟨J, hJunit, hJmap⟩ := hsplit
    refine ⟨(J : IntegralFractionalIdeal), hJunit, ?_⟩
    have hJmap' :
        Ideal.map
            N13IntegralFractionalHull.integralToRational J =
          N13CanonicalContractionQuotient.graphIdeal D.toSemi := by
      simpa [N13IntegralFractionalHull.integralToRational,
        N13CanonicalContractionQuotient.graphIdeal] using hJmap
    calc
      N13IntegralFractionalHull.extendFractional
            (J : IntegralFractionalIdeal) =
          ((Ideal.map
              N13IntegralFractionalHull.integralToRational J :
                Ideal RationalRing) : RationalFractionalIdeal) := by
        rw [N13IntegralFractionalHull.extendFractional,
          FractionalIdeal.extendedHom'_apply,
          FractionalIdeal.extended_coeIdeal_eq_map]
      _ =
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi :
            RationalFractionalIdeal) := by
        exact congrArg
          (fun I : Ideal RationalRing =>
            (I : RationalFractionalIdeal)) hJmap'
  · let J : Ideal RationalRing :=
      N13CanonicalContractionQuotient.graphIdeal D.toSemi
    have hJunit : IsUnit (J : RationalFractionalIdeal) := by
      exact
        (SexticMumford.mumfordIdealUnit Model D.toSemi).isUnit
    have hJne : J ≠ ⊥ := by
      intro hbot
      have hzero : (J : RationalFractionalIdeal) = 0 := by
        rw [hbot]
        rfl
      exact hJunit.ne_zero hzero
    refine
      ⟨N13IntegralFractionalHull.divisorialHull J,
        N13IrreducibleQuadraticSpread.divisorialHull_isUnit
          D hdeg hirr, ?_⟩
    simpa [J] using
      (N13IntegralFractionalHull.extendFractional_divisorialHull_eq
        hJne hJunit)

/-- The Padé-selected degree-two graph has the same uniform invertible
fractional spread interface.

Monicity shows that coefficient extension from `ℚ` to `ℚ₂` preserves the
horizontal degree.  The theorem therefore specializes the preceding
quadratic construction to the normalized graph selected by the half-root
procedure, providing the classifier-facing statement over the rational
Picard group. -/
theorem selectedQuadratic_has_integralFractionalSpread
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2) :
    ∃ H : IntegralFractionalIdeal,
      IsUnit H ∧
        N13IntegralFractionalHull.extendFractional H =
          (SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v :
            RationalFractionalIdeal) := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  have hDdeg : D.u.natDegree = 2 := by
    change
      ((N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u.map
          N13InfinityBaseChange.ratToQ₂).natDegree = 2
    rw [
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u_monic.natDegree_map]
    exact
      (N13DegreeOneGraphPoint.normalizedGraphMumford_u_natDegree P).trans
        hdeg
  simpa [D, N13CanonicalContractionQuotient.graphIdeal] using
    (mumfordGraph_has_integralFractionalSpread D hDdeg)

end

end MazurProof.N13QuadraticFractionalSpread
