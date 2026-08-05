import FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread

/-!
# Uniform fractional spreads for linear N13 graphs

An integral degree-one point is represented by its canonical divisorial
hull.  A point escaping the affine integral chart instead supplies an
explicit invertible two-chart line.  Both branches extend to the same
selected rational Mumford ideal.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13DegreeOneFractionalSpread

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The quadratic two-adic coefficient field used by the N13 model. -/
abbrev Q₂ : Type :=
  N13EscapingDegreeOneSpread.Q₂

/-- The N13 Mumford model over the quadratic two-adic coefficient field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13EscapingDegreeOneSpread.Model

/-- The rational N13 Picard group used by the selected graph construction. -/
abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- The integral two-adic coordinate ring from which spreads are extended. -/
abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

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

/-! ## Unifying integral and escaping points

The affine-point analysis already isolates the only possible failure of an
integral degree-one graph: its rational point can escape to the infinity
chart.  The proper two-chart construction supplies an invertible affine
closure in precisely that case.  The following theorem identifies both
branches after extension to the rational coordinate ring.
-/

/-- Every Padé-selected degree-one graph has an invertible integral
fractional spread whose generic fibre is exactly the selected graph ideal.

For an integral point, the witness is the canonical divisorial hull and its
generic fibre is recovered by divisorial extension.  For an escaping point,
the witness is the affine half of the explicit invertible two-chart line;
the previously proved generic map identity identifies it with the same
Mumford graph.  This supplies the uniform degree-one input needed beside the
quadratic spread in the eventual N13 classifier. -/
theorem selectedLinear_has_integralFractionalSpread
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 1) :
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
  let J : Ideal RationalRing :=
    SexticMumford.mumfordIdeal Model D.u D.v
  have hJunit : IsUnit (J : RationalFractionalIdeal) := by
    simpa [J] using
      (SexticMumford.mumfordIdealUnit Model D.toSemi).isUnit
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hzero : (J : RationalFractionalIdeal) = 0 := by
      rw [hbot]
      rfl
    exact hJunit.ne_zero hzero
  rcases
      N13EscapingDegreeOneSpread.selectedGraph_isUnit_or_has_pointLine
        P hdeg with
    hdiv | ⟨L, hLmap⟩
  · refine
      ⟨N13IntegralFractionalHull.divisorialHull J, ?_, ?_⟩
    · simpa [J, D] using hdiv
    · simpa [J, D] using
        (N13IntegralFractionalHull.extendFractional_divisorialHull_eq
          hJne hJunit)
  · refine
      ⟨(L.affineIdeal : IntegralFractionalIdeal),
        L.affine_isUnit, ?_⟩
    have hLmap' :
        Ideal.map
            N13IntegralFractionalHull.integralToRational
            L.affineIdeal =
          J := by
      simpa [N13IntegralFractionalHull.integralToRational,
        J, D] using hLmap
    calc
      N13IntegralFractionalHull.extendFractional
            (L.affineIdeal : IntegralFractionalIdeal) =
          ((Ideal.map
              N13IntegralFractionalHull.integralToRational
              L.affineIdeal : Ideal RationalRing) :
            RationalFractionalIdeal) := by
        rw [N13IntegralFractionalHull.extendFractional,
          FractionalIdeal.extendedHom'_apply,
          FractionalIdeal.extended_coeIdeal_eq_map]
      _ = (J : RationalFractionalIdeal) := by
        exact congrArg
          (fun I : Ideal RationalRing =>
            (I : RationalFractionalIdeal)) hLmap'
      _ = _ := by rfl

end

end MazurProof.N13DegreeOneFractionalSpread
