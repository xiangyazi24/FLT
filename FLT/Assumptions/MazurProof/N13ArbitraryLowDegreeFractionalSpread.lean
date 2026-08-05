import FLT.Assumptions.MazurProof.N13AllPointAffineSpread
import FLT.Assumptions.MazurProof.N13QuadraticFractionalSpread

/-!
# Integral fractional spreads for arbitrary balanced N13 graphs

A balanced genus-two Mumford representative has horizontal degree at most
two.  Degree zero is the unit graph.  A linear graph is the graph of one
two-adic curve point, and the point's affine or infinity presentation gives
an integral spread.  The quadratic case is the previously completed
reducible/irreducible dichotomy.

Unlike the Padé-selected interface, the theorem here applies directly to
any balanced two-adic Mumford representative.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13ArbitraryLowDegreeFractionalSpread

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The quadratic two-adic coefficient field. -/
abbrev Q₂ : Type :=
  N13InfinityBaseChange.Q₂

/-- The N13 sextic Mumford model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂

/-- The integral affine coordinate ring of the good two-adic model. -/
abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

/-- Its generic sextic coordinate ring. -/
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

/-- The common function field of the integral and generic models. -/
abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

/-- Fractional ideals over the integral two-adic coordinate ring. -/
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

/-- Fractional ideals over the generic sextic coordinate ring. -/
abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

/-- The rational oriented Picard group represented by low-degree graphs. -/
abbrev G : Type :=
  N13LowDegreeKummerHom.G

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-! ## The linear graph as a two-adic point

The infinity coordinate of a balanced Mumford representative does not
affect its affine graph ideal.  Consequently the linear calculation records
only the polynomial generators and does not impose `nInf = 0`.
-/

/-- A monic linear Mumford graph is given by `X - x` and a constant
ordinate `z`, and `(x,z)` lies on the sextic curve. -/
theorem exists_affineGraph_of_natDegree_eq_one
    (D : SexticMumford.Mumford Model)
    (hdegree : D.u.natDegree = 1) :
    ∃ x z : Q₂,
      D.u = X - C x ∧
        D.v = C z ∧
          z ^ 2 = Model.f.eval x := by
  let x : Q₂ := -D.u.coeff 0
  let z : Q₂ := D.v.coeff 0
  have hu :
      D.u = X - C x := by
    rw [D.u_monic.eq_X_add_C hdegree]
    simp [x]
  have huDegree :
      D.u.degree = (1 : WithBot ℕ) := by
    rw [degree_eq_natDegree D.u_monic.ne_zero, hdegree]
    norm_num
  have hvDegree :
      D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree :
      D.v.natDegree = 0 := by
    by_cases hv0 : D.v = 0
    · simp [hv0]
    · have hvlt : D.v.natDegree < 1 := by
        rw [natDegree_lt_iff_degree_lt hv0]
        simpa [huDegree] using hvDegree
      omega
  have hv :
      D.v = C z :=
    eq_C_of_natDegree_eq_zero hvNatDegree
  have hzero :
      (Model.f - D.v ^ 2).eval x = 0 := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    rw [hq, eval_mul, hu]
    simp
  have hcurve :
      z ^ 2 = Model.f.eval x := by
    have hzero' :
        Model.f.eval x - z ^ 2 = 0 := by
      simpa [hv] using hzero
    exact (sub_eq_zero.mp hzero').symm
  exact ⟨x, z, hu, hv, hcurve⟩

/-! ## Uniform spread

The degree-one branch converts the sextic ordinate to the good-model
ordinate before choosing the integral or escaping point spread.  Its map
identity is then transported from ordinary ideals to fractional ideals.
-/

/-- Every balanced two-adic N13 Mumford graph has an invertible integral
fractional spread whose generic extension is exactly its affine graph ideal.

The proof exhausts the intrinsic degree bound of a balanced representative.
It is independent of the Padé half-root construction and hence can be used
for a representative of an arbitrary rational Picard class after two-adic
base change. -/
theorem mumfordGraph_has_integralFractionalSpread
    (D : SexticMumford.Mumford Model) :
    ∃ H : IntegralFractionalIdeal,
      IsUnit H ∧
        N13IntegralFractionalHull.extendFractional H =
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi :
            RationalFractionalIdeal) := by
  have hdegree : D.u.natDegree ≤ 2 :=
    D.deg_u
  have hcases :
      D.u.natDegree = 0 ∨
        D.u.natDegree = 1 ∨
          D.u.natDegree = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · have hu : D.u = 1 :=
      D.u_monic.natDegree_eq_zero.mp hzero
    have hv : D.v = 0 := by
      have hred := D.v_reduced
      have hmod :
          D.v % (1 : Q₂[X]) = 0 :=
        EuclideanDomain.mod_one D.v
      rw [hu, hmod] at hred
      exact hred.symm
    refine ⟨1, isUnit_one, ?_⟩
    rw [map_one]
    change
      (1 : RationalFractionalIdeal) =
        (SexticMumford.mumfordIdeal Model D.u D.v :
          RationalFractionalIdeal)
    rw [hu, hv,
      show SexticMumford.mumfordIdeal Model 1 0 = ⊤ from
        SexticMumford.zero_mumfordIdeal Model]
    rfl
  · obtain ⟨x, z, hu, hv, hcurve⟩ :=
      exists_affineGraph_of_natDegree_eq_one D hone
    let y := N13TwoChartLineTensor.goodY x z
    have hgood :
        N13GoodModelTwo.AffineEquation x y :=
      N13TwoChartLineTensor.goodY_onCurve x z hcurve
    let S :=
      N13AllPointAffineSpread.pointSpread x y hgood
    refine
      ⟨(S.ideal : IntegralFractionalIdeal), S.isUnit, ?_⟩
    have hmap :
        Ideal.map
            N13IntegralFractionalHull.integralToRational
            S.ideal =
          N13CanonicalContractionQuotient.graphIdeal D.toSemi := by
      simpa [N13IntegralFractionalHull.integralToRational,
        N13CanonicalContractionQuotient.graphIdeal,
        hu, hv, y] using S.map_ideal
    calc
      N13IntegralFractionalHull.extendFractional
            (S.ideal : IntegralFractionalIdeal) =
          ((Ideal.map
              N13IntegralFractionalHull.integralToRational
              S.ideal : Ideal RationalRing) :
            RationalFractionalIdeal) := by
        rw [N13IntegralFractionalHull.extendFractional,
          FractionalIdeal.extendedHom'_apply,
          FractionalIdeal.extended_coeIdeal_eq_map]
      _ =
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi :
            RationalFractionalIdeal) := by
        exact congrArg
          (fun I : Ideal RationalRing =>
            (I : RationalFractionalIdeal)) hmap
  · exact
      N13QuadraticFractionalSpread.mumfordGraph_has_integralFractionalSpread
        D htwo

/-! ## The finite graph of an arbitrary rational class

The chosen low-degree representative retains an integer infinity
coordinate.  Resetting that coordinate to zero changes only the oriented
infinity component, not the affine graph ideal.  The following result
therefore constructs the integral affine part for every rational Picard
class; the separate proper infinity correction remains visible rather than
being silently discarded.
-/

/-- The coefficient-extended affine Mumford graph of the chosen rational
low-degree representative. -/
def twoAdicFiniteRepresentative (P : G) :
    SexticMumford.Mumford Model :=
  (N13LowDegreeKummerHom.asMumford
      (N13LowDegreeKummerHom.representative P)).mapCoeffs
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- Every rational Picard class has an invertible integral affine spread
for the finite graph of its chosen low-degree representative.

This theorem deliberately does not identify that affine spread alone with
the full oriented class: the representative's integer infinity coordinate
must still be supplied by a proper infinity-chart line. -/
theorem rationalClassFiniteGraph_has_integralFractionalSpread
    (P : G) :
    ∃ H : IntegralFractionalIdeal,
      IsUnit H ∧
        N13IntegralFractionalHull.extendFractional H =
          (N13CanonicalContractionQuotient.graphIdeal
            (twoAdicFiniteRepresentative P).toSemi :
            RationalFractionalIdeal) :=
  mumfordGraph_has_integralFractionalSpread
    (twoAdicFiniteRepresentative P)

end

end MazurProof.N13ArbitraryLowDegreeFractionalSpread
