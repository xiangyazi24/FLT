import FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction
import FLT.Assumptions.MazurProof.N13ReciprocalVerticalGraphPicardRealization
import FLT.Assumptions.MazurProof.N13SplitQuadraticPicardRealization

/-!
# Picard realization of every quadratic N13 graph

The finite irreducible branch now has a literal special divisor, while the
reciprocal branch is complete for both horizontal and vertical rank-two
recovery.  Combining those two cases gives complete two-fibre Picard data
for every irreducible quadratic Mumford representative.

A nonirreducible monic quadratic factors into two linear terms.  Distinct
roots use the existing secant realization and a repeated root uses the
existing tangent realization.  Thus every balanced quadratic representative
has exact generic raw data, its standard oriented generic Picard class, and
the canonical two-chart ideals of a literal effective special divisor.
-/

open Polynomial

namespace MazurProof.N13QuadraticPicardRealization

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two-adic coefficient field. -/
abbrev Q₂ :=
  N13TwoChartPicardRealization.Q₂

/-- The good sextic N13 model. -/
abbrev Model :=
  N13TwoChartPicardRealization.Model

/-- The proper line obtained from a finite quadratic graph is vertically
saturated on the affine chart.  Its affine ideal is definitionally the
canonical contraction of the generic Mumford graph. -/
theorem finiteQuadraticTwoChartLine_affineVerticallySaturated
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite N13FiniteAffineTwoChart.R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
        D.toSemi hdeg hfinite) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_contractIdeal
      _ (N13CanonicalContractionQuotient.graphIdeal D.toSemi)
  rfl

/-- A finite irreducible quadratic contraction yields complete two-fibre
Picard data. -/
theorem exists_data_of_finite
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite N13FiniteAffineTwoChart.R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D := by
  let L :=
    N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
      D.toSemi hdeg hfinite
  obtain ⟨Δ, hrestrict⟩ :=
    N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
        D.toSemi hdeg hfinite
  have haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal :=
    congrArg (fun C => C.affineIdeal) hrestrict
  have hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal :=
    congrArg (fun C => C.infinityIdeal) hrestrict
  have hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
    exact
      N13FiniteAffineTwoChart.map_finiteQuadraticTwoChartLine_affineIdeal
          D.toSemi hdeg hfinite
  let R :=
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization
      D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
          D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
          D L Δ haffine hinfinity hmap

/-- Every irreducible quadratic Mumford representative has complete
two-fibre Picard data. -/
theorem exists_data_of_irreducible
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
          D hdeg hirr with
    hfinite | ⟨h0, a, b, hm⟩
  · exact exists_data_of_finite D hdeg hfinite
  · exact
      N13ReciprocalVerticalGraphPicardRealization.exists_data
        D hdeg h0 a b hm

/-- Every balanced quadratic Mumford representative has complete two-fibre
Picard data, with split, tangent, finite irreducible, and reciprocal
irreducible cases all represented by literal special divisors. -/
theorem exists_data
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D := by
  by_cases hirr : Irreducible D.u
  · exact exists_data_of_irreducible D hdeg hirr
  obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
    (D.u_monic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp
      hirr
  let x₁ : Q₂ := -c₁
  let x₂ : Q₂ := -c₂
  have hfactor :
      D.u = (X - C x₁) * (X - C x₂) := by
    have hc₂ : D.u.coeff 2 = 1 := by
      calc
        D.u.coeff 2 = D.u.coeff D.u.natDegree :=
          congrArg D.u.coeff hdeg.symm
        _ = 1 := D.u_monic.coeff_natDegree
    simp only [x₁, x₂, C_neg, sub_neg_eq_add]
    rw [D.u.as_sum_range_C_mul_X_pow, hdeg,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc₂, hc₀, hc₁, C_mul, C_add, C_1]
    ring
  by_cases hneq : x₁ ≠ x₂
  · exact
      N13SplitQuadraticPicardRealization.exists_data_of_distinct_split
        D hdeg x₁ x₂ hfactor hneq
  · have heq : x₂ = x₁ := by
      apply not_ne_iff.mp
      exact fun h ↦ hneq h.symm
    have hfactorSquare :
        D.u = (X - C x₁) ^ 2 := by
      rw [heq] at hfactor
      simpa only [pow_two] using hfactor
    exact
      N13SplitQuadraticPicardRealization.exists_data_of_repeated_root
        D x₁ hfactorSquare

end

end MazurProof.N13QuadraticPicardRealization
