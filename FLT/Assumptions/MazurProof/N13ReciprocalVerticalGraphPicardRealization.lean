import FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphContraction
import FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
import FLT.Assumptions.MazurProof.N13ReciprocalGraphPicardRealization

/-!
# Picard realization of reciprocal vertical N13 graphs

The direct reciprocal kernel may recover its rank-two integral quotient in
the vertical basis `{1,v}` rather than the horizontal basis `{1,t}`.  Its
weighted affine closure still has the exact original generic Mumford ideal.
The vertical special-restriction theorem supplies a literal effective
degree-two divisor for either reduced slope `c̄=0` or `c̄=1`.

This file packages those comparisons as two-fibre Picard data and then joins
the horizontal and vertical reciprocal branches.
-/

open Polynomial

namespace MazurProof.N13ReciprocalVerticalGraphPicardRealization

noncomputable section

/-- A recovered vertical reciprocal graph realizes the original generic
quadratic class and a literal effective degree-two special divisor. -/
theorem verticalGraph_exists_data
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹))
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D := by
  let u :=
    N13ReciprocalQuadraticReflection.integralReciprocal a b
  have hu : u.Monic :=
    N13ReciprocalQuadraticReflection.integralReciprocal_monic a b
  have huDegree : u.natDegree = 2 :=
    N13ReciprocalQuadraticReflection.integralReciprocal_natDegree a b
  have huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal := by
    rw [← hI]
    exact
      N13ReciprocalInfinityContraction.reciprocal_mem_integralInfinityIdeal
        D hdeg h0 a b hm
  let L :=
    N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
      u E hu huDegree hmDegree huMem
  obtain ⟨Δ, hrestrict⟩ :=
    N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
      u E hu huDegree hmDegree huMem
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
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v := by
    change
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E) =
        N13ReciprocalInfinityContraction.genericIdeal D
    rw [←
        N13IntegralInfinityVerticalGraphContraction.contractIdeal_eq_affineIdeal
          D hdeg h0 u E hu huDegree hmDegree huMem hI,
      N13IntegralModelContraction.map_contractIdeal]
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

/-- The reciprocal direct-kernel construction admits complete two-fibre
Picard data regardless of whether rank-two recovery chooses the horizontal
or vertical infinity-chart basis. -/
theorem exists_data
    (D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D := by
  rcases
      N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
        D hdeg h0 a b hm with
    hhorizontal | ⟨E, hmDegree, hI⟩
  · obtain ⟨E⟩ := hhorizontal
    exact
      N13ReciprocalGraphPicardRealization.ReciprocalGraphClosure.exists_data
        E hdeg h0 hm
  · exact
      verticalGraph_exists_data
        hdeg h0 hm E hmDegree hI

end

end MazurProof.N13ReciprocalVerticalGraphPicardRealization
