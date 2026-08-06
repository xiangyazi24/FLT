import FLT.Assumptions.MazurProof.N13IntegralInfinityVerticalGraphTwoChart
import FLT.Assumptions.MazurProof.N13SpecialAffineSaturation
import FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph

/-!
# Special restriction of constant vertical infinity graphs

An integral vertical infinity graph is defined by a monic quadratic
`m(v)` and a linear relation `t=a+cv`.  This file treats the branch in
which `c` reduces to zero.  On the special fibre the relation becomes the
constant equation `t=ā`, so the reduced quadratic is forced to be `v²+v`
and the infinity ideal is the principal fibre ideal `(t-ā)`.

The weighted affine closure is not recomputed generator by generator.
Its reflected reciprocal equation makes `x` a unit modulo the ideal, and
this property survives reduction.  The canonical target fibre has the same
property.  Equality of the infinity ideals and compatibility on the overlap
therefore determine the full reduced two-chart pair.
-/

open Polynomial

namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two-adic coefficient ring. -/
abbrev R₂ :=
  N13IntegralInfinityChart.R₂

/-- The special residue field. -/
abbrev K :=
  N13SpecialInfinityChart.K

/-- Integral vertical graph data on the infinity chart. -/
abbrev VerticalGraph :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph

/-- Reduction commutes with evaluation of a polynomial at the infinity
ordinate `v`. -/
theorem reduce_aeval_vClass (p : R₂[X]) :
    N13IntegralInfinityReduction.reduceCoordinate
        (aeval N13IntegralInfinityGraphJacobian.yClass p) =
      aeval N13SpecialInfinityChart.vClass
        (N13IntegralInfinityReduction.reducePoly p) := by
  have h :=
    Polynomial.map_aeval_eq_aeval_map
      (R := R₂)
      (S := N13IntegralInfinityReduction.IntegralRing)
      (T := K)
      (U := N13IntegralInfinityReduction.SpecialRing)
      (φ := N13IntegralInfinityReduction.reduceBase)
      (ψ := N13IntegralInfinityReduction.reduceCoordinate)
      (by
        ext r
        change
          N13IntegralInfinityReduction.specialBaseClass
              (C (N13IntegralInfinityReduction.reduceBase r)) =
            N13IntegralInfinityReduction.reduceCoordinate
              (N13IntegralInfinityReduction.integralBaseClass (C r))
        rw [N13IntegralInfinityReduction.reduce_integralBaseClass]
        simp [N13IntegralInfinityReduction.reducePoly])
      p N13IntegralInfinityGraphJacobian.yClass
  have hv :
      N13IntegralInfinityReduction.reduceCoordinate
          N13IntegralInfinityGraphJacobian.yClass =
        N13SpecialInfinityChart.vClass :=
    N13IntegralInfinityReduction.reduce_vClass
  rw [hv] at h
  simpa only [N13IntegralInfinityReduction.reducePoly_apply] using h

/-- Coefficient reduction sends the integral vertical substitution equation
to the corresponding equation on the special infinity chart. -/
theorem reduce_verticalCurve
    (s : R₂[X]) :
    N13IntegralInfinityReduction.reducePoly
        (N13IntegralInfinityVerticalGraphJacobian.verticalCurve s) =
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
        (N13IntegralInfinityReduction.reducePoly s) := by
  rw [N13IntegralInfinityVerticalGraphJacobian.verticalCurve,
    N13SpecialConstantInfinityVerticalGraph.verticalCurve]
  change
    (X ^ 2 +
          N13IntegralInfinityChart.hBase.comp s * X -
        N13IntegralInfinityChart.rhsBase.comp s).map
          N13IntegralInfinityReduction.reduceBase =
      _
  simp only [Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_comp]
  rw [show
        N13IntegralInfinityChart.hBase.map
            N13IntegralInfinityReduction.reduceBase =
          N13SpecialInfinityChart.hPoly from
        N13IntegralInfinityReduction.reduce_hBase,
      show
        N13IntegralInfinityChart.rhsBase.map
            N13IntegralInfinityReduction.reduceBase =
          N13SpecialInfinityChart.rhsPoly from
        N13IntegralInfinityReduction.reduce_rhsBase]
  rfl

/-- When the slope `c` vanishes after reduction, the reduced integral
factorization is the constant special vertical factorization at `t=ā`. -/
theorem reduced_curve_eq_of_reduce_c_eq_zero
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C (N13IntegralInfinityReduction.reduceBase E.a)) =
      N13IntegralInfinityReduction.reducePoly E.m *
        N13IntegralInfinityReduction.reducePoly E.w := by
  have h :=
    congrArg N13IntegralInfinityReduction.reducePoly E.curve_eq
  rw [reduce_verticalCurve] at h
  simpa [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc] using h

/-- The reduced vertical quadratic remains monic. -/
theorem reduced_m_monic
    (E : VerticalGraph) :
    (N13IntegralInfinityReduction.reducePoly E.m).Monic :=
  E.m_monic.map N13IntegralInfinityReduction.reduceBase

/-- A monic integral quadratic keeps degree two after reduction. -/
theorem reduced_m_natDegree
    (E : VerticalGraph)
    (hmDegree : E.m.natDegree = 2) :
    (N13IntegralInfinityReduction.reducePoly E.m).natDegree = 2 := by
  rw [N13IntegralInfinityReduction.reducePoly_apply,
    E.m_monic.natDegree_map, hmDegree]

/-- In the constant-slope branch, reducing the integral infinity graph ideal
gives the literal special vertical ideal `(m̄(v),t-ā)`. -/
theorem map_infinityIdeal_of_reduce_c_eq_zero
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
      N13SpecialConstantInfinityVerticalGraph.verticalIdeal
        (N13IntegralInfinityReduction.reducePoly E.m)
        (N13IntegralInfinityReduction.reduceBase E.a) := by
  rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
    N13SpecialConstantInfinityVerticalGraph.verticalIdeal,
    Ideal.map_span, Set.image_pair]
  simp only [map_sub, N13IntegralInfinityReduction.reduce_tClass,
    reduce_aeval_vClass]
  congr 2
  simp [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc]
  exact
    (IsScalarTower.algebraMap_apply
      K K[X] N13IntegralInfinityReduction.SpecialRing
      (N13IntegralInfinityReduction.reduceBase E.a)).symm

/-- The canonical constant special fibre has `x` invertible modulo its
affine chart ideal.  At `t=0` the affine ideal is the unit ideal; at `t=1`
the relation is `x=1`. -/
theorem constantInfinityFibre_affine_xUnitMod
    (a : K) :
    N13SpecialAffineSaturation.XUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          a)).affineIdeal := by
  rw [
    N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor_affineIdeal]
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · refine ⟨0, ?_⟩
    simp
  · simp only [if_false, one_ne_zero]
    refine ⟨1, ?_⟩
    have hgen :
        N13GoodCoordinateRingTwo.xClass (X - C (1 : K)) ∈
          Ideal.span
            ({N13GoodCoordinateRingTwo.xClass (X - C (1 : K))} :
              Set N13GoodCoordinateRingTwo.CoordinateRing) :=
      Ideal.subset_span (by simp)
    have hneg :=
      (Ideal.span
        ({N13GoodCoordinateRingTwo.xClass (X - C (1 : K))} :
          Set N13GoodCoordinateRingTwo.CoordinateRing)).neg_mem hgen
    convert hneg using 1
    simp [N13SpecialCurveOverlap.xClass]

/-- If the vertical slope reduces to zero, the complete reduced two-chart
line is the canonical fibre over the constant special coordinate `t=ā`. -/
theorem restrict_twoChartLine_of_reduce_c_eq_zero
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
          u E hu huDegree hmDegree huMem) =
      N13SpecialDivisorCharts.ofDivisor
        (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          (N13IntegralInfinityReduction.reduceBase E.a)) := by
  apply
    N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
  · apply
      N13SpecialAffineSaturation.map_reduceCoordinate_xUnitMod
    exact
      N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_xUnitMod
        u E hu huDegree
  · exact
      constantInfinityFibre_affine_xUnitMod
        (N13IntegralInfinityReduction.reduceBase E.a)
  · change
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
            (N13IntegralInfinityReduction.reduceBase E.a))).infinityIdeal
    rw [map_infinityIdeal_of_reduce_c_eq_zero E hc,
      N13SpecialConstantInfinityVerticalGraph.verticalIdeal_eq_span
        (N13IntegralInfinityReduction.reducePoly E.m)
        (N13IntegralInfinityReduction.reducePoly E.w)
        (N13IntegralInfinityReduction.reduceBase E.a)
        (reduced_m_monic E)
        (reduced_m_natDegree E hmDegree)
        (reduced_curve_eq_of_reduce_c_eq_zero E hc),
      N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor_infinityIdeal]

end

end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
