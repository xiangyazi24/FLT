import FLT.Assumptions.MazurProof.N13IntegralGraphContraction
import FLT.Assumptions.MazurProof.N13SpecialGraphDivisor

/-!
# Abel-compatible reduction of integral N13 Mumford graphs

Coefficientwise reduction of a smooth integral generalized Mumford graph is
again a special-fibre Mumford graph.  If its effective degree-two divisor
has the selected set-valued Abel class, special Abel rigidity identifies the
literal reduced graph ideal with `(X²+X,Y)`.

Combining this with exact contraction of integral sextic graphs gives the
representative-level special-ideal equality required by the two-fibre graph
recovery theorem.  The remaining geometric input is now only the existence
of an integral representative and its Abel compatibility.
-/

open Polynomial

namespace MazurProof.N13SpecialGraphReduction

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- Monic degree is preserved by coefficientwise reduction. -/
theorem reduceSmoothMumford_u_natDegree
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2) :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford D).u.natDegree =
      2 := by
  change
    (D.u.map
      N13GeneralizedMumfordReduction.reduceBase).natDegree = 2
  calc
    (D.u.map
        N13GeneralizedMumfordReduction.reduceBase).natDegree =
        D.u.natDegree :=
      D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase
    _ = 2 := hdeg

/-- An integral graph whose reduced divisor has the selected Abel class
maps to the fixed special graph ideal. -/
theorem map_mumfordIdeal_eq_special_of_setAbel_eq
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (reduceSmoothMumford_u_natDegree D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
      N13SpecialQuotientBasis.specialIdeal := by
  rw [N13GeneralizedMumfordReduction.map_smoothMumfordIdeal]
  exact
    N13SpecialGraphDivisor.mumfordIdeal_eq_special_of_setAbel_eq
      (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
      (reduceSmoothMumford_u_natDegree D hdeg) habel

/-- For an integral quadratic graph, mapped-ideal equality is equivalent to
the intrinsic special-fibre Abel equality. -/
theorem setAbel_eq_iff_map_mumfordIdeal_eq_special
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (reduceSmoothMumford_u_natDegree D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal := by
  rw [N13GeneralizedMumfordReduction.map_smoothMumfordIdeal]
  exact
    N13SpecialGraphDivisor.setAbel_eq_iff_mumfordIdeal_eq_special
      (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
      (reduceSmoothMumford_u_natDegree D hdeg)

/-- Exact contraction turns the preceding Abel statement into precisely the
special-ideal equality consumed by the concrete two-fibre recovery layer. -/
theorem map_contractIdeal_sexticIdeal_eq_special_of_setAbel_eq
    (D : SmoothMumford₂)
    (nInf : ℤ)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (reduceSmoothMumford_u_natDegree D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13IntegralGraphContraction.sexticIdeal D nInf)) =
      N13SpecialQuotientBasis.specialIdeal := by
  rw [N13IntegralGraphContraction.contractIdeal_sexticIdeal]
  exact map_mumfordIdeal_eq_special_of_setAbel_eq D hdeg habel

end

end MazurProof.N13SpecialGraphReduction
