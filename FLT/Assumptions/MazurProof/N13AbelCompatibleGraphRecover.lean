import FLT.Assumptions.MazurProof.N13SpecialGraphReduction
import FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover

/-!
# Recovering an N13 disk pair from an Abel-compatible integral graph

A special-fibre Abel equality identifies the reduced quadratic graph with
the selected divisor.  Its graph polynomial is therefore zero modulo the
reduced quadratic, but need not itself reduce coefficientwise to zero.

This file removes that harmless choice of representative.  Replacing `v`
by its monic remainder modulo `u`, and changing `w` by the resulting exact
algebraic formula, preserves the generalized Mumford equation, smoothness,
and graph ideal.  The normalized graph then satisfies the literal hypotheses
of the two-adic Hensel recovery theorem.
-/

open Polynomial

namespace MazurProof.N13AbelCompatibleGraphRecover

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂

abbrev K : Type :=
  N13GeneralizedMumfordReduction.K

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- The quotient removed from the graph polynomial. -/
def graphQuotient (D : SmoothMumford₂) : R₂[X] :=
  D.v /ₘ D.u

/-- The canonical graph polynomial of degree strictly below `u`. -/
def normalizedV (D : SmoothMumford₂) : R₂[X] :=
  D.v %ₘ D.u

/-- The quotient in the generalized Mumford equation after replacing
`v` by its monic remainder modulo `u`. -/
def normalizedW (D : SmoothMumford₂) : R₂[X] :=
  D.w -
      graphQuotient D *
        (2 * D.v +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
    D.u * graphQuotient D ^ 2

theorem normalizedV_add_mul_graphQuotient
    (D : SmoothMumford₂) :
    normalizedV D + D.u * graphQuotient D = D.v :=
  Polynomial.modByMonic_add_div D.v D.u

/-- Monic-remainder normalization preserves both the generalized curve
equation and its smoothness Bezout identity. -/
def normalizeSmoothMumford
    (D : SmoothMumford₂) : SmoothMumford₂ where
  u := D.u
  v := normalizedV D
  w := normalizedW D
  u_monic := D.u_monic
  curve_eq := by
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (D.v - D.u * graphQuotient D) ^ 2 +
            N13GeneralizedMumfordIntegral.hPoly *
              (D.v - D.u * graphQuotient D) -
          N13GeneralizedMumfordIntegral.rhsPoly =
          (D.v ^ 2 +
                N13GeneralizedMumfordIntegral.hPoly * D.v -
              N13GeneralizedMumfordIntegral.rhsPoly) -
            D.u * graphQuotient D *
              (2 * D.v +
                N13GeneralizedMumfordIntegral.hPoly) +
            D.u ^ 2 * graphQuotient D ^ 2 := by ring
      _ =
          D.u *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly) +
              D.u * graphQuotient D ^ 2) := by
        rw [D.curve_eq]
        ring
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine
      ⟨a + 2 * b * graphQuotient D +
          c * graphQuotient D ^ 2,
        b + c * graphQuotient D, c, ?_⟩
    have hv :
        normalizedV D =
          D.v - D.u * graphQuotient D := by
      linear_combination normalizedV_add_mul_graphQuotient D
    rw [hv]
    unfold normalizedW
    calc
      (a + 2 * b * graphQuotient D +
              c * graphQuotient D ^ 2) * D.u +
            (b + c * graphQuotient D) *
              (2 * (D.v - D.u * graphQuotient D) +
                N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c *
            (D.w -
                graphQuotient D *
                  (2 * D.v +
                    N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
              D.u * graphQuotient D ^ 2) =
          a * D.u +
              b *
                (2 * D.v +
                  N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
            c * D.w := by ring
      _ = 1 := habc

@[simp] theorem normalizeSmoothMumford_u
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).u = D.u := rfl

@[simp] theorem normalizeSmoothMumford_v
    (D : SmoothMumford₂) :
    (normalizeSmoothMumford D).v = normalizedV D := rfl

/-- Normalization does not change the integral graph ideal. -/
theorem normalizeSmoothMumford_mumfordIdeal
    (D : SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.mumfordIdeal
        (normalizeSmoothMumford D).u
        (normalizeSmoothMumford D).v =
      N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v := by
  exact
    N13TwoAdicAbelChartRecover.NearBaseMumford.mumfordIdeal_eq_of_dvd_sub
      D.u (normalizedV D) D.v
      (Polynomial.dvd_modByMonic_sub D.v D.u)

/-- Abel compatibility of the special fibre makes the normalized integral
graph a literal near-base graph. -/
def normalizedNearBase
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree
              D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    N13TwoAdicAbelChartRecover.NearBaseMumford where
  toSmoothMumford₂ := normalizeSmoothMumford D
  reduce_u := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    exact
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).1
  reduce_v := by
    have hgraph :=
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_setAbel_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        habel
    have hdvd :
        N13GeneralizedMumfordReduction.reducePoly D.u ∣
          N13GeneralizedMumfordReduction.reducePoly D.v :=
      (N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
        (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
        (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree D hdeg)
        hgraph).2
    change
      N13GeneralizedMumfordReduction.reducePoly
          (D.v %ₘ D.u) = 0
    rw [N13GeneralizedMumfordReduction.reducePoly_apply,
      Polynomial.map_modByMonic
        N13GeneralizedMumfordReduction.reduceBase D.u_monic]
    exact
      (Polynomial.modByMonic_eq_zero_iff_dvd
        (D.u_monic.map
          N13GeneralizedMumfordReduction.reduceBase)).2 hdvd

/-- The disk pair recovered by Hensel lifting from an Abel-compatible
integral graph. -/
def recoveredDiskPair
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree
              D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    N13TwoAdicAbelChartData.DiskPair :=
  (normalizedNearBase D hdeg habel).diskPair

/-- Recovery is exact at the level of integral graph ideals. -/
theorem mumfordIdeal_eq_recoveredDiskPair
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (N13SpecialGraphReduction.reduceSmoothMumford_u_natDegree
              D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (recoveredDiskPair D hdeg habel).u
        (recoveredDiskPair D hdeg habel).v := by
  unfold recoveredDiskPair
  rw [←
    (normalizedNearBase D hdeg habel).mumfordIdeal_diskPair]
  exact (normalizeSmoothMumford_mumfordIdeal D).symm

end

end MazurProof.N13AbelCompatibleGraphRecover
