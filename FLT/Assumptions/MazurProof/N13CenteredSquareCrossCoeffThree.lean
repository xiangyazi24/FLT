import FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingJet

open Polynomial

namespace MazurProof.N13CenteredSquareCrossCoeffThree

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev DiskPair : Type :=
  N13MumfordCenteredDoublingJet.DiskPair

abbrev R₂ : Type :=
  N13MumfordCenteredDoublingJet.R₂

/-- For the canonical first-order centered square normalization, the
degree-three cross coefficient vanishes identically. -/
theorem centeredSquare_crossCoeff_three_eq_zero
    (P : DiskPair) :
    (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u *
          N13MumfordCenteredDoublingJet.centeredSquareU P).coeff 3 = 0 := by
  rw [
    N13MumfordCenteredDoublingJet.u_sq_sub_base_mul_centeredSquareU,
    N13MumfordFormalTransitionJet.u_sub_base
  ]
  let a : R₂ := -(P.x₀ + (P.x₁ + 1))
  let b : R₂ := P.x₀ * P.x₁
  -- The polynomial (C a * X + C b) has degree at most 1, so its square has degree at most 2
  have hdeg : ((C a * X + C b) ^ 2).natDegree ≤ 2 := by
    have h1 : (C a * X + C b).natDegree ≤ 1 := by
      -- Use degree_add_le which gives the bound without requiring non-zero
      have h2 : (C a * X + C b).natDegree ≤ max (C a * X).natDegree (C b).natDegree := by
        apply Polynomial.natDegree_add_le
      -- Both C a * X and C b have degree at most 1
      have h3 : (C a * X).natDegree ≤ 1 := by
        -- degree of C a * X is at most 1 (it's either 0 or 1 depending on whether a = 0)
        calc
          (C a * X).natDegree ≤ (C a).natDegree + X.natDegree := by
            apply Polynomial.natDegree_mul_le
          _ ≤ 0 + 1 := by
            gcongr <;> simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
          _ = 1 := by norm_num
      have h4 : (C b).natDegree ≤ 1 := by
        simp [Polynomial.natDegree_C]
      have h5 : max (C a * X).natDegree (C b).natDegree ≤ 1 := by
        rw [max_le_iff]
        constructor <;> assumption
      exact le_trans h2 h5
    calc
      ((C a * X + C b) ^ 2).natDegree ≤ 2 * (C a * X + C b).natDegree := by
        apply Polynomial.natDegree_pow_le
      _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 h1
      _ = 2 := by norm_num
  have hcoeff : ((C a * X + C b) ^ 2).coeff 3 = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  exact hcoeff

/-- Consequently the degree-three cross coefficient belongs to the square
of the moving coordinate ideal. -/
theorem centeredSquare_crossCoeff_three
    (P : DiskPair) :
    (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u *
          N13MumfordCenteredDoublingJet.centeredSquareU P).coeff 3 ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  rw [centeredSquare_crossCoeff_three_eq_zero]
  exact Ideal.zero_mem _

end

end MazurProof.N13CenteredSquareCrossCoeffThree
