import FLT.Assumptions.MazurProof.N13ActualPrincipalNorm
import FLT.Assumptions.MazurProof.N13NormalizedHermiteResidual
import FLT.Assumptions.MazurProof.N13CenteredNormFirstOrder

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Descend the actual matched norm identity to Z2. Leading coefficients
determine the scalar exactly as 1-e1 after cancelling the nonzero rational
normalization scale squared. Coefficient injection then gives the literal
integral norm equation required by the accepted centered-norm theorem.
-/

namespace MazurProof.N13IntegralMatchedNorm

noncomputable section
open Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev R₂ := ℤ_[2]
abbrev U : R₂[X] := N13AbelChartBase.baseSmoothMumford.u

def normPoly (A b : R₂[X]) : R₂[X] :=
  (U * A) ^ 2 - (U * A) * b * N13GeneralizedMumfordIntegral.hPoly -
    b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly

theorem norm_map (A b : R₂[X]) :
    (normPoly A b).map c =
      ((X ^ 2 + X) * A.map c) ^ 2 -
        ((X ^ 2 + X) * A.map c) * b.map c * N13GeneralizedMumfordIntegral.hPoly -
        (b.map c) ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly := by
  simp [normPoly, U, N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly]

theorem norm_leading (P : DiskPair) (d₀ d₁ e₀ e₁ : R₂)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P) :
    (normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁)).leadingCoeff = 1 - e₁ := by
  have hu := N13NormalizedHermiteResidual.one_sub_unit P e₁ he₁
  have hd : (N13HermiteResidualDivisibility.residual d₀ d₁ e₀ e₁).natDegree = 6 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
      (N13NormalizedHermiteResidual.residual_degree_le _ _ _ _)
    rw [N13NormalizedHermiteResidual.residual_coeff_six]
    exact hu.ne_zero
  have hf : normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁) =
        U * N13HermiteResidualDivisibility.residual d₀ d₁ e₀ e₁ := by
    simpa [normPoly, U, N13FormalAbelLinearization.uBase] using
      N13HermiteResidualDivisibility.norm_factor d₀ d₁ e₀ e₁
  rw [hf, leadingCoeff_monic_mul N13AbelChartBase.baseSmoothMumford.u_monic,
    leadingCoeff, hd, N13NormalizedHermiteResidual.residual_coeff_six]

theorem descend_actual_norm
    (P Q : DiskPair) (A b : K[X]) (t : K) (ht : t ≠ 0)
    (d₀ d₁ e₀ e₁ : R₂)
    (hA : A = C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c)
    (hb : b = C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P)
    (k : Kˣ)
    (hnorm : ((X ^ 2 + X) * A) ^ 2 -
        ((X ^ 2 + X) * A) * b * N13GeneralizedMumfordIntegral.hPoly -
        b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
      C (k : K) * (P.u.map c) ^ 2 * (X ^ 2 + X) * Q.u.map c) :
    normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁) =
        C (1 - e₁) * P.u ^ 2 * U * Q.u := by
  let N := normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
    (N13HermiteResidualDivisibility.lin e₀ e₁)
  let T := P.u ^ 2 * U * Q.u
  have hTm : (T.map c).Monic :=
    (((P.u_monic.pow 2).mul N13AbelChartBase.baseSmoothMumford.u_monic).mul Q.u_monic).map c
  have hlN : (N.map c).leadingCoeff = c (1 - e₁) := by
    rw [Polynomial.leadingCoeff_map_of_injective (IsFractionRing.injective R₂ K)]
    exact congrArg c (norm_leading P d₀ d₁ e₀ e₁ he₁)
  have he : C (t ^ 2) * N.map c = C (k : K) * T.map c := by
    calc
      C (t ^ 2) * N.map c =
          ((X ^ 2 + X) * A) ^ 2 -
            ((X ^ 2 + X) * A) * b * N13GeneralizedMumfordIntegral.hPoly -
            b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly := by
        simp only [hA, hb]
        dsimp [N]
        rw [norm_map, map_pow]
        ring
      _ = C (k : K) * (P.u.map c) ^ 2 * (X ^ 2 + X) * Q.u.map c := hnorm
      _ = C (k : K) * T.map c := by
        simp [T, U, N13FormalAbelLinearization.uBase, mul_assoc]
  have hk : t ^ 2 * c (1 - e₁) = (k : K) := by
    have hl := congrArg Polynomial.leadingCoeff he
    rw [leadingCoeff_mul, leadingCoeff_C, hlN, hTm.leadingCoeff_C_mul] at hl
    exact hl
  have hmapped : N.map c = C (c (1 - e₁)) * T.map c := by
    apply mul_left_cancel₀ (show (C (t ^ 2) : K[X]) ≠ 0 from C_ne_zero.mpr (pow_ne_zero 2 ht))
    rw [he, ← hk, map_mul, mul_assoc]
  apply Polynomial.map_injective c (IsFractionRing.injective R₂ K)
  simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    N, T, mul_assoc] using hmapped

end
end MazurProof.N13IntegralMatchedNorm
