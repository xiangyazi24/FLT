import FLT.Assumptions.MazurProof.N13IntegralMatchedNorm

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Convert the four retained integral coefficient bounds to the literal
coefficientwise hypotheses of the accepted centered-norm theorem.
-/

namespace MazurProof.N13IntegralHermiteCoefficientBounds

noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem linear_coefficients_mem (J : Ideal R₂) (a b : R₂)
    (ha : a ∈ J) (hb : b ∈ J) : ∀ n, (C a + C b * X).coeff n ∈ J := by
  intro n
  rcases n with _ | n
  · simpa using ha
  · rcases n with _ | n
    · simpa using hb
    · have hz : (C a + C b * X).coeff (n + 1 + 1) = 0 := by simp
      rw [hz]
      exact J.zero_mem

theorem quad_monic (a b : R₂) : (quad a b).Monic := by
  unfold quad
  monicity!

theorem lin_coefficients_mem (P : DiskPair) (e₀ e₁ : R₂)
    (he₀ : e₀ ∈ I P * I P) (he₁ : e₁ ∈ I P * I P) :
    ∀ n, (lin e₀ e₁).coeff n ∈ I P * I P :=
  linear_coefficients_mem (I P * I P) e₀ e₁ he₀ he₁

theorem centered_coefficients_mem (P : DiskPair) (d₀ d₁ : R₂)
    (hd₀ : d₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P)
    (hd₁ : d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P) :
    ∀ n, (quad d₀ d₁ - N13MumfordCenteredDoublingJet.centeredSquareU P).coeff n ∈ I P * I P := by
  have he : quad d₀ d₁ - N13MumfordCenteredDoublingJet.centeredSquareU P =
      C (d₀ - 2 * P.x₀ * P.x₁) + C (d₁ + 2 * (P.x₀ + P.x₁) + 1) * X := by
    simp only [quad, N13MumfordCenteredDoublingJet.centeredSquareU,
      N13TwoAdicAbelChartData.DiskPair.u, N13AbelChartBase.baseSmoothMumford_u,
      N13FormalAbelLinearization.uBase, map_add, map_sub, map_mul, map_ofNat, map_one]
    ring
  rw [he]
  exact linear_coefficients_mem (I P * I P) _ _ hd₀ hd₁

end
end MazurProof.N13IntegralHermiteCoefficientBounds
