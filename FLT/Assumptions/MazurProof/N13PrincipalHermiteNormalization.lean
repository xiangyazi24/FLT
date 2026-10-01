import FLT.Assumptions.MazurProof.N13RationalHermiteMatrix

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Match the actual rational principal numerator to an integral normalized
Hermite numerator. The degree-two leading coefficient is proved nonzero
from the same numerator's nonvanishing, rather than assumed or inverted
without justification. The integral coefficients retain their I² bounds.
-/

namespace MazurProof.N13PrincipalHermiteNormalization

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
open N13ActualHermiteEquations N13RationalHermiteMatrix
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem quadratic_eq (A : K[X]) (hA : A.natDegree ≤ 2) :
    A = C (A.coeff 2) * X ^ 2 + C (A.coeff 1) * X + C (A.coeff 0) := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp
  · have hp : A.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h₀ : n ≠ 0 := by omega
    have h₁ : n ≠ 1 := by omega
    have h₂ : n ≠ 2 := by omega
    simp [hp, h₀, h₁, h₂, Polynomial.coeff_C_mul]

theorem linear_eq (b : K[X]) (hb : b.natDegree ≤ 1) :
    b = C (b.coeff 0) + C (b.coeff 1) * X := by
  ext n
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp
  · have hp : b.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h₀ : n ≠ 0 := by omega
    have h₁ : n ≠ 1 := by omega
    simp [hp, h₀, h₁, Polynomial.coeff_C_mul]

theorem normalize_shape (P : DiskPair) (A b : K[X])
    (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1) (hne : A ≠ 0 ∨ b ≠ 0)
    (hv : ∀ j, (x P j ^ 2 + x P j) * A.eval (x P j) + b.eval (x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * A.eval (x P j) +
      (x P j ^ 2 + x P j) * A.derivative.eval (x P j) +
      b.derivative.eval (x P j) * y P j + b.eval (x P j) * s P j = 0) :
    ∃ t : K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c ∧
      b = C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  have ha := quadratic_eq A hA
  have hb' := linear_eq b hb
  have hAe (j : Fin 2) : A.eval (x P j) =
      A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0 := by
    have h := congrArg (fun p : K[X] => p.eval (x P j)) ha
    simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X] using h
  have hAd (j : Fin 2) : A.derivative.eval (x P j) =
      2 * A.coeff 2 * x P j + A.coeff 1 := by
    have h := congrArg (fun p : K[X] => p.derivative.eval (x P j)) ha
    simp [derivative_mul, derivative_pow, -mul_eq_zero] at h
    convert h using 1 <;> ring
  have hbeval (j : Fin 2) : b.eval (x P j) = b.coeff 0 + b.coeff 1 * x P j := by
    have h := congrArg (fun p : K[X] => p.eval (x P j)) hb'
    simpa only [eval_add, eval_mul, eval_C, eval_X] using h
  have hbder (j : Fin 2) : b.derivative.eval (x P j) = b.coeff 1 := by
    have h := congrArg (fun p : K[X] => p.derivative.eval (x P j)) hb'
    simpa [derivative_mul] using h
  have hv' (j : Fin 2) :
      (x P j ^ 2 + x P j) *
        (A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0) +
      (b.coeff 0 + b.coeff 1 * x P j) * y P j = 0 := by
    rw [← hAe, ← hbeval]
    exact hv j
  have hd' (j : Fin 2) :
      (2 * x P j + 1) *
        (A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0) +
      (x P j ^ 2 + x P j) * (2 * A.coeff 2 * x P j + A.coeff 1) +
      b.coeff 1 * y P j + (b.coeff 0 + b.coeff 1 * x P j) * s P j = 0 := by
    rw [← hAe, ← hAd, ← hbder, ← hbeval]
    exact hd j
  obtain ⟨d₀, d₁, e₀, e₁, h₀, h₁, k₀, k₁, hm⟩ :=
    coefficients_are_scaled_integral P (A.coeff 2) (A.coeff 0) (A.coeff 1)
      (b.coeff 0) (b.coeff 1) hv' hd'
  have hAe : A = C (A.coeff 2) * (N13HermiteResidualDivisibility.quad d₀ d₁).map c := by
    conv_lhs => rw [ha]
    simp only [N13HermiteResidualDivisibility.quad, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    rw [h₀, h₁]
    simp only [map_mul]
    ring
  have hbe : b = C (A.coeff 2) * (N13HermiteResidualDivisibility.lin e₀ e₁).map c := by
    conv_lhs => rw [hb']
    simp only [N13HermiteResidualDivisibility.lin, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    rw [k₀, k₁]
    simp only [map_mul]
    ring
  refine ⟨A.coeff 2, d₀, d₁, e₀, e₁, ?_, hAe, hbe, hm⟩
  intro ht
  have hAz : A = 0 := by simpa only [ht, C_0, zero_mul] using hAe
  have hbz : b = 0 := by simpa only [ht, C_0, zero_mul] using hbe
  exact hne.elim (fun h => h hAz) (fun h => h hbz)

/-- Actual principal membership supplies the normalization hypotheses.
This is same-witness matching, not a separate choice of a divisor or class. -/
theorem normalize_actual_numerator (P Q : DiskPair) (n : R) (A b : K[X])
    (hn : n ≠ 0) (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1)
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy)
    (hmem : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    ∃ t : K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c ∧
      b = C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨hv, hd⟩ := hermite_equations_of_product_membership P Q n A b hshape hmem
  apply normalize_shape P A b hA hb ?_ hv hd
  by_contra hz
  push_neg at hz
  have he : toGood n = 0 := by simp [hshape, hz.1, hz.2]
  apply hn
  apply (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm.injective
  simpa only [map_zero] using he

end
end MazurProof.N13PrincipalHermiteNormalization
