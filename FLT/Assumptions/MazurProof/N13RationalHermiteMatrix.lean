import FLT.Assumptions.MazurProof.N13ActualHermiteEquations

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

The accepted integral interpolation matrix stays invertible over Q2.
Consequently every rational Hermite numerator with leading coefficient t
has its four remaining coefficients equal to t times one integral solution.
No division by a moving coordinate or by t occurs in this comparison.
-/

namespace MazurProof.N13RationalHermiteMatrix

noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev R₂ := ℤ_[2]

def matrixQ (P : DiskPair) : Matrix (Fin 4) (Fin 4) K :=
  (N13IntegralHermiteNumerator.matrix P (N13HermiteResidualDivisibility.slope P)).map c

def rhsQ (P : DiskPair) : Fin 4 → K :=
  fun j => c (N13IntegralHermiteNumerator.rightSide P j)

theorem matrixQ_unit (P : DiskPair) : IsUnit (matrixQ P) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h := (N13IntegralHermiteNumerator.matrix_det_unit P
    (N13HermiteResidualDivisibility.slope P)).map c
  rw [c.map_det] at h
  change IsUnit (matrixQ P).det at h
  exact h

theorem matrixQ_injective (P : DiskPair) : Function.Injective (matrixQ P).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr (matrixQ_unit P)

theorem matrix_equation (P : DiskPair) (t a₀ a₁ b₀ b₁ : K)
    (hv : ∀ j, (x P j ^ 2 + x P j) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (b₀ + b₁ * x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (x P j ^ 2 + x P j) * (2 * t * x P j + a₁) +
      b₁ * y P j + (b₀ + b₁ * x P j) * s P j = 0) :
    (matrixQ P).mulVec ![a₀, a₁, b₀, b₁] = t • rhsQ P := by
  have hv₀ := hv 0
  have hv₁ := hv 1
  have hd₀ := hd 0
  have hd₁ := hd 1
  dsimp [x, y, s, N13CenteredHermiteFirstOrder.x] at hv₀ hv₁ hd₀ hd₁
  ext j
  fin_cases j <;>
    simp [matrixQ, rhsQ, N13IntegralHermiteNumerator.matrix,
      N13IntegralHermiteNumerator.rightSide, Matrix.map,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, smul_eq_mul]
  · linear_combination hv₀
  · linear_combination hv₁
  · linear_combination hd₀
  · linear_combination hd₁

theorem exists_integral_solution (P : DiskPair) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (matrixQ P).mulVec ![c a₀, c a₁, c b₀, c b₁] = rhsQ P ∧
      b₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      b₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨a₀, a₁, b₀, b₁, hv, hd, hm⟩ :=
    N13IntegralHermiteNumerator.exists_normalized_coefficients P
      (N13HermiteResidualDivisibility.slope P)
  refine ⟨a₀, a₁, b₀, b₁, ?_, hm⟩
  have hvQ (j : Fin 2) :
      (x P j ^ 2 + x P j) * (1 * x P j ^ 2 + c a₁ * x P j + c a₀) +
        (c b₀ + c b₁ * x P j) * y P j = 0 := by
    have h := congrArg c (hv j)
    simpa only [map_add, map_mul, map_pow, map_zero, one_mul] using h
  have hdQ (j : Fin 2) :
      (2 * x P j + 1) * (1 * x P j ^ 2 + c a₁ * x P j + c a₀) +
        (x P j ^ 2 + x P j) * (2 * 1 * x P j + c a₁) +
        c b₁ * y P j + (c b₀ + c b₁ * x P j) * s P j = 0 := by
    have h := congrArg c (hd j)
    simpa only [map_add, map_mul, map_pow, map_zero, map_one, map_ofNat,
      one_mul, mul_one] using h
  simpa only [one_smul] using matrix_equation P 1 (c a₀) (c a₁) (c b₀) (c b₁) hvQ hdQ

/-- Rational Hermite data are a scalar multiple of an integral normalized
solution. This is an equality of coefficients, with their I² bounds retained. -/
theorem coefficients_are_scaled_integral (P : DiskPair) (t a₀ a₁ b₀ b₁ : K)
    (hv : ∀ j, (x P j ^ 2 + x P j) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (b₀ + b₁ * x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (x P j ^ 2 + x P j) * (2 * t * x P j + a₁) +
      b₁ * y P j + (b₀ + b₁ * x P j) * s P j = 0) :
    ∃ d₀ d₁ e₀ e₁ : R₂,
      a₀ = t * c d₀ ∧ a₁ = t * c d₁ ∧ b₀ = t * c e₀ ∧ b₁ = t * c e₁ ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨d₀, d₁, e₀, e₁, hsol, hm⟩ := exists_integral_solution P
  have he : ![a₀, a₁, b₀, b₁] = t • ![c d₀, c d₁, c e₀, c e₁] := by
    apply matrixQ_injective P
    rw [matrix_equation P t a₀ a₁ b₀ b₁ hv hd, Matrix.mulVec_smul, hsol]
  refine ⟨d₀, d₁, e₀, e₁, ?_, ?_, ?_, ?_, hm⟩
  · simpa using congrFun he (0 : Fin 4)
  · simpa using congrFun he (1 : Fin 4)
  · simpa using congrFun he (2 : Fin 4)
  · simpa using congrFun he (3 : Fin 4)

end
end MazurProof.N13RationalHermiteMatrix
