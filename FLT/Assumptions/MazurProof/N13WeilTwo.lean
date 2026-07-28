import FLT.Assumptions.MazurProof.N13GoodModelTwo

/-!
# The characteristic-two Weil numerator for `X₁(13)`

`N13GoodModelTwo` proves structurally that the good completion has six points
over both `F₂` and `F₄`.  This file applies the genus-two Newton identities
to those two counts.  They force

`P₂(T) = 1 + 3T + 5T² + 6T³ + 4T⁴`

and `P₂(1)=19`.

Mathlib currently has no general genus-two zeta/Jacobian theorem identifying
this evaluation with the cardinality of the special-fibre Jacobian.  The
elementary trace calculation is therefore kept separate from that remaining
geometric interface.
-/

namespace MazurProof.N13WeilTwo

noncomputable section

open Polynomial

/-- Size of the ground field. -/
def q : ℤ := 2

/-- The point count over `F₂`, supplied by the good-model layer. -/
def N₁ : ℤ :=
  Nat.card (N13GoodModelTwo.CompletedPoint N13GoodModelTwo.F2)

/-- The point count over `F₄`, supplied by the good-model layer. -/
def N₂ : ℤ :=
  Nat.card (N13GoodModelTwo.CompletedPoint N13GoodModelTwo.F4)

theorem N₁_eq_six : N₁ = 6 := by
  rw [N₁, N13GoodModelTwo.completed_points_f2_card]
  norm_num

theorem N₂_eq_six : N₂ = 6 := by
  rw [N₂, N13GoodModelTwo.completed_points_f4_card]
  norm_num

/-- The first two genus-two Newton point-count equations. -/
def CountEquations (s₁ s₂ : ℤ) : Prop :=
  N₁ = q + 1 - s₁ ∧
  N₂ = q ^ 2 + 1 - (s₁ ^ 2 - 2 * s₂)

/-- The two point counts uniquely determine the first two symmetric
Frobenius coefficients. -/
theorem countEquations_iff (s₁ s₂ : ℤ) :
    CountEquations s₁ s₂ ↔ s₁ = -3 ∧ s₂ = 5 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [N₁_eq_six] at h₁
    rw [N₂_eq_six] at h₂
    dsimp only [q] at h₁ h₂
    have hs₁ : s₁ = -3 := by
      linarith
    have hs₂ : s₂ = 5 := by
      rw [hs₁] at h₂
      norm_num at h₂
      linarith
    exact ⟨hs₁, hs₂⟩
  · rintro ⟨rfl, rfl⟩
    simp only [CountEquations, N₁_eq_six, N₂_eq_six, q]
    norm_num

/-- Reciprocal genus-two numerator associated to `q,s₁,s₂`. -/
def genusTwoNumerator (q s₁ s₂ : ℤ) : ℤ[X] :=
  1 - C s₁ * X + C s₂ * X ^ 2 - C (q * s₁) * X ^ 3 +
    C (q ^ 2) * X ^ 4

/-- The concrete numerator forced by the two point counts. -/
def P₂ : ℤ[X] :=
  1 + C 3 * X + C 5 * X ^ 2 + C 6 * X ^ 3 + C 4 * X ^ 4

theorem genusTwoNumerator_eq_P₂ {s₁ s₂ : ℤ}
    (heq : CountEquations s₁ s₂) :
    genusTwoNumerator q s₁ s₂ = P₂ := by
  obtain ⟨rfl, rfl⟩ := (countEquations_iff s₁ s₂).mp heq
  norm_num [genusTwoNumerator, q, P₂]

/-- Evaluation of the forced numerator at one. -/
theorem P₂_eval_one : P₂.eval 1 = 19 := by
  norm_num [P₂]

end

end MazurProof.N13WeilTwo
