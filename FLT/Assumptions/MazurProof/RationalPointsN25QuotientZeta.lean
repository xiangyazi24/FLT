import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF16Field

/-!
# Newton data for the level-25 genus-four quotient

The kernel-checked point counts over the first four binary extensions are
converted here into the first four Frobenius power sums.  The imported cubic
and quartic field-table certificates justify the executable extension-field
models.  Newton's identities then determine the first half of the degree-eight
numerator, and genus-four Weil reciprocity supplies the second half:

`P(T) = 1 + 2T + 2T^2 + 5T^3 + 11T^4 + 10T^5 + 8T^6 + 16T^7 + 16T^8`.

The file proves only the exact integer and polynomial calculation, including
`P(1)=71`.  Identifying this polynomial with the zeta numerator of the curve
requires geometric smoothness, genus, and the general Weil functional
equation.  Identifying `P(1)` with the special-fibre Jacobian cardinality is a
further general algebraic-geometric theorem not currently supplied by
Mathlib; neither statement is assumed here.
-/

namespace MazurProof.RationalPointsN25QuotientZeta

noncomputable section

open Polynomial
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil

/-- The cardinality of the ground field. -/
def q : ℤ := 2

/-- The projective point count over `F_2`. -/
def N₁ : ℤ := canonicalPoints25F2.card

/-- The projective point count over `F_4`. -/
def N₂ : ℤ := canonicalNormalizedPoints25F4.card

/-- The projective point count over `F_8`. -/
def N₃ : ℤ := canonicalProjectivePointCount25F8

/-- The projective point count over `F_16`. -/
def N₄ : ℤ := canonicalProjectivePointCount25F16

/-- The first point count is five, by exhaustive enumeration over `F_2`. -/
theorem N₁_eq_five : N₁ = 5 := by
  rw [N₁, canonicalPoints25F2_card]
  norm_num

/-- The second point count is five, by exhaustive enumeration over `F_4`. -/
theorem N₂_eq_five : N₂ = 5 := by
  rw [N₂, canonicalNormalizedPoints25F4_card]
  norm_num

/-- The third point count is twenty, by exhaustive enumeration over `F_8`. -/
theorem N₃_eq_twenty : N₃ = 20 := by
  rw [N₃, canonicalProjectivePointCount25F8_eq]
  norm_num

/-- The fourth point count is twenty-nine, by exhaustive enumeration over
`F_16`. -/
theorem N₄_eq_twenty_nine : N₄ = 29 := by
  rw [N₄, canonicalProjectivePointCount25F16_eq]
  norm_num

/-- Point-count equations for the first four Frobenius power sums, in the
sign convention `s_n = q^n + 1 - #C(F_{q^n})`. -/
def CountMomentEquations (s₁ s₂ s₃ s₄ : ℤ) : Prop :=
  N₁ = q + 1 - s₁ ∧
  N₂ = q ^ 2 + 1 - s₂ ∧
  N₃ = q ^ 3 + 1 - s₃ ∧
  N₄ = q ^ 4 + 1 - s₄

/-- The four certified point counts uniquely determine the Frobenius power
sums `(-2, 0, -11, -12)`. -/
theorem countMomentEquations_iff (s₁ s₂ s₃ s₄ : ℤ) :
    CountMomentEquations s₁ s₂ s₃ s₄ ↔
      s₁ = -2 ∧ s₂ = 0 ∧ s₃ = -11 ∧ s₄ = -12 := by
  simp only [CountMomentEquations, N₁_eq_five, N₂_eq_five,
    N₃_eq_twenty, N₄_eq_twenty_nine, q]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num

/-- Newton's first four coefficient equations for a polynomial
`1 + a₁T + ... + a₄T⁴ + ...` whose reciprocal roots have power sums
`s₁,...,s₄`. -/
def NewtonCoefficientEquations
    (s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ : ℤ) : Prop :=
  a₁ + s₁ = 0 ∧
  2 * a₂ + s₁ * a₁ + s₂ = 0 ∧
  3 * a₃ + s₁ * a₂ + s₂ * a₁ + s₃ = 0 ∧
  4 * a₄ + s₁ * a₃ + s₂ * a₂ + s₃ * a₁ + s₄ = 0

/-- The point-count moments and Newton identities force the first-half
coefficients `(2,2,5,11)`. -/
theorem count_and_newton_force_coefficients
    {s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ : ℤ}
    (hcount : CountMomentEquations s₁ s₂ s₃ s₄)
    (hnewton : NewtonCoefficientEquations s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄) :
    a₁ = 2 ∧ a₂ = 2 ∧ a₃ = 5 ∧ a₄ = 11 := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    (countMomentEquations_iff s₁ s₂ s₃ s₄).mp hcount
  rcases hnewton with ⟨h₁, h₂, h₃, h₄⟩
  have ha₁ : a₁ = 2 := by omega
  have ha₂ : a₂ = 2 := by omega
  have ha₃ : a₃ = 5 := by omega
  have ha₄ : a₄ = 11 := by omega
  exact ⟨ha₁, ha₂, ha₃, ha₄⟩

/-- Reciprocal degree-eight numerator associated to a genus-four curve over a
field of size `q`, written in terms of its first four coefficients.  The
coefficients above degree four encode the Weil functional equation. -/
def genusFourReciprocalNumerator
    (q a₁ a₂ a₃ a₄ : ℤ) : ℤ[X] :=
  1 + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4 +
    C (q * a₃) * X ^ 5 + C (q ^ 2 * a₂) * X ^ 6 +
    C (q ^ 3 * a₁) * X ^ 7 + C (q ^ 4) * X ^ 8

/-- The concrete reciprocal polynomial forced by the four point-count
moments, subject to the genus-four Weil functional equation. -/
def P₂₅ : ℤ[X] :=
  1 + C 2 * X + C 2 * X ^ 2 + C 5 * X ^ 3 + C 11 * X ^ 4 +
    C 10 * X ^ 5 + C 8 * X ^ 6 + C 16 * X ^ 7 + C 16 * X ^ 8

/-- The certified moments satisfy Newton's equations with coefficients
`(2,2,5,11)`. -/
theorem certified_newton_equations :
    NewtonCoefficientEquations (-2) 0 (-11) (-12) 2 2 5 11 := by
  norm_num [NewtonCoefficientEquations]

/-- The four point counts, Newton identities, and reciprocal coefficient rule
produce the displayed degree-eight polynomial exactly. -/
theorem genusFourReciprocalNumerator_eq_P₂₅ :
    genusFourReciprocalNumerator q 2 2 5 11 = P₂₅ := by
  norm_num [genusFourReciprocalNumerator, q, P₂₅]

/-- The forced reciprocal numerator evaluates to seventy-one at one.  Once a
general curve-zeta/Jacobian bridge is available, this is the arithmetic input
for `#Jac(C)(F_2)=71`. -/
theorem P₂₅_eval_one : P₂₅.eval 1 = 71 := by
  norm_num [P₂₅]

end

end MazurProof.RationalPointsN25QuotientZeta
