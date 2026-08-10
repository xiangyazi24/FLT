import FLT.Assumptions.MazurProof.RationalPointsN25QuotientHilbert
import FLT.Assumptions.MazurProof.RationalPointsN25NewformEulerCertificate

/-!
# Newton data at three for the level-25 quotient

The semantic canonical-model counts over the first four characteristic-three
extensions are `5`, `5`, `20`, and `89`.  This file converts them into the
Frobenius moments `(-1,5,8,-7)`, applies Newton's identities, and obtains the
first four reciprocal coefficients `(1,-2,-5,1)`.

Imposing the genus-four reciprocal coefficient rule gives

`1 + T - 2T² - 5T³ + T⁴ - 15T⁵ - 18T⁶ + 27T⁷ + 81T⁸`,

which is exactly the independently certified four-conjugate newform
polynomial at three.  This file proves that integer-polynomial coincidence;
it does not assert smoothness, good reduction, the curve zeta theorem, or the
modular quotient identification needed to interpret the polynomial as a
Jacobian Frobenius polynomial.
-/

namespace MazurProof.RationalPointsN25QuotientZetaThree

noncomputable section

open Polynomial
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientWeilThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic
open RationalPointsN25QuotientZeta
open RationalPointsN25NewformEulerCertificate

/-! ## Semantic point counts and Frobenius moments -/

/-- The cardinality of the characteristic-three ground field. -/
def q : ℤ := 3

/-- The semantic canonical-model point count over `F3`. -/
def N₁ : ℤ :=
  Nat.card {P : NormalizedProjective4 Trit // IsCanonicalNormalizedThree P}

/-- The semantic canonical-model point count over `F9`. -/
def N₂ : ℤ :=
  Nat.card {P : NormalizedProjective4 F9 // IsCanonicalNormalizedThree P}

/-- The semantic canonical-model point count over `F27`. -/
def N₃ : ℤ :=
  Nat.card {P : NormalizedProjective4 F27 // IsCanonicalNormalizedThree P}

/-- The semantic canonical-model point count over `F81`. -/
def N₄ : ℤ :=
  Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P}

/-- The ground-field canonical model has five points. -/
theorem N₁_eq_five : N₁ = 5 := by
  norm_num [N₁, f3_canonical_normalized_three_card]

/-- The quadratic-extension canonical model has five points. -/
theorem N₂_eq_five : N₂ = 5 := by
  norm_num [N₂, f9_canonical_normalized_three_card]

/-- The cubic-extension canonical model has twenty points. -/
theorem N₃_eq_twenty : N₃ = 20 := by
  norm_num [N₃, f27_canonical_normalized_three_card]

/-- The quartic-extension canonical model has eighty-nine points. -/
theorem N₄_eq_eighty_nine : N₄ = 89 := by
  norm_num [N₄, f81_canonical_normalized_three_card]

/-- Point-count equations for the first four power sums, using the convention
`s_n = 3^n + 1 - #C(F_{3^n})`. -/
def CountMomentEquations (s₁ s₂ s₃ s₄ : ℤ) : Prop :=
  N₁ = q + 1 - s₁ ∧
  N₂ = q ^ 2 + 1 - s₂ ∧
  N₃ = q ^ 3 + 1 - s₃ ∧
  N₄ = q ^ 4 + 1 - s₄

/-- The four semantic counts uniquely determine the power sums
`(-1,5,8,-7)`. -/
theorem countMomentEquations_iff (s₁ s₂ s₃ s₄ : ℤ) :
    CountMomentEquations s₁ s₂ s₃ s₄ ↔
      s₁ = -1 ∧ s₂ = 5 ∧ s₃ = 8 ∧ s₄ = -7 := by
  simp only [CountMomentEquations, N₁_eq_five, N₂_eq_five,
    N₃_eq_twenty, N₄_eq_eighty_nine, q]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num

/-! ## Newton coefficients and the reciprocal polynomial -/

/-- The characteristic-three counts and Newton identities force the first
half of a reciprocal degree-eight numerator to be `(1,-2,-5,1)`. -/
theorem count_and_newton_force_coefficients
    {s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ : ℤ}
    (hcount : CountMomentEquations s₁ s₂ s₃ s₄)
    (hnewton : NewtonCoefficientEquations s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄) :
    a₁ = 1 ∧ a₂ = -2 ∧ a₃ = -5 ∧ a₄ = 1 := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    (countMomentEquations_iff s₁ s₂ s₃ s₄).mp hcount
  rcases hnewton with ⟨h₁, h₂, h₃, h₄⟩
  have ha₁ : a₁ = 1 := by omega
  have ha₂ : a₂ = -2 := by omega
  have ha₃ : a₃ = -5 := by omega
  have ha₄ : a₄ = 1 := by omega
  exact ⟨ha₁, ha₂, ha₃, ha₄⟩

/-- The certified moments satisfy Newton's first four equations with
coefficients `(1,-2,-5,1)`. -/
theorem certified_newton_equations :
    NewtonCoefficientEquations (-1) 5 8 (-7) 1 (-2) (-5) 1 := by
  norm_num [NewtonCoefficientEquations]

/-- Genus-four reciprocity applied to the count-derived coefficients produces
exactly the independently certified newform polynomial at three.  The theorem
is an equality of explicit polynomials, not yet a geometric identification of
either polynomial with Frobenius on the quotient Jacobian. -/
theorem genusFourReciprocalNumerator_eq_newformAtThree :
    genusFourReciprocalNumerator q 1 (-2) (-5) 1 = P₂₅AtThree := by
  norm_num [genusFourReciprocalNumerator, q, P₂₅AtThree]
  ring

/-- The count-derived reciprocal polynomial has value seventy-one at one,
after rewriting it to the independent newform certificate. -/
theorem genusFourReciprocalNumerator_eval_one :
    (genusFourReciprocalNumerator q 1 (-2) (-5) 1).eval 1 = 71 := by
  rw [genusFourReciprocalNumerator_eq_newformAtThree]
  exact P₂₅AtThree_eval_one

end

end MazurProof.RationalPointsN25QuotientZetaThree
