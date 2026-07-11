import FLT.Assumptions.MazurProof.TateOrder18
import FLT.Assumptions.MazurProof.RationalPointsN18Descent

/-!
# Cyclic order 18 exclusion

Order 18 = 2 · 9: put the order-9 point at the Tate origin (F9 = 0),
then show the 2-division polynomial T2 has no rational root compatible
with the Kubert order-9 parametrization.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion18

noncomputable section

def F9 (b c : ℚ) : ℚ := (b - c) ^ 3 + c ^ 3 * (b - c - c ^ 2)

def T2 (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

def Obstruction18 (b c X : ℚ) : Prop :=
  b ≠ 0 ∧ F9 b c = 0 ∧ T2 b c X = 0

theorem order18_to_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h18 : HasRationalPointOfOrder E 18) :
    ∃ b c X : ℚ, Obstruction18 b c X := by
  simpa [Obstruction18, F9, T2, TateNFDivision.F9, TateNFDivision.T2] using
    TateOrder18.order18_to_tate_obstruction E h18

/-- A point of exact order 18 produces the full elementary five-descent
package on the standard hyperelliptic model of `X₁(18)`.  This is the
axiom-free front end of the remaining rational-points argument. -/
theorem order18_to_five_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h18 : HasRationalPointOfOrder E 18) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((RationalPointsN18Descent.normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2) ∨
       (RationalPointsN18Descent.normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2)) ∧
      (((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f) ∨ ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e)) ∧
      (((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
       ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) := by
  obtain ⟨b, c, X, hb, hF9, hT2⟩ :=
    TateOrder18.order18_to_tate_obstruction E h18
  obtain ⟨U, Y, hU0, hU1, hY⟩ :=
    RationalPointsN18.obstruction_to_hyperelliptic hb hF9 hT2
  exact RationalPointsN18Descent.noncuspidal_point_to_five_descent hU0 hU1 hY

theorem no_obstruction18 : ¬ ∃ b c X : ℚ, Obstruction18 b c X := by
  sorry

theorem no_rational_point_of_order_18
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  intro h18
  exact no_obstruction18 (order18_to_tate_obstruction E h18)

end
end MazurProof.CyclicExclusion18
