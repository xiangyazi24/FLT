import FLT.Assumptions.MazurProof.TorsionDefs

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
  sorry

theorem no_obstruction18 : ¬ ∃ b c X : ℚ, Obstruction18 b c X := by
  sorry

theorem no_rational_point_of_order_18
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  intro h18
  exact no_obstruction18 (order18_to_tate_obstruction E h18)

end
end MazurProof.CyclicExclusion18
