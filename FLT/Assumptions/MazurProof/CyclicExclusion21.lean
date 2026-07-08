import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 21 exclusion

Order 21 = 3 · 7: put the order-7 point at the Tate origin (F7 = 0),
then show the 3-division polynomial Psi3X has no rational root (with
rational Y satisfying the curve equation) compatible with the Kubert
order-7 parametrization.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion21

noncomputable section

def F7 (b c : ℚ) : ℚ := c ^ 3 - b ^ 2 + b * c

def TateEq (b c X Y : ℚ) : Prop :=
  Y ^ 2 + (1 - c) * X * Y - b * Y = X ^ 3 - b * X ^ 2

def Psi3X (b c X : ℚ) : ℚ :=
  3 * X ^ 4 + ((1 - c) ^ 2 - 4 * b) * X ^ 3 +
    3 * b * (c - 1) * X ^ 2 + 3 * b ^ 2 * X - b ^ 3

def Obstruction21 (b c X Y : ℚ) : Prop :=
  b ≠ 0 ∧ F7 b c = 0 ∧ TateEq b c X Y ∧ Psi3X b c X = 0

theorem order21_to_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h21 : HasRationalPointOfOrder E 21) :
    ∃ b c X Y : ℚ, Obstruction21 b c X Y := by
  sorry

theorem no_obstruction21 : ¬ ∃ b c X Y : ℚ, Obstruction21 b c X Y := by
  sorry

theorem no_rational_point_of_order_21
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 21 := by
  intro h21
  exact no_obstruction21 (order21_to_tate_obstruction E h21)

end
end MazurProof.CyclicExclusion21
