import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil

/-!
# Distributivity for the level-25 `F_16` model

This isolated certificate checks all `16^3` triples in the distributive law
for the quartic polynomial-basis operations.  Together with the separate
associativity certificate, it supplies the expensive part of the formal
finite-field interpretation of the point-count table.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Exhaustive ordinary-kernel certificate that multiplication distributes
over addition in the quartic polynomial-basis table. -/
theorem f16_mul_add :
    ∀ a b c : F16,
      f16Operations.mul a (f16Operations.add b c) =
        f16Operations.add (f16Operations.mul a b)
          (f16Operations.mul a c) := by
  set_option maxHeartbeats 600000 in
    exact of_decide_eq_true rfl

end MazurProof.RationalPointsN25QuotientF16Field
