import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil

/-!
# Multiplicative associativity for the level-25 `F_16` model

This isolated certificate checks all `16^3` multiplication triples in the
quartic polynomial-basis table.  It is separated from the other field laws
because this is one of the two expensive reductions in the `F_16` semantic
bridge.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Exhaustive ordinary-kernel certificate for associativity of multiplication
modulo `beta^4 + beta + 1`. -/
theorem f16_mul_assoc :
    ∀ a b c : F16,
      f16Operations.mul (f16Operations.mul a b) c =
        f16Operations.mul a (f16Operations.mul b c) := by
  set_option maxHeartbeats 600000 in
    exact of_decide_eq_true rfl

end MazurProof.RationalPointsN25QuotientF16Field
