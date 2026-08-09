import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil

/-!
# Additive field-table laws for the level-25 `F_16` model

The quartic polynomial-basis model is deliberately verified in small files.
This file checks the additive group laws by exhaustive ordinary-kernel
reduction.  Splitting these laws from multiplication keeps the proof terms
and elaborator memory bounded while preserving an auditable certificate.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The displayed zero and one of the quartic table are distinct. -/
theorem f16_zero_ne_one : f16Operations.zero ≠ f16Operations.one := by
  decide

/-- Exhaustive certificate for associativity of polynomial-basis addition. -/
theorem f16_add_assoc :
    ∀ a b c : F16,
      f16Operations.add (f16Operations.add a b) c =
        f16Operations.add a (f16Operations.add b c) := by
  exact of_decide_eq_true rfl

/-- Exhaustive certificate for commutativity of polynomial-basis addition. -/
theorem f16_add_comm :
    ∀ a b : F16, f16Operations.add a b = f16Operations.add b a := by
  exact of_decide_eq_true rfl

/-- The displayed zero is a left identity for the quartic addition table. -/
theorem f16_zero_add :
    ∀ a : F16, f16Operations.add f16Operations.zero a = a := by
  exact of_decide_eq_true rfl

/-- Every element is its own additive inverse, as required in
characteristic two. -/
theorem f16_add_self :
    ∀ a : F16, f16Operations.add a a = f16Operations.zero := by
  exact of_decide_eq_true rfl

end MazurProof.RationalPointsN25QuotientF16Field
