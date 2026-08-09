import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF16Add
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF16Mul
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF16Distrib

/-!
# Complete field certificate for the level-25 `F_16` model

The expensive triple laws are imported from separate resource-bounded
modules.  This file checks the remaining small multiplication tables and
assembles all components into `IsBinaryFieldTable`.  The resulting theorem is
the semantic bridge from the executable quartic model used by the point count
to a sixteen-element field of characteristic two.
-/

namespace MazurProof.RationalPointsN25QuotientF16Field

open RationalPointsN25QuotientWeil

-- Restore finite quantifier decision procedures disabled by an upstream
-- combinatorics import.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Exhaustive certificate for commutativity of the quartic multiplication
table. -/
theorem f16_mul_comm :
    ∀ a b : F16, f16Operations.mul a b = f16Operations.mul b a := by
  exact of_decide_eq_true rfl

/-- The displayed one is a left identity for the quartic multiplication
table. -/
theorem f16_one_mul :
    ∀ a : F16, f16Operations.mul f16Operations.one a = a := by
  exact of_decide_eq_true rfl

/-- The displayed zero is left absorbing for the quartic multiplication
table. -/
theorem f16_zero_mul :
    ∀ a : F16,
      f16Operations.mul f16Operations.zero a = f16Operations.zero := by
  exact of_decide_eq_true rfl

/-- The quartic polynomial-basis operations satisfy every field-table law.
This theorem packages the split kernel certificates and the inverse theorem
from the point-count module into the exact semantic interface used there. -/
theorem f16_isBinaryFieldTable :
    IsBinaryFieldTable f16Operations f16Inv := by
  exact ⟨f16_zero_ne_one, f16_add_assoc, f16_add_comm, f16_zero_add,
    f16_add_self, f16_mul_assoc, f16_mul_comm, f16_one_mul, f16_zero_mul,
    f16_mul_add, f16_mul_inv_of_ne_zero⟩

end MazurProof.RationalPointsN25QuotientF16Field
