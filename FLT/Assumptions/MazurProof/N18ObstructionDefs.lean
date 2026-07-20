import Mathlib.Data.Rat.Defs

/-!
# Obstruction18 definitions (extracted for cycle-breaking)

`Obstruction18`, `F9`, and `T2` are used by both `CyclicExclusion18` and
`N18Block5Instantiation`.  Keeping them in `CyclicExclusion18` creates an
import cycle:

  CyclicExclusion18 → N18GoodModelAssembly → N18Block5Instantiation → CyclicExclusion18

Extracting the definitions here lets both files import this leaf module instead.
-/

namespace MazurProof.CyclicExclusion18

def F9 (b c : ℚ) : ℚ := (b - c) ^ 3 + c ^ 3 * (b - c - c ^ 2)

def T2 (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

def Obstruction18 (b c X : ℚ) : Prop :=
  b ≠ 0 ∧ F9 b c = 0 ∧ T2 b c X = 0

end MazurProof.CyclicExclusion18
