import Mathlib

/-!
# Shared definitions for the N=12 descent bridge

This file contains only the obstruction-curve definitions used by the N=12
Kubert bridge and descent bridge.
-/

namespace MazurProof

def E_N12_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4

def E_N12_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

end MazurProof
