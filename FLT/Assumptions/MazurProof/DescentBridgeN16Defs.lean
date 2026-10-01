import Mathlib

/-!
# Shared definitions for the N=16 descent bridge

This file contains only the obstruction-curve definitions used by the N=16
rational-points computation and descent bridge.
-/

namespace MazurProof

def E_N16_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - u

def E_N16_DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

end MazurProof
