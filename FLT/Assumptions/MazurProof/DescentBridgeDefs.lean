import Mathlib

/-!
# Shared definitions for the N=10 descent bridge

This file contains only the elementary obstruction-curve definitions used by
the N=10 Kubert bridge and the rational-points computation.  Keeping these
definitions separate avoids importing the old axiom seam when proving the
bridge from narrower inputs.
-/

namespace MazurProof

def E20AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - u

def E20DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

end MazurProof
