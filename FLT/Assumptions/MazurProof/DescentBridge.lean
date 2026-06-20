import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.ObstructionComplete
import scratch.TateZ2xZ10Reduction

/-!
# N=10 descent bridge

Connects the native_decide local obstructions (DescentObstruction.lean) to the
noncyclic exclusion. Full version needs lake build to resolve olean dependencies.

One narrow axiom remains:
1. local_obstructions_imply_E20_point_classification
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E20AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - u

def E20DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

theorem obstruction_curve_20a4_points_degenerate :
    ∀ u w : ℚ, E20AffineEquation u w → E20DegenerateParameter u := by
  intro u w h
  exact _root_.obstruction_20a4 u w h

theorem Z2xZ10_gives_non_degenerate_E20_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u := by
  simpa [E20AffineEquation, E20DegenerateParameter] using
    Scratch.TateZ2xZ10Reduction.Z2xZ10_gives_non_degenerate_E20_point E hE

theorem no_Z2_cross_Z10_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ10_gives_non_degenerate_E20_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_20a4_points_degenerate u w hcurve)

end MazurProof
