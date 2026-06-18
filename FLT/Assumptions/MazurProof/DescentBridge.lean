import Mathlib
import FLT.EllipticCurve.Torsion

/-!
# N=10 descent bridge (placeholder)

Connects the native_decide local obstructions (DescentObstruction.lean) to the
noncyclic exclusion. Full version needs lake build to resolve olean dependencies.

Two narrow axioms remain:
1. local_obstructions_imply_E20_point_classification
2. Z2xZ10_gives_non_degenerate_E20_point
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E20AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - u

def E20DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

axiom obstruction_curve_20a4_points_degenerate :
    ∀ u w : ℚ, E20AffineEquation u w → E20DegenerateParameter u

axiom Z2xZ10_gives_non_degenerate_E20_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u

theorem no_Z2_cross_Z10_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ10_gives_non_degenerate_E20_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_20a4_points_degenerate u w hcurve)

end MazurProof
