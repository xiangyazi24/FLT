import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.ObstructionN14

/-! # N=14 descent bridge -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E_N14_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - 2 * u

def E_N14_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1

theorem obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u := by
  intro u w h
  exact _root_.obstruction_N14 u w h

axiom Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u

theorem no_Z2_cross_Z14_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ14_gives_non_degenerate_N14_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)

end MazurProof
