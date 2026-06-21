import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.ObstructionN16
import scratch.DischargeN16

/-! # N=16 descent bridge -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E_N16_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - u

def E_N16_DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

theorem obstruction_curve_N16_points_degenerate :
    ∀ u w : ℚ, E_N16_AffineEquation u w → E_N16_DegenerateParameter u := by
  intro u w h
  exact _root_.obstruction_N16 u w h

theorem Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u := by
  simpa [E_N16_AffineEquation, E_N16_DegenerateParameter] using
    Scratch.DischargeN16.Z2xZ16_gives_non_degenerate_N16_point E hE

theorem no_Z2_cross_Z16_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ16_gives_non_degenerate_N16_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N16_points_degenerate u w hcurve)

end MazurProof
