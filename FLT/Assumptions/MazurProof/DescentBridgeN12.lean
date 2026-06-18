import Mathlib
import FLT.EllipticCurve.Torsion

/-! # N=12 descent bridge — same pattern as N=10 -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E_N12_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4

def E_N12_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

axiom obstruction_curve_N12_points_degenerate :
    ∀ u w : ℚ, E_N12_AffineEquation u w → E_N12_DegenerateParameter u

axiom Z2xZ12_gives_non_degenerate_N12_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u

theorem no_Z2_cross_Z12_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ12_gives_non_degenerate_N12_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N12_points_degenerate u w hcurve)

end MazurProof
