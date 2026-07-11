import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN12Defs
import FLT.Assumptions.MazurProof.KubertBridgeN12
import FLT.Assumptions.MazurProof.N12CheckedDescentBridge

/-! # N=12 descent bridge — same pattern as N=10 -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem obstruction_curve_N12_points_degenerate_of_pell_and_denominator
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (hden : RationalPointsN12.N12SquareDenominatorOneResidual) :
    ∀ u w : ℚ, E_N12_AffineEquation u w → E_N12_DegenerateParameter u := by
  intro u w h
  exact RationalPointsN12.N12_rational_points_degenerate_of_pell_and_denominator
    hpell hden u w h

theorem obstruction_curve_N12_points_degenerate_of_pell_and_no_nontrivial_denominator
    (hpell : ∀ k a b : ℤ,
      2 * k ^ 2 + 2 * k + 1 = a ^ 2 →
      6 * k ^ 2 + 6 * k + 1 = b ^ 2 →
      k = 0 ∨ k = -1)
    (hno : RationalPointsN12.N12NoNontrivialSquareDenominatorResidual) :
    ∀ u w : ℚ, E_N12_AffineEquation u w → E_N12_DegenerateParameter u := by
  intro u w h
  exact RationalPointsN12.N12_rational_points_degenerate_of_pell_and_no_nontrivial_denominator
    hpell hno u w h

theorem obstruction_curve_N12_points_degenerate :
    ∀ u w : ℚ, E_N12_AffineEquation u w → E_N12_DegenerateParameter u :=
  RationalPointsN12.checked_E_N12_degenerate_boundary_of_fullCover

theorem no_Z2_cross_Z12_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases KubertBridgeN12.bridge_N12 E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N12_points_degenerate u w hcurve)

end MazurProof
