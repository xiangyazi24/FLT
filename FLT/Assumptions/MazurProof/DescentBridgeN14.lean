import Mathlib
import scratch.ObstructionN14
import FLT.Assumptions.MazurProof.CyclicExclusion14

/-! # N=14 descent bridge

The noncyclic subgroup ℤ/2 × ℤ/14 is excluded by observing that it contains
a cyclic point of order 14, which contradicts `no_rational_point_of_order_14`
(proved in `CyclicExclusion14`).
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def E_N14_AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - 2 * u

def E_N14_DegenerateParameter (u : ℚ) : Prop :=
  u = -2 ∨ u = 0 ∨ u = 1

theorem obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u := by
  intro u w h
  simp only [E_N14_AffineEquation] at h
  simp only [E_N14_DegenerateParameter]
  exact _root_.obstruction_N14 u w h

/-- The injection ℤ/2 × ℤ/14 → E(ℚ) implies E has a cyclic point of order 14,
which is impossible by `no_rational_point_of_order_14`. -/
theorem Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u := by
  exfalso
  obtain ⟨f, hf⟩ := hE
  have h14 : HasRationalPointOfOrder E 14 := by
    refine ⟨f (0, 1), ?_⟩
    rw [addOrderOf_injective f hf, Prod.addOrderOf_mk,
      addOrderOf_zero, ZMod.addOrderOf_one]; rfl
  exact no_rational_point_of_order_14 E h14

theorem no_Z2_cross_Z14_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases Z2xZ14_gives_non_degenerate_N14_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)

end MazurProof
