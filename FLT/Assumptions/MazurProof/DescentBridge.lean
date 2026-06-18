import Mathlib
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.DescentObstruction

/-!
# Bridge from the N=10 descent checks to the noncyclic exclusion
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof
namespace NoncyclicN10Bridge

abbrev RatPoints (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℚ).Point

def ContainsZ2xZ10 (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ f : (ZMod 2 × ZMod 10) →+ RatPoints E, Function.Injective f

def E20AffineEquation (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 + u ^ 2 - u

def E20DegenerateParameter (u : ℚ) : Prop :=
  u = -1 ∨ u = 0 ∨ u = 1

theorem local_obstructions_verified :
    (¬ ∃ x y z : ZMod 125,
        FLT.C20LocalObstructions.PrimitiveMod5_125 x z = true ∧
        (5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 +
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4)
    ∧
    (¬ ∃ x y z : ZMod 16,
        FLT.C20LocalObstructions.PrimitiveMod2_16 x z = true ∧
        y ^ 2 = FLT.C20LocalObstructions.Ep_dm1_rhs_plus x z) := by
  exact FLT.C20LocalObstructions.local_obstructions_verified

axiom local_obstructions_imply_E20_point_classification
    (hlocal :
      (¬ ∃ x y z : ZMod 125,
          FLT.C20LocalObstructions.PrimitiveMod5_125 x z = true ∧
          (5 : ZMod 125) * y ^ 2 =
            (25 : ZMod 125) * x ^ 4 +
            (5 : ZMod 125) * x ^ 2 * z ^ 2 -
            z ^ 4)
      ∧
      (¬ ∃ x y z : ZMod 16,
          FLT.C20LocalObstructions.PrimitiveMod2_16 x z = true ∧
          y ^ 2 = FLT.C20LocalObstructions.Ep_dm1_rhs_plus x z)) :
    ∀ u w : ℚ, E20AffineEquation u w → E20DegenerateParameter u

theorem obstruction_curve_20a4_points_degenerate :
    ∀ u w : ℚ, E20AffineEquation u w → E20DegenerateParameter u :=
  local_obstructions_imply_E20_point_classification local_obstructions_verified

axiom Z2xZ10_gives_non_degenerate_E20_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ContainsZ2xZ10 E) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u

theorem no_Z2_cross_Z10_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ RatPoints E, Function.Injective f := by
  intro hE
  rcases Z2xZ10_gives_non_degenerate_E20_point E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_20a4_points_degenerate u w hcurve)

end NoncyclicN10Bridge
end MazurProof
