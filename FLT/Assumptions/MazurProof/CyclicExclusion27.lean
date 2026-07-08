import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 27 exclusion via X₀(27) ≅ Fermat cubic

A rational point of order 27 gives a rational cyclic subgroup of order 27,
hence a non-cuspidal rational point on X₀(27). The classical identification
X₀(27) ≅ {x³ + y³ = 1} (the Fermat cubic) plus `fermatLastTheoremThree`
from Mathlib gives the contradiction.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion27

/-- The Fermat cubic equation x³ + y³ = 1, as the affine model of X₀(27). -/
def FermatCubicEquation (x y : ℚ) : Prop :=
  x ^ 3 + y ^ 3 = 1

/-- The cuspidal rational points on X₀(27) correspond to (1,0) and (0,1)
    on the Fermat cubic. -/
def FermatCubicCusp (x y : ℚ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1)

/-- A rational point of order 27 on E/ℚ maps to a non-cuspidal rational
    point on X₀(27), realized as the Fermat cubic. -/
axiom order27_to_fermat_cubic
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h27 : HasRationalPointOfOrder E 27) :
    ∃ x y : ℚ, FermatCubicEquation x y ∧ ¬ FermatCubicCusp x y

/-- The only rational points on x³ + y³ = 1 are (1,0) and (0,1).
    This follows from Fermat's Last Theorem for exponent 3. -/
theorem fermat_cubic_rational_points_are_cusps :
    ∀ x y : ℚ, FermatCubicEquation x y → FermatCubicCusp x y := by
  sorry

theorem no_rational_point_of_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 27 := by
  intro h27
  obtain ⟨x, y, hcurve, hncusp⟩ := order27_to_fermat_cubic E h27
  exact hncusp (fermat_cubic_rational_points_are_cusps x y hcurve)

end MazurProof.CyclicExclusion27
