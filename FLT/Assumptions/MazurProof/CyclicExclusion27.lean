import Mathlib
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
private lemma rat_cube_eq_one (z : ℚ) (hz : z ^ 3 = 1) : z = 1 := by
  have : z ^ 3 = (1 : ℚ) ^ 3 := by simpa using hz
  exact ((show Odd 3 by decide).pow_inj).mp this

theorem fermat_cubic_rational_points_are_cusps :
    ∀ x y : ℚ, FermatCubicEquation x y → FermatCubicCusp x y := by
  intro x y h
  unfold FermatCubicEquation at h
  unfold FermatCubicCusp
  have hFLTQ : FermatLastTheoremWith ℚ 3 :=
    (fermatLastTheoremFor_iff_rat (n := 3)).mp fermatLastTheoremThree
  by_cases hx : x = 0
  · right; exact ⟨hx, rat_cube_eq_one y (by simpa [hx] using h)⟩
  · by_cases hy : y = 0
    · left; exact ⟨rat_cube_eq_one x (by simpa [hy] using h), hy⟩
    · exfalso; exact hFLTQ x y 1 hx hy (by norm_num) (by simpa using h)

theorem no_rational_point_of_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 27 := by
  intro h27
  obtain ⟨x, y, hcurve, hncusp⟩ := order27_to_fermat_cubic E h27
  exact hncusp (fermat_cubic_rational_points_are_cusps x y hcurve)

end MazurProof.CyclicExclusion27
