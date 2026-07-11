import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 27 exclusion via the genus-one quotient `27C1`

A rational point of order 27 gives a rational point on `X₁(27)`, hence on
its degree-three genus-one quotient `27C1` (LMFDB
`27.216.1-27.a.1.1`).  This quotient has the model `y² + y = x³`,
equivalently the Fermat cubic `x³ + y³ = 1`.  Its three rational
projective points are cusps, so its affine rational points are precisely the
two points displayed below.  Mathlib's `fermatLastTheoremThree` proves this
rational-point computation.

It is important that this is the intermediate quotient `27C1`, not
`X₀(27)`: `X₀(27)` itself has a rational noncuspidal CM point.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion27

/-- The Fermat cubic equation `x³ + y³ = 1`, as an affine model of the
level-27 genus-one quotient `27C1`. -/
def FermatCubicEquation (x y : ℚ) : Prop :=
  x ^ 3 + y ^ 3 = 1

/-- The two affine rational cusps on the Fermat model of `27C1`.  The third
rational cusp is the point at infinity. -/
def FermatCubicCusp (x y : ℚ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1)

/-- A rational point of order 27 on `E/ℚ` maps to a noncuspidal rational
point on the degree-three quotient `X₁(27) → 27C1`, realized in the
affine Fermat chart. -/
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
