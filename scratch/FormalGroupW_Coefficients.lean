/-
# Downstream coefficient proofs for FormalGroupW

Proves the 4 remaining coefficient sorries via coefficient extraction
from formalAddY_eq_cube_mul, WITHOUT unfolding Dvd.dvd.choose.

Strategy: coeff_{(3,0)} of (X₀-X₁)³ * q = constantCoeff(q).
-/

import scratch.FormalGroupW

open MvPowerSeries Finsupp

namespace WeierstrassCurve.FormalGroupCoefficients

variable {R : Type*} [CommRing R]

/-- Key helper: coeff_{(3,0)} of (X₀-X₁)³ extracts constantCoeff of the quotient.

Since (X₀-X₁)³ = X₀³ - 3X₀²X₁ + 3X₀X₁² - X₁³, the only monomial with
exponent (3,0) in the expansion is X₀³ (coefficient 1). All other monomials
in (X₀-X₁)³ involve X₁, so their contribution to coeff_{(3,0)} of the product is 0. -/
private theorem coeff_30_delta_cube_mul (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (R := R) (single 0 3)
      ((X 0 - X 1 : MvPowerSeries (Fin 2) R) ^ 3 * q) =
    MvPowerSeries.constantCoeff (σ := Fin 2) q := by
  sorry

/-- The raw numerator coefficient: coeff_{(3,0)} of formalAddY is 1. -/
private theorem formalAddY_coeff_30 (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (R := R) (single 0 3) W.formalAddY = 1 := by
  sorry

/-- normalizedAddY has constant coefficient 1 (NOT -1). -/
theorem normalizedAddY_constantCoeff_eq_one (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff (σ := Fin 2) W.normalizedAddY = 1 := by
  have h := congr_arg (MvPowerSeries.coeff (R := R) (single 0 3)) W.formalAddY_eq_cube_mul
  rw [formalAddY_coeff_30, coeff_30_delta_cube_mul] at h
  exact h.symm

end WeierstrassCurve.FormalGroupCoefficients
