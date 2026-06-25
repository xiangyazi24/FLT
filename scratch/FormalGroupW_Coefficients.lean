import scratch.FormalGroupW

open MvPowerSeries Finsupp

namespace WeierstrassCurve.FormalGroupCoefficients

variable {R : Type*} [CommRing R]

private noncomputable abbrev e30 : Fin 2 →₀ ℕ := single (0 : Fin 2) 3

private lemma not_single1_le_e30 :
    ¬ single (1 : Fin 2) 1 ≤ e30 := by
  intro h; have := h (1 : Fin 2); simp [e30] at this

private lemma coeff_e30_X1_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (R := R) e30 (X (1 : Fin 2) * q) = 0 := by
  rw [X_def, coeff_monomial_mul, if_neg not_single1_le_e30]

private lemma coeff_e30_X0_cube_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (R := R) e30 (X (0 : Fin 2) ^ 3 * q) =
      constantCoeff (σ := Fin 2) q := by
  rw [X_pow_eq, coeff_monomial_mul]
  simp [e30, coeff_zero_eq_constantCoeff_apply]

private theorem coeff_e30_delta_cube_mul (q : MvPowerSeries (Fin 2) R) :
    coeff (R := R) e30
      ((X 0 - X 1 : MvPowerSeries (Fin 2) R) ^ 3 * q) =
    constantCoeff (σ := Fin 2) q := by
  have hsplit : (X 0 - X 1 : MvPowerSeries (Fin 2) R) ^ 3 =
      X (0 : Fin 2) ^ 3 + X (1 : Fin 2) *
        (-(3 : MvPowerSeries (Fin 2) R) * X 0 ^ 2 + 3 * X 0 * X 1 - X 1 ^ 2) := by ring
  rw [hsplit, add_mul, map_add, coeff_e30_X0_cube_mul, mul_assoc, coeff_e30_X1_mul, add_zero]

/-- Raw numerator coefficient: coeff_{(3,0)} of formalAddY is 1. -/
private theorem formalAddY_coeff_e30 (W : WeierstrassCurve R) :
    coeff (R := R) e30 W.formalAddY = 1 := by
  sorry

/-- normalizedAddY has constant coefficient 1. -/
theorem normalizedAddY_constantCoeff_correct (W : WeierstrassCurve R) :
    constantCoeff (σ := Fin 2) W.normalizedAddY = 1 := by
  have h := congr_arg (coeff (R := R) e30) W.formalAddY_eq_cube_mul
  rw [formalAddY_coeff_e30, coeff_e30_delta_cube_mul] at h
  exact h.symm

end WeierstrassCurve.FormalGroupCoefficients
