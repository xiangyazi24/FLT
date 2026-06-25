/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib

/-!
# Diagonal difference lemma for power series

For a univariate power series `f ∈ R⟦X⟧`, the difference
`f(X₀) - f(X₁)` (viewed in `MvPowerSeries (Fin 2) R`) is divisible
by `X₀ - X₁`.

The proof constructs an explicit quotient: its coefficient at multi-index `e`
is `PowerSeries.coeff (e 0 + e 1 + 1) f`, corresponding to the classical identity
  `f(X₀) - f(X₁) = (X₀ - X₁) · Σ_{n≥1} aₙ · Σ_{k=0}^{n-1} X₀ᵏ · X₁ⁿ⁻¹⁻ᵏ`.
-/

open Finsupp

noncomputable section

variable {R : Type*} [CommRing R]

/-- The diagonal difference quotient: for a univariate power series `f`,
this is the bivariate power series `q` such that
`f(X₀) - f(X₁) = (X₀ - X₁) * q`. Its coefficient at multi-index `e`
is `PowerSeries.coeff (e 0 + e 1 + 1) f`. -/
noncomputable def PowerSeries.diagDiffQuot (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  fun e => (PowerSeries.coeff (e 0 + e 1 + 1) : PowerSeries R →ₗ[R] R) f

@[simp]
lemma PowerSeries.diagDiffQuot_coeff (f : PowerSeries R) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e f.diagDiffQuot = PowerSeries.coeff (e 0 + e 1 + 1) f :=
  rfl

-- Fin 2 Finsupp helper lemmas
private lemma fin2_eq_single_0_iff (e : Fin 2 →₀ ℕ) :
    e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h
    have := DFunLike.congr_fun h 1
    simp only [single_apply] at this
    exact this
  · intro h; ext i; fin_cases i <;> simp [h]

private lemma fin2_eq_single_1_iff (e : Fin 2 →₀ ℕ) :
    e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
  constructor
  · intro h
    have := DFunLike.congr_fun h 0
    simp only [single_apply] at this
    exact this
  · intro h; ext i; fin_cases i <;> simp [h]

private lemma fin2_single0_le_iff (e : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) 1 ≤ e ↔ 1 ≤ e 0 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    have := h 0
    simp only [single_apply] at this
    exact this
  · intro h i; fin_cases i <;> simp_all

private lemma fin2_single1_le_iff (e : Fin 2 →₀ ℕ) :
    Finsupp.single (1 : Fin 2) 1 ≤ e ↔ 1 ≤ e 1 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    have := h 1
    simp only [single_apply] at this
    exact this
  · intro h i; fin_cases i <;> simp_all

private lemma fin2_sub_single0_0 (e : Fin 2 →₀ ℕ) :
    (e - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = e 0 - 1 := by
  rw [tsub_apply, single_eq_same]

private lemma fin2_sub_single0_1 (e : Fin 2 →₀ ℕ) :
    (e - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = e 1 := by
  simp [tsub_apply]

private lemma fin2_sub_single1_0 (e : Fin 2 →₀ ℕ) :
    (e - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = e 0 := by
  simp [tsub_apply]

private lemma fin2_sub_single1_1 (e : Fin 2 →₀ ℕ) :
    (e - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = e 1 - 1 := by
  rw [tsub_apply, single_eq_same]

private lemma PowerSeries.coeff_congr {n m : ℕ} (h : n = m) (f : PowerSeries R) :
    PowerSeries.coeff n f = PowerSeries.coeff m f :=
  congrArg (· f) (congrArg PowerSeries.coeff h)

set_option maxHeartbeats 800000 in
-- Expanding `coeff_subst_single` across 4 cases on `(e 0, e 1)` for `Fin 2`.
/-- The diagonal difference identity: `f(X₀) - f(X₁) = (X₀ - X₁) * diagDiffQuot f`.
Here `f(Xᵢ)` means `PowerSeries.subst (MvPowerSeries.X i) f`. -/
theorem PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot (f : PowerSeries R) :
    f.subst (MvPowerSeries.X (0 : Fin 2)) - f.subst (MvPowerSeries.X (1 : Fin 2)) =
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * f.diagDiffQuot := by
  classical
  apply MvPowerSeries.ext
  intro e
  change MvPowerSeries.coeff e
      (f.subst (MvPowerSeries.X 0) - f.subst (MvPowerSeries.X 1)) =
    MvPowerSeries.coeff e
      ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * f.diagDiffQuot)
  rw [map_sub, PowerSeries.coeff_subst_single, PowerSeries.coeff_subst_single,
    sub_mul, map_sub, MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, one_mul, one_mul,
    diagDiffQuot_coeff, diagDiffQuot_coeff,
    fin2_sub_single0_0, fin2_sub_single0_1, fin2_sub_single1_0, fin2_sub_single1_1]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · -- e 0 = 0, e 1 = 0
    rw [if_pos ((fin2_eq_single_0_iff e).mpr h1),
        if_pos ((fin2_eq_single_1_iff e).mpr h0),
        if_neg (by rw [fin2_single0_le_iff]; omega),
        if_neg (by rw [fin2_single1_le_iff]; omega),
        h0, h1]; ring
  · -- e 0 = 0, e 1 ≠ 0
    rw [if_neg (by rw [fin2_eq_single_0_iff]; exact h1),
        if_pos ((fin2_eq_single_1_iff e).mpr h0),
        if_neg (by rw [fin2_single0_le_iff]; omega),
        if_pos (by rw [fin2_single1_le_iff]; omega),
        zero_sub, zero_sub, neg_inj]
    exact PowerSeries.coeff_congr (by omega) f
  · -- e 0 ≠ 0, e 1 = 0
    rw [if_pos ((fin2_eq_single_0_iff e).mpr h1),
        if_neg (by rw [fin2_eq_single_1_iff]; exact h0),
        if_pos (by rw [fin2_single0_le_iff]; omega),
        if_neg (by rw [fin2_single1_le_iff]; omega),
        sub_zero, sub_zero]
    exact PowerSeries.coeff_congr (by omega) f
  · -- e 0 ≠ 0, e 1 ≠ 0
    rw [if_neg (by rw [fin2_eq_single_0_iff]; exact h1),
        if_neg (by rw [fin2_eq_single_1_iff]; exact h0),
        if_pos (by rw [fin2_single0_le_iff]; omega),
        if_pos (by rw [fin2_single1_le_iff]; omega),
        sub_self, eq_comm, sub_eq_zero]
    exact PowerSeries.coeff_congr (by omega) f

/-- The diagonal difference divisibility: `(X₀ - X₁) ∣ (f(X₀) - f(X₁))`. -/
theorem PowerSeries.X_sub_X_dvd_subst_sub_subst (f : PowerSeries R) :
    (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) :
      MvPowerSeries (Fin 2) R) ∣
      (f.subst (MvPowerSeries.X 0) - f.subst (MvPowerSeries.X 1)) :=
  ⟨f.diagDiffQuot, f.subst_X_sub_subst_X_eq_mul_diagDiffQuot⟩

end
