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


private lemma fin2_equivFunOnFinite_symm_eq_self (e : Fin 2 →₀ ℕ) :
    Finsupp.equivFunOnFinite.symm ![e 0, e 1] = e := by
  ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The quotient for the diagonal-sum divisibility theorem.
Given `g : MvPowerSeries (Fin 2) R`, define `q(e) = -(∑_{i=0}^{e 0} g(i, e 0 + e 1 + 1 - i))`. -/
noncomputable def MvPowerSeries.divQuotByDiff (g : MvPowerSeries (Fin 2) R) :
    MvPowerSeries (Fin 2) R := fun e =>
  -(∑ i ∈ Finset.range (e 0 + 1),
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 + e 1 + 1 - i]) g)

@[simp]
lemma MvPowerSeries.coeff_divQuotByDiff (g : MvPowerSeries (Fin 2) R)
    (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (g.divQuotByDiff) =
      -(∑ i ∈ Finset.range (e 0 + 1),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 + e 1 + 1 - i]) g) :=
  rfl

private lemma coeff_fin2_congr (g : MvPowerSeries (Fin 2) R)
    {a b c d : ℕ} (h0 : a = c) (h1 : b = d) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![a, b]) g =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![c, d]) g := by
  congr 2; ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, *]

private lemma coeff_fin2_eq_coeff_self (g : MvPowerSeries (Fin 2) R) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![e 0, e 1]) g =
    MvPowerSeries.coeff e g := by
  rw [fin2_equivFunOnFinite_symm_eq_self]

set_option maxHeartbeats 3200000 in
/-- If the diagonal sums of a bivariate power series `g` all vanish, then `(X₀ - X₁) ∣ g`. -/
theorem MvPowerSeries.X_sub_X_dvd_of_diagSum_zero
    (g : MvPowerSeries (Fin 2) R)
    (hdiag : ∀ n, ∑ k ∈ Finset.range (n + 1),
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![k, n - k]) g = 0) :
    (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) :
      MvPowerSeries (Fin 2) R) ∣ g := by
  refine ⟨g.divQuotByDiff, MvPowerSeries.ext fun e => ?_⟩
  rw [eq_comm, sub_mul, map_sub, MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, one_mul, one_mul,
    coeff_divQuotByDiff, coeff_divQuotByDiff,
    fin2_sub_single0_0, fin2_sub_single0_1,
    fin2_sub_single1_0, fin2_sub_single1_1]
  simp only [fin2_single0_le_iff, fin2_single1_le_iff]
  split_ifs with h0 h1
  · -- Case (a≥1, b≥1): telescoping
    have hcong1 : ∑ i ∈ Finset.range (e 0 - 1 + 1),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 - 1 + e 1 + 1 - i]) g =
        ∑ i ∈ Finset.range (e 0),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 + e 1 - i]) g := by
      rw [show e 0 - 1 + 1 = e 0 from by omega]
      apply Finset.sum_congr rfl
      intro i hi
      exact coeff_fin2_congr g rfl (by have := Finset.mem_range.mp hi; omega)
    have hcong2 : ∑ i ∈ Finset.range (e 0 + 1),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 + (e 1 - 1) + 1 - i]) g =
        ∑ i ∈ Finset.range (e 0 + 1),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 + e 1 - i]) g := by
      apply Finset.sum_congr rfl
      intro i hi
      exact coeff_fin2_congr g rfl (by have := Finset.mem_range.mp hi; omega)
    rw [hcong1, hcong2, Finset.sum_range_succ,
      coeff_fin2_congr g rfl (show e 0 + e 1 - e 0 = e 1 from by omega),
      coeff_fin2_eq_coeff_self]
    ring
  · -- Case (a≥1, b=0): use diagonal vanishing
    have he1 : e 1 = 0 := by omega
    have hcong : ∑ i ∈ Finset.range (e 0 - 1 + 1),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 - 1 + e 1 + 1 - i]) g =
        ∑ i ∈ Finset.range (e 0),
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![i, e 0 - i]) g := by
      rw [show e 0 - 1 + 1 = e 0 from by omega]
      apply Finset.sum_congr rfl
      intro i hi
      exact coeff_fin2_congr g rfl (by have := Finset.mem_range.mp hi; omega)
    rw [hcong, sub_zero]
    have hd := hdiag (e 0)
    rw [Finset.sum_range_succ, Nat.sub_self] at hd
    have hlast : MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![e 0, 0]) g =
        MvPowerSeries.coeff e g := by
      rw [coeff_fin2_congr g rfl he1.symm, coeff_fin2_eq_coeff_self]
    rw [hlast] at hd
    -- hd : ∑ range e0, ... + coeff e g = 0
    -- goal: -(∑ range e0, ...) = coeff e g
    linear_combination -hd
  · -- Case (a=0, b≥1): direct from definition
    have he0 : e 0 = 0 := by omega
    rw [zero_sub]
    rw [show e 0 + 1 = 1 from by omega]
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [coeff_fin2_congr g (show 0 = e 0 from he0.symm)
        (show e 0 + (e 1 - 1) + 1 - 0 = e 1 from by omega),
      coeff_fin2_eq_coeff_self]
    ring
  · -- Case (a=0, b=0): diagonal vanishing at degree 0
    have he0 : e 0 = 0 := by omega
    have he1 : e 1 = 0 := by omega
    rw [sub_self, eq_comm]
    have hd := hdiag 0
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.zero_sub] at hd
    have hlast : MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![0, 0]) g =
        MvPowerSeries.coeff e g := by
      rw [coeff_fin2_congr g he0.symm he1.symm, coeff_fin2_eq_coeff_self]
    rw [hlast] at hd
    exact hd


variable {S : Type*} [CommRing S] [NoZeroDivisors S] [Nontrivial S]

omit [NoZeroDivisors S] [Nontrivial S] in
set_option maxHeartbeats 800000 in
private lemma mapDomain_const_fin2 (e : Fin 2 →₀ ℕ) :
    Finsupp.mapDomain (fun _ : Fin 2 => (0 : Fin 1)) e =
    Finsupp.single 0 (e 0 + e 1) := by
  classical
  simp only [Finsupp.mapDomain]
  rw [Finsupp.sum_fintype]
  · simp only [Fin.sum_univ_two, Finsupp.single_add]
  · intro; simp

omit [NoZeroDivisors S] [Nontrivial S] in
set_option maxHeartbeats 3200000 in
/-- The diagonal sum of `f` at degree `n` equals the coefficient of `single 0 n`
in `rename (fun _ => 0) f`. This bridges the diagonal-sum vanishing condition
with the kernel of the specialization map `X₀, X₁ ↦ X`. -/
private lemma diagSum_eq_coeff_rename (f : MvPowerSeries (Fin 2) S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![k, n - k]) f =
    MvPowerSeries.coeff (Finsupp.single 0 n)
      (MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) f) := by
  rw [MvPowerSeries.coeff_rename]
  classical
  set fiber := (Filter.TendstoCofinite.finite_preimage_singleton
    (Finsupp.mapDomain (fun _ : Fin 2 => (0 : Fin 1)))
    (Finsupp.single 0 n)).toFinset
  apply Finset.sum_nbij (fun k => Finsupp.equivFunOnFinite.symm ![k, n - k])
  · intro k hk
    show _ ∈ fiber
    simp only [fiber, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    rw [mapDomain_const_fin2]
    have hk' := Finset.mem_range.mp hk
    congr 1
    simp [Finsupp.equivFunOnFinite]
    omega
  · intro a _ b _ hab
    have := DFunLike.congr_fun hab 0
    simp [Finsupp.equivFunOnFinite] at this
    exact this
  · intro e he
    have he' : e ∈ fiber := he
    simp only [fiber, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at he'
    have hsum : e 0 + e 1 = n := by
      rw [mapDomain_const_fin2] at he'
      have h := DFunLike.congr_fun he' 0
      simp at h
      exact h
    refine ⟨e 0, Finset.mem_range.mpr (by omega), ?_⟩
    ext i; fin_cases i
    · simp [Finsupp.equivFunOnFinite]
    · simp [Finsupp.equivFunOnFinite]; omega
  · intro a _; rfl

set_option maxHeartbeats 6400000 in
/-- `X 0 - X 1` is prime in `MvPowerSeries (Fin 2) S` when `S` is a nontrivial
commutative ring with no zero divisors. -/
theorem MvPowerSeries.X_sub_X_prime :
    Prime (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) :
      MvPowerSeries (Fin 2) S) := by
  refine ⟨?ne_zero, ?not_unit, ?dvd_or_dvd⟩
  case ne_zero =>
    intro h
    have h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) :
          MvPowerSeries (Fin 2) S) = 0 := by
      rw [h]; simp
    rw [map_sub, MvPowerSeries.coeff_index_single_self_X] at h1
    simp only [MvPowerSeries.coeff_X] at h1
    have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
      intro heq
      have := DFunLike.congr_fun heq 0
      simp at this
    simp [hne] at h1
  case not_unit =>
    intro hu
    have hconst : (MvPowerSeries.constantCoeff :
        MvPowerSeries (Fin 2) S →+* S)
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) = 0 := by
      simp [map_sub, MvPowerSeries.constantCoeff_X]
    have hunit := hu.map (MvPowerSeries.constantCoeff :
        MvPowerSeries (Fin 2) S →+* S)
    rw [hconst] at hunit
    exact not_isUnit_zero hunit
  case dvd_or_dvd =>
    intro a b ⟨q, hab⟩
    have hρ_zero : MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1))
        (MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) :
          MvPowerSeries (Fin 2) S) = 0 := by
      simp [map_sub, MvPowerSeries.rename_X]
    have hab' : MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) a *
        MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) b = 0 := by
      calc MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) a *
          MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) b
          = MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) (a * b) := by
            rw [map_mul]
        _ = MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1))
            ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * q) := by rw [hab]
        _ = MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1))
            (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
            MvPowerSeries.rename (fun _ : Fin 2 => (0 : Fin 1)) q := by rw [map_mul]
        _ = 0 * _ := by rw [hρ_zero]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hab' with ha | hb
    · left
      have hdiag : ∀ n, ∑ k ∈ Finset.range (n + 1),
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![k, n - k]) a = 0 := by
        intro n
        rw [diagSum_eq_coeff_rename]
        rw [ha]; simp
      exact MvPowerSeries.X_sub_X_dvd_of_diagSum_zero a hdiag
    · right
      have hdiag : ∀ n, ∑ k ∈ Finset.range (n + 1),
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ![k, n - k]) b = 0 := by
        intro n
        rw [diagSum_eq_coeff_rename]
        rw [hb]; simp
      exact MvPowerSeries.X_sub_X_dvd_of_diagSum_zero b hdiag

end
