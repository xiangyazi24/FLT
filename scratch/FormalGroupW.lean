/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import scratch.DiagonalDifference

/-! # The Weierstrass formal group: w(t) power series, formal point, and formal addition

For a Weierstrass curve `W` with coefficients `a₁, a₂, a₃, a₄, a₆` over a commutative ring `R`,
define the power series `w(t)` satisfying

  `w = t³ + a₁·t·w + a₂·t²·w + a₃·w² + a₄·t·w² + a₆·w³`

Equivalently, `u(t) = w(t)/t³` satisfies

  `u = 1 + a₁·t·u + a₂·t²·u + a₃·t³·u² + a₄·t⁴·u² + a₆·t⁶·u³`

with `u(0) = 1`.

## Main definitions

* `WeierstrassCurve.formalU` : the power series `u(t) ∈ R⟦X⟧` with `u(0) = 1`
* `WeierstrassCurve.formalW` : the power series `w(t) = t³ · u(t) ∈ R⟦X⟧`
* `WeierstrassCurve.formalPoint` : the projective point `![t, -1, w(t)]` over `R⟦X⟧`
* `WeierstrassCurve.formalPointMv` : `![Xᵢ, -1, w(Xᵢ)]` over `MvPowerSeries (Fin 2) R`
* `WeierstrassCurve.formalAddXYZ` : projective addition of `P(X₀)` and `P(X₁)`

## Main results

* `WeierstrassCurve.formalU_constantCoeff` : `constantCoeff u = 1`
* `WeierstrassCurve.formalU_isUnit` : `u` is a unit in `R⟦X⟧`
* `WeierstrassCurve.formalU_eq` : `u` satisfies its defining functional equation
* `WeierstrassCurve.formalW_eq` : `w` satisfies its defining functional equation
* `WeierstrassCurve.formalPoint_equation` : `formalPoint` lies on the curve
-/

open PowerSeries Finset

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ## The power series u(t) and w(t) -/

/-- The body of the recursion defining `formalUCoeff`. -/
private noncomputable def formalUCoeffBody (W : WeierstrassCurve R) :
    (n : ℕ) → ((m : ℕ) → m < n → R) → R := fun n u =>
  match n with
  | 0 => 1
  | n + 1 =>
    W.a₁ * u n (by omega)
    + (if h : n ≥ 1 then W.a₂ * u (n - 1) (by omega) else 0)
    + (if h : n ≥ 2
       then W.a₃ * ∑ x ∈ (Finset.range (n - 1)).attach,
         have hx := Finset.mem_range.mp x.2
         u x.1 (by omega) * u (n - 2 - x.1) (by omega)
       else 0)
    + (if h : n ≥ 3
       then W.a₄ * ∑ x ∈ (Finset.range (n - 2)).attach,
         have hx := Finset.mem_range.mp x.2
         u x.1 (by omega) * u (n - 3 - x.1) (by omega)
       else 0)
    + (if h : n ≥ 5
       then W.a₆ * ∑ x ∈ (Finset.range (n - 4)).attach,
         have hx := Finset.mem_range.mp x.2
         u x.1 (by omega) *
         ∑ y ∈ (Finset.range (n - 4 - x.1)).attach,
           have hy := Finset.mem_range.mp y.2
           u y.1 (by omega) * u (n - 5 - x.1 - y.1) (by omega)
       else 0)

/-- The recursive coefficient sequence for `u(t)`, defined via well-founded recursion. -/
noncomputable def formalUCoeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFounded.fix Nat.lt_wfRel.wf W.formalUCoeffBody

theorem formalUCoeff_eq (W : WeierstrassCurve R) (n : ℕ) :
    W.formalUCoeff n = W.formalUCoeffBody n (fun m _ => W.formalUCoeff m) :=
  WellFounded.fix_eq _ _ _

@[simp]
theorem formalUCoeff_zero (W : WeierstrassCurve R) : W.formalUCoeff 0 = 1 := by
  rw [formalUCoeff_eq]; rfl

/-- The formal power series `u(t) ∈ R⟦X⟧` associated to a Weierstrass curve. -/
noncomputable def formalU (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk W.formalUCoeff

/-- The formal power series `w(t) = t³ · u(t)`, the inverse local parameter at infinity. -/
noncomputable def formalW (W : WeierstrassCurve R) : R⟦X⟧ :=
  X ^ 3 * W.formalU

@[simp]
theorem formalU_coeff (W : WeierstrassCurve R) (n : ℕ) :
    PowerSeries.coeff n W.formalU = W.formalUCoeff n :=
  PowerSeries.coeff_mk n _

/-- The constant coefficient of `u(t)` is 1. -/
@[simp]
theorem formalU_constantCoeff (W : WeierstrassCurve R) :
    constantCoeff W.formalU = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, formalU_coeff, formalUCoeff_zero]

/-- `u(t)` is a unit in `R⟦X⟧` since its constant coefficient is 1. -/
theorem formalU_isUnit (W : WeierstrassCurve R) : IsUnit W.formalU := by
  rw [isUnit_iff_constantCoeff, formalU_constantCoeff]
  exact isUnit_one

/-! ## Functional equations -/

/-- Clean form of the coefficient recursion, without `attach`. -/
theorem formalUCoeff_succ (W : WeierstrassCurve R) (n : ℕ) :
    W.formalUCoeff (n + 1) =
      W.a₁ * W.formalUCoeff n
      + (if n ≥ 1 then W.a₂ * W.formalUCoeff (n - 1) else 0)
      + (if n ≥ 2 then W.a₃ * ∑ x ∈ range (n - 1),
           W.formalUCoeff x * W.formalUCoeff (n - 2 - x) else 0)
      + (if n ≥ 3 then W.a₄ * ∑ x ∈ range (n - 2),
           W.formalUCoeff x * W.formalUCoeff (n - 3 - x) else 0)
      + (if n ≥ 5 then W.a₆ * ∑ x ∈ range (n - 4),
           W.formalUCoeff x * ∑ y ∈ range (n - 4 - x),
             W.formalUCoeff y * W.formalUCoeff (n - 5 - x - y) else 0) := by
  rw [formalUCoeff_eq]; simp only [formalUCoeffBody]
  suffices h2 : (if h : n ≥ 1 then W.a₂ * W.formalUCoeff (n - 1) else (0 : R)) =
      (if n ≥ 1 then W.a₂ * W.formalUCoeff (n - 1) else 0) by
    suffices h3 : (if h : n ≥ 2 then W.a₃ * ∑ x ∈ (Finset.range (n - 1)).attach,
        W.formalUCoeff x.1 * W.formalUCoeff (n - 2 - x.1) else (0 : R)) =
      (if n ≥ 2 then W.a₃ * ∑ x ∈ range (n - 1),
           W.formalUCoeff x * W.formalUCoeff (n - 2 - x) else 0) by
      suffices h4 : (if h : n ≥ 3 then W.a₄ * ∑ x ∈ (Finset.range (n - 2)).attach,
          W.formalUCoeff x.1 * W.formalUCoeff (n - 3 - x.1) else (0 : R)) =
        (if n ≥ 3 then W.a₄ * ∑ x ∈ range (n - 2),
             W.formalUCoeff x * W.formalUCoeff (n - 3 - x) else 0) by
        suffices h6 : (if h : n ≥ 5 then W.a₆ * ∑ x ∈ (Finset.range (n - 4)).attach,
            W.formalUCoeff x.1 * ∑ y ∈ (Finset.range (n - 4 - x.1)).attach,
              W.formalUCoeff y.1 * W.formalUCoeff (n - 5 - x.1 - y.1) else (0 : R)) =
          (if n ≥ 5 then W.a₆ * ∑ x ∈ range (n - 4),
               W.formalUCoeff x * ∑ y ∈ range (n - 4 - x),
                 W.formalUCoeff y * W.formalUCoeff (n - 5 - x - y) else 0) by
          rw [h2, h3, h4, h6]
        split <;> [skip; rfl]; congr 1
        rw [Finset.sum_attach (range (n - 4)) (fun x =>
          W.formalUCoeff x * ∑ y ∈ (range (n - 4 - x)).attach,
            W.formalUCoeff y.1 * W.formalUCoeff (n - 5 - x - y.1))]
        congr 1; ext x; congr 1
        exact Finset.sum_attach _ (fun y => W.formalUCoeff y * W.formalUCoeff (n - 5 - x - y))
      split <;> [skip; rfl]; congr 1
      exact Finset.sum_attach _ (fun x => W.formalUCoeff x * W.formalUCoeff (n - 3 - x))
    split <;> [skip; rfl]; congr 1
    exact Finset.sum_attach _ (fun x => W.formalUCoeff x * W.formalUCoeff (n - 2 - x))
  split <;> rfl

-- Helpers for the coefficient proof
private theorem coeff_C_X_pow_mul (a : R) (f : PowerSeries R) (m k : ℕ) :
    PowerSeries.coeff m (C a * X ^ k * f) =
      if k ≤ m then a * PowerSeries.coeff (m - k) f else 0 := by
  rw [show C a * X ^ k * f = C a * (X ^ k * f) from by ring, coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  split <;> simp [*]

private theorem coeff_formalU_sq (W : WeierstrassCurve R) (m : ℕ) :
    PowerSeries.coeff m (W.formalU ^ 2) =
      ∑ k ∈ range (m + 1), W.formalUCoeff k * W.formalUCoeff (m - k) := by
  rw [sq, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a W.formalU * PowerSeries.coeff b W.formalU) m]
  simp only [formalU_coeff]

private theorem coeff_formalU_cube (W : WeierstrassCurve R) (m : ℕ) :
    PowerSeries.coeff m (W.formalU ^ 3) =
      ∑ j ∈ range (m + 1), W.formalUCoeff j *
        ∑ k ∈ range (m - j + 1), W.formalUCoeff k * W.formalUCoeff (m - j - k) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, mul_comm, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a W.formalU * PowerSeries.coeff b (W.formalU ^ 2)) m]
  simp only [formalU_coeff, coeff_formalU_sq]

/-- Helper: match two conditional terms with equivalent conditions and equal values. -/
private theorem ite_match {a b : R} {p q : Prop} [Decidable p] [Decidable q]
    (hpq : p ↔ q) (heq : p → a = b) :
    (if p then a else (0 : R)) = (if q then b else 0) := by
  split
  · rw [heq (by assumption)]; rw [if_pos (hpq.mp (by assumption))]
  · rw [if_neg (by intro hq; exact absurd (hpq.mpr hq) (by assumption))]

set_option maxHeartbeats 12800000 in
/-- `u(t)` satisfies its defining functional equation:
  `u = 1 + a₁·X·u + a₂·X²·u + a₃·X³·u² + a₄·X⁴·u² + a₆·X⁶·u³`. -/
theorem formalU_eq (W : WeierstrassCurve R) :
    W.formalU = 1 + C W.a₁ * X * W.formalU + C W.a₂ * X ^ 2 * W.formalU
      + C W.a₃ * X ^ 3 * W.formalU ^ 2 + C W.a₄ * X ^ 4 * W.formalU ^ 2
      + C W.a₆ * X ^ 6 * W.formalU ^ 3 := by
  ext n
  simp only [map_add, coeff_one, formalU_coeff]
  rw [show C W.a₁ * X * W.formalU = C W.a₁ * X ^ 1 * W.formalU from by ring]
  simp only [coeff_C_X_pow_mul, formalU_coeff, coeff_formalU_sq, coeff_formalU_cube]
  cases n with
  | zero => simp [formalUCoeff_zero]
  | succ n =>
    rw [formalUCoeff_succ]
    simp only [Nat.succ_ne_zero, ite_false, zero_add, show 1 ≤ n + 1 from by omega, ite_true,
      show n + 1 - 1 = n from by omega]
    -- Align ite conditions and arithmetic inside branches.
    -- Use split_ifs to handle each combination, then have+rw for arithmetic.
    simp only [show (2 ≤ n + 1) ↔ (n ≥ 1) from by omega,
      show (3 ≤ n + 1) ↔ (n ≥ 2) from by omega,
      show (4 ≤ n + 1) ↔ (n ≥ 3) from by omega,
      show (6 ≤ n + 1) ↔ (n ≥ 5) from by omega]
    -- Now both sides have ite (n ≥ k) for k = 1, 2, 3, 5.
    -- Use split_ifs to enter each branch, then omega for arithmetic.
    split_ifs with h1 h2 h3 h4
    -- 16 cases. In each, the equation has concrete arithmetic to equate.
    -- Close impossible cases, then align arithmetic in compatible cases.
    -- Close all remaining goals: rfl, contradiction, or arithmetic alignment
    all_goals first | rfl | (exfalso; omega) | skip
    -- Goal 1: n >= 5
    · congr 1
      · congr 1; congr 1
        · -- a₃ part
          refine congr_arg (W.a₃ * ·) ?_
          refine Finset.sum_congr (by congr 1; omega) (fun x hx => by congr 1)
        · -- a₄ part
          refine congr_arg (W.a₄ * ·) ?_
          refine Finset.sum_congr (by congr 1; omega) (fun x hx => by congr 1)
      · -- a₆ part
        refine congr_arg (W.a₆ * ·) ?_
        refine Finset.sum_congr (by congr 1; omega) (fun j hj => ?_)
        refine congr_arg (W.formalUCoeff j * ·) ?_
        have hjr := Finset.mem_range.mp hj
        refine Finset.sum_congr (by congr 1; omega) (fun k hk => by congr 1)
    -- Goal 2: 3 <= n < 5
    · congr 1
      · congr 1; congr 1
        · refine congr_arg (W.a₃ * ·) ?_
          refine Finset.sum_congr (by congr 1; omega) (fun x hx => by congr 1)
        · refine congr_arg (W.a₄ * ·) ?_
          refine Finset.sum_congr (by congr 1; omega) (fun x hx => by congr 1)
    -- Goal 3: 2 <= n < 3
    · congr 1; congr 1; congr 1
      refine congr_arg (W.a₃ * ·) ?_
      refine Finset.sum_congr (by congr 1; omega) (fun x hx => by congr 1)

/-- `w(t)` satisfies its defining functional equation. Derived from `formalU_eq` by
  multiplying through by `X³`. -/
theorem formalW_eq (W : WeierstrassCurve R) :
    W.formalW = X ^ 3 + C W.a₁ * X * W.formalW + C W.a₂ * X ^ 2 * W.formalW
      + C W.a₃ * W.formalW ^ 2 + C W.a₄ * X * W.formalW ^ 2
      + C W.a₆ * W.formalW ^ 3 := by
  have hu := W.formalU_eq
  unfold formalW
  linear_combination (norm := ring) X ^ 3 * hu

/-! ## The formal point on the curve -/

section FormalPoint

/-- The projective point `![t, -1, w(t)]` on the Weierstrass curve, living in `R⟦X⟧`. -/
noncomputable def formalPoint (W : WeierstrassCurve R) : Fin 3 → PowerSeries R :=
  ![X, -1, W.formalW]

@[simp]
theorem formalPoint_x (W : WeierstrassCurve R) : W.formalPoint 0 = X := by
  simp [formalPoint]

@[simp]
theorem formalPoint_y (W : WeierstrassCurve R) : W.formalPoint 1 = -1 := by
  simp [formalPoint, Matrix.cons_val_one]

@[simp]
theorem formalPoint_z (W : WeierstrassCurve R) : W.formalPoint 2 = W.formalW := by
  simp [formalPoint, Matrix.cons_val_two]

/-- The formal point `![t, -1, w(t)]` satisfies the projective Weierstrass equation
  for the curve `W.map C` (the curve with coefficients lifted to `R⟦X⟧`). -/
theorem formalPoint_equation (W : WeierstrassCurve R) :
    (W.map (PowerSeries.C (R := R))).toProjective.Equation W.formalPoint := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [formalPoint_x, formalPoint_y, formalPoint_z, WeierstrassCurve.map]
  have h := W.formalW_eq
  linear_combination (norm := ring) h

end FormalPoint

/-! ## Two-variable formal points and projective addition -/

section FormalAddition

/-- Embed the formal point at variable `i` into `MvPowerSeries (Fin 2) R`.
  `formalPointMv W i = ![Xᵢ, -1, w(Xᵢ)]`. -/
noncomputable def formalPointMv (W : WeierstrassCurve R) (i : Fin 2) :
    Fin 3 → MvPowerSeries (Fin 2) R :=
  ![MvPowerSeries.X i, -1,
    PowerSeries.subst (MvPowerSeries.X i) W.formalW]

@[simp]
theorem formalPointMv_x (W : WeierstrassCurve R) (i : Fin 2) :
    W.formalPointMv i 0 = MvPowerSeries.X i := by
  simp [formalPointMv]

@[simp]
theorem formalPointMv_y (W : WeierstrassCurve R) (i : Fin 2) :
    W.formalPointMv i 1 = -1 := by
  simp [formalPointMv, Matrix.cons_val_one]

@[simp]
theorem formalPointMv_z (W : WeierstrassCurve R) (i : Fin 2) :
    W.formalPointMv i 2 =
      PowerSeries.subst (MvPowerSeries.X i) W.formalW := by
  simp [formalPointMv, Matrix.cons_val_two]

/-- The projective addition `addXYZ(P(X₀), P(X₁))` of the two formal points.
  The curve is lifted to `MvPowerSeries (Fin 2) R` coefficients. -/
noncomputable def formalAddXYZ (W : WeierstrassCurve R) :
    Fin 3 → MvPowerSeries (Fin 2) R :=
  (W.map (MvPowerSeries.C (σ := Fin 2))).toProjective.addXYZ
    (W.formalPointMv 0) (W.formalPointMv 1)

/-- The `X`-coordinate of the formal projective sum. -/
noncomputable def formalAddX (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddXYZ 0

/-- The `Y`-coordinate of the formal projective sum. -/
noncomputable def formalAddY (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddXYZ 1

/-- The `Z`-coordinate of the formal projective sum. -/
noncomputable def formalAddZ (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddXYZ 2

theorem formalAddXYZ_def (W : WeierstrassCurve R) :
    W.formalAddXYZ = ![W.formalAddX, W.formalAddY, W.formalAddZ] := by
  ext i; fin_cases i <;> rfl

end FormalAddition

end WeierstrassCurve

/-! ## ATOM 3: Formal group law F(t₁, t₂) -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### Substituted functional equation -/

set_option maxHeartbeats 800000 in
-- Distributing subst over add/mul/pow in the functional equation is expensive.
/-- The functional equation of `w(t)` after substituting `Xᵢ` into the MvPowerSeries ring. -/
theorem formalW_subst_eq (W : WeierstrassCurve R) (i : Fin 2) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) W.formalW =
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ 3 +
    MvPowerSeries.C W.a₁ * MvPowerSeries.X i *
      PowerSeries.subst (MvPowerSeries.X i) W.formalW +
    MvPowerSeries.C W.a₂ * (MvPowerSeries.X i) ^ 2 *
      PowerSeries.subst (MvPowerSeries.X i) W.formalW +
    MvPowerSeries.C W.a₃ * (PowerSeries.subst (MvPowerSeries.X i) W.formalW) ^ 2 +
    MvPowerSeries.C W.a₄ * MvPowerSeries.X i *
      (PowerSeries.subst (MvPowerSeries.X i) W.formalW) ^ 2 +
    MvPowerSeries.C W.a₆ * (PowerSeries.subst (MvPowerSeries.X i) W.formalW) ^ 3 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.X i
  have h := congr_arg (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R))
    (formalW_eq W)
  simp only [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha,
    PowerSeries.subst_C, PowerSeries.subst_X ha] at h
  exact h

set_option maxHeartbeats 1600000 in
-- linear_combination + ring on the Weierstrass equation with MvPowerSeries coefficients.
/-- The multivariate formal point `P(Xᵢ)` satisfies the Weierstrass equation. -/
theorem formalPointMv_equation (W : WeierstrassCurve R) (i : Fin 2) :
    (W.map (MvPowerSeries.C (σ := Fin 2))).toProjective.Equation (W.formalPointMv i) := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [WeierstrassCurve.map, formalPointMv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  have h := formalW_subst_eq W i
  linear_combination (norm := ring) h

/-! ### The addZ factoring identity -/

/-- The projective slope denominator `Px·Qz - Qx·Pz` for the two formal points. -/
noncomputable def formalDelta (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalPointMv 0 0 * W.formalPointMv 1 2 - W.formalPointMv 1 0 * W.formalPointMv 0 2

/-- Mathlib's `addZ_eq'` specialized to the formal points. -/
theorem formalAddZ_mul_ww (W : WeierstrassCurve R) :
    W.formalAddZ * (W.formalPointMv 0 2 * W.formalPointMv 1 2) = W.formalDelta ^ 3 := by
  unfold formalAddZ formalAddXYZ formalDelta
  exact WeierstrassCurve.Projective.addZ_eq'
    (W.formalPointMv_equation 0) (W.formalPointMv_equation 1)


/-- For any power series `f`, `(X₀ - X₁)` divides `f(X₀) - f(X₁)` in `MvPowerSeries (Fin 2) R`. -/
private theorem X_sub_dvd_subst_diff (f : R⟦X⟧) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣
    (PowerSeries.subst (MvPowerSeries.X 0) f -
     PowerSeries.subst (MvPowerSeries.X 1) f) :=
  PowerSeries.X_sub_X_dvd_subst_sub_subst f

/-- `formalDelta` is divisible by `(X₀ - X₁)`. -/
private theorem X_sub_dvd_formalDelta (W : WeierstrassCurve R) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣
    formalDelta W := by
  unfold formalDelta
  simp only [formalPointMv_x, formalPointMv_z]
  obtain ⟨q, hq⟩ := X_sub_dvd_subst_diff (R := R) W.formalW
  exact ⟨PowerSeries.subst (MvPowerSeries.X 1) W.formalW -
    MvPowerSeries.X 1 * q,
    by linear_combination (norm := ring) -(MvPowerSeries.X (R := R) 1) * hq⟩

/-! ### Divisibility by (X₀ - X₁)³ -/

/-- `(X₀ - X₁)³` divides `formalAddX`. -/
theorem formalAddX_dvd_cube (W : WeierstrassCurve R) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ 3 ∣ W.formalAddX :=
  sorry

/-- `(X₀ - X₁)³` divides `formalAddY`. -/
theorem formalAddY_dvd_cube (W : WeierstrassCurve R) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ 3 ∣ W.formalAddY :=
  sorry

/-- The diagonal-difference quotient for w: `w₁ - w₀ = (X₁ - X₀) · wDiffQ`. -/
private noncomputable def wDiffQ (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.diagDiffQuot W.formalW

/-- The quotient `E = w₀ - X₀ · wDiffQ`, so that `delta = (X₀-X₁) · E`. -/
private noncomputable def deltaQuot (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X 0) W.formalW -
  MvPowerSeries.X 0 * W.wDiffQ

private theorem formalDelta_eq_mul (W : WeierstrassCurve R) :
    formalDelta W = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * W.deltaQuot := by
  unfold formalDelta deltaQuot wDiffQ
  simp only [formalPointMv_x, formalPointMv_z]
  have h := PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot W.formalW
  -- h : w₀ - w₁ = (X₀ - X₁) * q
  -- Goal: X₀ * w₁ - X₁ * w₀ = (X₀ - X₁) * (w₀ - X₀ * q)
  -- RHS = X₀*w₀ - X₀²*q - X₁*w₀ + X₁*X₀*q
  -- From h: w₀ = w₁ + (X₀-X₁)*q, so X₀*w₁ = X₀*(w₀ - (X₀-X₁)*q)
  -- LHS = X₀*w₁ - X₁*w₀ = X₀*(w₀-(X₀-X₁)q) - X₁*w₀ = (X₀-X₁)*w₀ - X₀(X₀-X₁)q
  --     = (X₀-X₁)*(w₀ - X₀*q) = RHS ✓
  -- Goal: X₀w₁ - X₁w₀ = (X₀-X₁)(w₀ - X₀q)
  -- From h: w₀ - w₁ = (X₀-X₁)*q
  -- LHS - RHS = -X₀ * (w₀ - w₁ - (X₀-X₁)*q) = -X₀ * 0 = 0
  linear_combination -MvPowerSeries.X (R := R) 0 * h

-- w₀ = X₀³ · u₀ where u₀ = subst X₀ u is a unit
private theorem formalPointMv_z_eq (W : WeierstrassCurve R) (i : Fin 2) :
    W.formalPointMv i 2 = (MvPowerSeries.X i) ^ 3 *
      PowerSeries.subst (MvPowerSeries.X i) W.formalU := by
  simp only [formalPointMv_z, formalW]
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X i),
    PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
    PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

-- u₀ is a unit (since constantCoeff u = 1, and subst X₀ preserves this)
private theorem formalU_subst_isUnit (W : WeierstrassCurve R) (i : Fin 2) :
    IsUnit (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) W.formalU) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst_single]
  simp [Finsupp.single_eq_zero.mpr rfl, formalU_coeff, formalUCoeff_zero]

/-- The quotient G such that deltaQuot = X₀ · X₁ · G.
Defined as -(X₀² · diagDiffQuot(u) + (X₀+X₁) · u₁). -/
private noncomputable def deltaQuotQuot (W : WeierstrassCurve R) :
    MvPowerSeries (Fin 2) R :=
  -((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ 2 *
      PowerSeries.diagDiffQuot W.formalU +
    (MvPowerSeries.X 0 + MvPowerSeries.X 1) *
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) W.formalU)

/-- diagDiffQuot(X³u) = X₀³ · diagDiffQuot(u) + u₁ · (X₀² + X₀X₁ + X₁²).
This identity holds coefficient-by-coefficient: both sides evaluate to coeff_{e₀+e₁-2}(u)
at any multi-index (e₀,e₁) with e₀+e₁ ≥ 2, and 0 otherwise. -/
private theorem diagDiffQuot_formalW (W : WeierstrassCurve R) :
    PowerSeries.diagDiffQuot W.formalW =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ 3 *
        PowerSeries.diagDiffQuot W.formalU +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) W.formalU *
        ((MvPowerSeries.X 0) ^ 2 + MvPowerSeries.X 0 * MvPowerSeries.X 1 +
         (MvPowerSeries.X 1) ^ 2) := by
  -- Both sides of the identity (X₀-X₁) * LHS = w₀ - w₁ can be verified.
  -- We prove the factorization of diagDiffQuot(w) by the uniqueness of the quotient:
  -- (X₀-X₁) * diagDiffQuot(w) = w₀ - w₁ = X₀³u₀ - X₁³u₁
  --   = X₀³(u₀-u₁) + u₁(X₀³-X₁³)
  --   = X₀³·(X₀-X₁)·diagDiffQuot(u) + u₁·(X₀-X₁)·(X₀²+X₀X₁+X₁²)
  --   = (X₀-X₁)·(X₀³·diagDiffQuot(u) + u₁·(X₀²+X₀X₁+X₁²))
  -- Since diagDiffQuot gives the UNIQUE quotient, the two are equal.
  -- Proof: show (X₀-X₁) * RHS = w₀ - w₁, then use the factored form of LHS.
  have ha0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.X 0
  have ha1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.X 1
  have hw := PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot W.formalW
  have hu := PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot W.formalU
  -- Rewrite w = X³u in hw
  rw [show W.formalW = X ^ 3 * W.formalU from rfl,
    PowerSeries.subst_mul ha0, PowerSeries.subst_pow ha0, PowerSeries.subst_X ha0,
    PowerSeries.subst_mul ha1, PowerSeries.subst_pow ha1, PowerSeries.subst_X ha1] at hw
  -- hw : X₀³u₀ - X₁³u₁ = (X₀-X₁) · diagDiffQuot(X³u)
  -- hu : u₀ - u₁ = (X₀-X₁) · diagDiffQuot(u)
  -- Show: (X₀-X₁) · RHS = (X₀-X₁) · diagDiffQuot(X³u)
  -- By showing (X₀-X₁) · RHS = X₀³u₀ - X₁³u₁ = (X₀-X₁) · diagDiffQuot(X³u)
  -- Then cancel (X₀-X₁) using ext on the diagDiffQuot
  -- Actually, we show the two sides are equal by showing they produce the same product with (X₀-X₁)
  -- This works because diagDiffQuot is the UNIQUE element with this property (by definition/ext).
  -- More directly: both sides have the same coefficients.
  -- Both sides multiplied by (X₀-X₁) equal w₀-w₁.
  -- Since diagDiffQuot is uniquely determined (coefficient-by-coefficient),
  -- we prove: (X₀-X₁) * RHS = (X₀-X₁) * LHS, and then use ext + diagDiffQuot_coeff.
  -- Actually, since diagDiffQuot(f)(e) = coeff_{e₀+e₁+1}(f) by definition,
  -- we prove the coefficient identity directly.
  -- LHS(e) = coeff_{e₀+e₁+1}(X³u)
  -- X³u: coeff_n = coeff_{n-3}(u) for n≥3, 0 for n<3
  -- So LHS(e) = coeff_{e₀+e₁-2}(u) when e₀+e₁+1≥3, i.e. e₀+e₁≥2
  --          = 0 when e₀+e₁≤1
  -- RHS: X₀³q_u + u₁(X₀²+X₀X₁+X₁²)
  -- We showed this also equals coeff_{e₀+e₁-2}(u) in all cases.
  -- Proof by uniqueness: both produce the same value when multiplied by (X₀-X₁).
  -- More directly: use linear_combination on the (X₀-X₁)-multiplied equations.
  have hwu := PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot (R := R) W.formalU
  -- hwu : u₀ - u₁ = (X₀-X₁) · diagDiffQuot(u)
  -- Suffices: (X₀-X₁) * LHS = (X₀-X₁) * RHS
  -- This follows from: both equal w₀-w₁ = X₀³u₀ - X₁³u₁
  suffices h : (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) *
    ((X ^ 3 * W.formalU).diagDiffQuot) =
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
    (MvPowerSeries.X 0 ^ 3 * W.formalU.diagDiffQuot +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) W.formalU *
        (MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 0 * MvPowerSeries.X 1 +
         MvPowerSeries.X 1 ^ 2)) by
    -- From h and hw: (X₀-X₁) * (LHS - RHS) = 0
    -- Then: LHS - RHS has the property that (X₀-X₁) * it = 0
    -- For diagDiffQuot: coeff at e is coeff_{e₀+e₁+1}(f), so
    -- LHS(e) - RHS(e) can be computed coefficient by coefficient
    -- Actually, we use ext on diagDiffQuot coefficients directly
    -- diagDiffQuot is defined so that coeff e q = coeff_{e₀+e₁+1} f
    -- The product (X₀-X₁)*q has coeff at e:
    --   q(e-s01) - q(e-s11) = coeff_{e₀+e₁}(f) - coeff_{e₀+e₁}(f) = 0 (when both defined)
    -- This uniquely determines q, so if two elements produce the same product with (X₀-X₁),
    -- they must be equal.
    -- More concretely: (X₀-X₁) * (LHS - RHS) = 0, and looking at
    -- coeff at (e₀, 0): 0 = (LHS-RHS)(e₀-1, 0) for e₀≥1
    -- coeff at (0, e₁): 0 = -(LHS-RHS)(0, e₁-1) for e₁≥1
    -- These recursively force (LHS-RHS)(e) = 0 for all e.
    -- Since diagDiffQuot(f)(e) = coeff_{e₀+e₁+1}(f) by definition,
    -- LHS = RHS follows from the ext proof below.
    -- LHS at e: diagDiffQuot(X³u)(e) = coeff_{e₀+e₁+1}(X³u)
    -- X³u has coeff_n = coeff_{n-3}(u) for n≥3, 0 for n<3
    -- RHS at e: X₀³·diagDiffQuot(u) + u₁·(X₀²+X₀X₁+X₁²)
    -- This is a sum where each summand contributes coeff_{e₀+e₁-2}(u) when active.
    -- Both equal coeff_{e₀+e₁-2}(u) when e₀+e₁≥2, and 0 when e₀+e₁≤1.
    --
    -- But proving this by ext is very tedious with Finsupp.
    -- Instead, use that (X₀-X₁)*diff = 0 where diff = LHS-RHS.
    -- Since both diff and (X₀-X₁) are defined coefficient-by-coefficient,
    -- the multiplication constraint forces diff(e) = 0 by induction.
    -- Specifically: diff at (0,b) is determined by (X₀-X₁)*diff at (1,b) and (0,b+1),
    -- which are both 0 from h.
    -- This is the uniqueness of diagDiffQuot: (X₀-X₁)*q = f(X₀)-f(X₁) has a UNIQUE solution q.
    -- Actually, the cleanest proof: apply ext, then use diagDiffQuot_coeff on both sides.
    apply MvPowerSeries.ext; intro e
    -- LHS coeff e = coeff_{e₀+e₁+1}(X³·u) = coeff_{e₀+e₁+1}(X^3 * u)
    simp only [PowerSeries.diagDiffQuot_coeff]
    -- LHS = coeff (e 0 + e 1 + 1) (X^3 * formalU W)
    -- This is coeff_{e₀+e₁-2}(formalU W) when e₀+e₁+1 ≥ 3, i.e., e₀+e₁ ≥ 2
    -- and 0 when e₀+e₁ ≤ 1
    simp only [formalW, PowerSeries.coeff_X_pow_mul']
    -- coeff (e0+e1+1) (X^3 * u) = if 3 ≤ e0+e1+1 then coeff (e0+e1+1-3) u else 0
    -- = if e0+e1 ≥ 2 then coeff (e0+e1-2) u else 0
    -- RHS: need to evaluate the sum X₀³·q_u + u₁·(X₀²+X₀X₁+X₁²) at e
    sorry
  -- Prove h: (X₀-X₁)*LHS = (X₀-X₁)*RHS
  -- (X₀-X₁)*LHS = w₀-w₁ (= hw, reversed)
  rw [← hw]
  -- (X₀-X₁)*RHS: distribute
  -- = (X₀-X₁)(X₀³q_u) + (X₀-X₁)(u₁(X₀²+X₀X₁+X₁²))
  -- = X₀³(u₀-u₁) + u₁(X₀³-X₁³)   [using hwu and X³-Y³ factoring]
  -- = X₀³u₀ - X₁³u₁
  linear_combination (MvPowerSeries.X (R := R) 0) ^ 3 * hwu

set_option maxHeartbeats 800000 in
private theorem deltaQuot_eq_X_mul_X_mul (W : WeierstrassCurve R) :
    W.deltaQuot = MvPowerSeries.X 0 * MvPowerSeries.X 1 * W.deltaQuotQuot := by
  -- E = w₀ - X₀ · q_w
  -- q_w = X₀³q_u + u₁(X₀²+X₀X₁+X₁²)  [diagDiffQuot_formalW]
  -- E = X₀³u₀ - X₀(X₀³q_u + u₁(X₀²+X₀X₁+X₁²))
  -- = X₀³u₀ - X₀⁴q_u - X₀³u₁ - X₀²X₁u₁ - X₀X₁²u₁
  -- = X₀³(u₀-u₁) - X₀⁴q_u - X₀²X₁u₁ - X₀X₁²u₁
  -- = X₀³(X₀-X₁)q_u - X₀⁴q_u - X₀²X₁u₁ - X₀X₁²u₁
  -- = -X₀³X₁q_u - X₀²X₁u₁ - X₀X₁²u₁
  -- = -X₀X₁(X₀²q_u + X₀u₁ + X₁u₁)
  -- = X₀X₁ · deltaQuotQuot ✓
  unfold deltaQuot wDiffQ deltaQuotQuot
  have hq := diagDiffQuot_formalW W
  have hu := PowerSeries.subst_X_sub_subst_X_eq_mul_diagDiffQuot W.formalU
  have hwdef : W.formalW = X ^ 3 * W.formalU := rfl
  rw [hwdef] at hq
  have ha0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.X 0
  rw [hwdef, PowerSeries.subst_mul ha0, PowerSeries.subst_pow ha0, PowerSeries.subst_X ha0]
  rw [hq]
  -- hu : u₀ - u₁ = (X₀-X₁) · diagDiffQuot(u)
  -- Goal should now be purely algebraic
  linear_combination (MvPowerSeries.X (R := R) 0) ^ 3 * hu

-- Helper: in a domain, addZ is divisible by d³.
-- Uses: addZ * w₀w₁ = d³ * E³, E = X₀X₁G, domain cancellation.
private theorem formalAddZ_dvd_cube_of_noZeroDivisors
    {S : Type*} [CommRing S] [NoZeroDivisors S] [Nontrivial S]
    (V : WeierstrassCurve S) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) ^ 3 ∣
    V.formalAddZ := by
  -- delta = d * E, so delta³ = d³ * E³
  have hd := formalDelta_eq_mul V
  -- E = X₀ · X₁ · G
  have hE := deltaQuot_eq_X_mul_X_mul V
  -- So delta = d · X₀ · X₁ · G, delta³ = d³ · X₀³ · X₁³ · G³
  have hd3 : formalDelta V ^ 3 = (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 *
      ((MvPowerSeries.X 0) ^ 3 * (MvPowerSeries.X 1) ^ 3 *
       V.deltaQuotQuot ^ 3) := by rw [hd, hE]; ring
  -- addZ * w₀w₁ = delta³ = d³ * X₀³X₁³ * G³
  have hmul := formalAddZ_mul_ww V
  rw [hd3] at hmul
  -- w₀ = X₀³ * u₀, w₁ = X₁³ * u₁
  have hw0 := formalPointMv_z_eq V 0
  have hw1 := formalPointMv_z_eq V 1
  rw [hw0, hw1] at hmul
  -- hmul : addZ * (X₀³u₀ * X₁³u₁) = d³ * (X₀³ * X₁³ * G³)
  -- Rearrange: (addZ * u₀u₁ - d³ * G³) * X₀³X₁³ = 0
  have hrearr : (V.formalAddZ *
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) V.formalU *
       PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) V.formalU) -
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 * V.deltaQuotQuot ^ 3) *
    ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) S) ^ 3 *
     (MvPowerSeries.X (1 : Fin 2)) ^ 3) = 0 := by linear_combination hmul
  -- In a NoZeroDivisors ring, X₀³X₁³ ≠ 0
  have hX0 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) S) ≠ 0 :=
    MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _ |>.mpr
      ⟨Finsupp.single 0 1, by simp [MvPowerSeries.coeff_X]⟩
  have hX1 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) S) ≠ 0 :=
    MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _ |>.mpr
      ⟨Finsupp.single 1 1, by simp [MvPowerSeries.coeff_X]⟩
  have hX01 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) S) ^ 3 *
    (MvPowerSeries.X (1 : Fin 2)) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hX0) (pow_ne_zero 3 hX1)
  -- So the other factor is zero
  have hcancel := (mul_eq_zero.mp hrearr).resolve_right hX01
  -- addZ * u₀u₁ = d³ * G³ (from sub_eq_zero)
  have heq : V.formalAddZ *
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) V.formalU *
       PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) V.formalU) =
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 * V.deltaQuotQuot ^ 3 :=
    sub_eq_zero.mp hcancel
  -- Since u₀u₁ is a unit, addZ = d³ * G³ * (u₀u₁)⁻¹
  have hu : IsUnit (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) V.formalU *
       PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) V.formalU) :=
    (formalU_subst_isUnit V 0).mul (formalU_subst_isUnit V 1)
  -- Extract the unit
  obtain ⟨uu, huu⟩ := hu
  -- addZ * uu = d³ * G³
  rw [← huu] at heq
  -- Multiply both sides by uu⁻¹ on the right
  have hfinal : V.formalAddZ = (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 *
      (V.deltaQuotQuot ^ 3 * (↑uu⁻¹ : MvPowerSeries (Fin 2) S)) := by
    have hone : (uu : MvPowerSeries (Fin 2) S) * (↑uu⁻¹ : MvPowerSeries (Fin 2) S) = 1 :=
      Units.mul_inv uu
    have := congr_arg (· * (↑uu⁻¹ : MvPowerSeries (Fin 2) S)) heq
    rw [mul_assoc, hone, mul_one, mul_assoc] at this
    exact this
  exact ⟨V.deltaQuotQuot ^ 3 * (↑uu⁻¹ : MvPowerSeries (Fin 2) S), hfinal⟩

/-- The universal Weierstrass curve over `ℤ[a₁,...,a₆]`. -/
private noncomputable def univWeierstrassCurve : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

/-- The evaluation ring hom from the universal ring to any target. -/
private noncomputable def univEval (W : WeierstrassCurve R) :
    MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

private theorem univEval_map (W : WeierstrassCurve R) :
    univWeierstrassCurve.map (univEval W) = W := by
  ext <;> simp [univWeierstrassCurve, univEval, MvPolynomial.eval₂Hom_X']

theorem formalAddZ_dvd_cube (W : WeierstrassCurve R) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ 3 ∣ W.formalAddZ := by
  sorry

/-! ### Normalized coordinates -/

/-- The quotient of `formalAddX` by `(X₀ - X₁)³`. -/
noncomputable def normalizedAddX (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddX_dvd_cube.choose

/-- `formalAddX = (X₀ - X₁)³ · normalizedAddX`. -/
theorem formalAddX_eq_cube_mul (W : WeierstrassCurve R) :
    W.formalAddX = (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 * W.normalizedAddX :=
  W.formalAddX_dvd_cube.choose_spec

/-- The quotient of `formalAddY` by `(X₀ - X₁)³`. -/
noncomputable def normalizedAddY (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddY_dvd_cube.choose

/-- `formalAddY = (X₀ - X₁)³ · normalizedAddY`. -/
theorem formalAddY_eq_cube_mul (W : WeierstrassCurve R) :
    W.formalAddY = (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 * W.normalizedAddY :=
  W.formalAddY_dvd_cube.choose_spec

/-- The quotient of `formalAddZ` by `(X₀ - X₁)³`. -/
noncomputable def normalizedAddZ (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  W.formalAddZ_dvd_cube.choose

/-- `formalAddZ = (X₀ - X₁)³ · normalizedAddZ`. -/
theorem formalAddZ_eq_cube_mul (W : WeierstrassCurve R) :
    W.formalAddZ = (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 3 * W.normalizedAddZ :=
  W.formalAddZ_dvd_cube.choose_spec

/-! ### normalizedAddY is a unit -/

/-- The constant coefficient of `normalizedAddY` is `-1`. -/
theorem normalizedAddY_constantCoeff (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff (W.normalizedAddY) = -1 :=
  sorry

/-- `normalizedAddY` is a unit in `MvPowerSeries (Fin 2) R`. -/
theorem normalizedAddY_isUnit (W : WeierstrassCurve R) : IsUnit (W.normalizedAddY) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, normalizedAddY_constantCoeff]
  exact isUnit_one.neg

/-! ### The formal group law -/

/-- The formal group law `F(t₁, t₂)` of a Weierstrass curve, defined as
  `F = -normalizedAddX · normalizedAddY⁻¹ = t₁ + t₂ + O(deg ≥ 2)`. -/
noncomputable def formalGroupLaw (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  -W.normalizedAddX * ↑(W.normalizedAddY_isUnit.unit⁻¹)

/-- `F(0, 0) = 0`. -/
theorem formalGroupLaw_constantCoeff (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff (W.formalGroupLaw) = 0 :=
  sorry

/-- The coefficient of `t₁` in `F(t₁, t₂)` is `1`. -/
theorem formalGroupLaw_lin_coeff_X (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (W.formalGroupLaw) = 1 :=
  sorry

/-- The coefficient of `t₂` in `F(t₁, t₂)` is `1`. -/
theorem formalGroupLaw_lin_coeff_Y (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single 1 1) (W.formalGroupLaw) = 1 :=
  sorry

end WeierstrassCurve
