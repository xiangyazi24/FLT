/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

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
