/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The Weierstrass formal group: w(t) power series

For a Weierstrass curve `W` with coefficients `a₁, a₂, a₃, a₄, a₆` over a commutative ring `R`,
define the power series `w(t)` satisfying

  `w = t³ + a₁·t·w + a₂·t²·w + a₃·w² + a₄·t·w² + a₆·w³`

Equivalently, `u(t) = w(t)/t³` satisfies

  `u = 1 + a₁·t·u + a₂·t²·u + a₃·t³·u² + a₄·t⁴·u² + a₆·t⁶·u³`

with `u(0) = 1`.

## Main definitions

* `WeierstrassCurve.formalU` : the power series `u(t) ∈ R⟦X⟧` with `u(0) = 1`
* `WeierstrassCurve.formalW` : the power series `w(t) = t³ · u(t) ∈ R⟦X⟧`

## Main results

* `WeierstrassCurve.formalU_constantCoeff` : `constantCoeff u = 1`
* `WeierstrassCurve.formalU_isUnit` : `u` is a unit in `R⟦X⟧`
-/

open PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

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

end WeierstrassCurve

