# Q656 (dm1): coefficient of the raw `negAddY` numerator

Below is the complete Lean proof I would add after `import scratch.FormalGroupW`.

The proof separates the computation into two parts:

1. a purely formal `negAddY` coefficient calculation after writing the two projective formal points as
   `![X₀, -1, X₀^3 * u₀]` and `![X₁, -1, X₁^3 * u₁]`;
2. the project-local bridge saying that the `Z`-coordinate of `W.formalPointMv i` is exactly of that form, and that the coefficient of the `X₀^3` term of the `i = 0` point is `1`.

The fourth term in Mathlib’s `Projective.negAddY` definition is the only surviving term:

```lean
P y * Q y ^ 2 * P z = (-1) * (-1)^2 * w(X₀) = -w(X₀).
```

All other terms either contain a positive power of `X₁`, or contain a power of `X₀` strictly larger than `3` after using `w(Xᵢ) = Xᵢ^3 u(Xᵢ)`.

```lean
import scratch.FormalGroupW

open Finsupp

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

/-- The exponent vector `(3,0)`. -/
private abbrev e30 : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 3

private lemma coeff_e30_X0_pow_mul
    (n : ℕ) (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ n) * q) =
      if Finsupp.single (0 : Fin 2) n ≤ e30 then
        MvPowerSeries.coeff (e30 - Finsupp.single (0 : Fin 2) n) q
      else 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]

private lemma coeff_e30_X1_pow_mul
    (n : ℕ) (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      (((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ n) * q) =
      if Finsupp.single (1 : Fin 2) n ≤ e30 then
        MvPowerSeries.coeff (e30 - Finsupp.single (1 : Fin 2) n) q
      else 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]

private lemma coeff_e30_X0_pow_X1_pow_mul
    (m n : ℕ) (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      ((((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ m) *
          ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ n)) * q) =
      if Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n ≤ e30 then
        MvPowerSeries.coeff
          (e30 - (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n)) q
      else 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq]
  rw [MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [MvPowerSeries.coeff_monomial_mul]

/-- `Z(w(Xᵢ))` has a factor `Xᵢ^3`.  This is the bridge from the projective formal
point definition `[Xᵢ, -1, w(Xᵢ)]` and `w = X^3 * u`.

If this lemma already exists in `scratch.FormalGroupW`, use that existing lemma and delete this
local bridge. -/
private lemma formalPointMv_Z_eq_X_cube_mul
    (W : WeierstrassCurve R) (i : Fin 2) :
    ∃ u : MvPowerSeries (Fin 2) R,
      (W.formalPointMv i) (2 : Fin 3) =
        ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ 3) * u := by
  refine ⟨MvPowerSeries.subst
      (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) W.formalU, ?_⟩
  have hsubst : MvPowerSeries.HasSubst
      (R := R) (S := R)
      (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) := by
    exact MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro _; simp)
  simp [WeierstrassCurve.formalPointMv, WeierstrassCurve.formalW,
    MvPowerSeries.subst_mul hsubst, MvPowerSeries.subst_pow hsubst,
    MvPowerSeries.subst_X hsubst]

/-- The coefficient of `X₀^3` in the `Z`-coordinate of the first formal point is `1`.
This is the multivariate form of `formalW_coeff_three`.

If `scratch.FormalGroupW` already has this as a named lemma, replace this bridge with that name. -/
private lemma formalPointMv_Z0_eq_X0_cube_mul_coeff
    (W : WeierstrassCurve R) :
    ∃ u : MvPowerSeries (Fin 2) R,
      (W.formalPointMv (0 : Fin 2)) (2 : Fin 3) =
        ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * u ∧
      MvPowerSeries.coeff e30
        (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * u) = 1 := by
  obtain ⟨u, hu⟩ := formalPointMv_Z_eq_X_cube_mul (W := W) (i := (0 : Fin 2))
  refine ⟨u, hu, ?_⟩
  rw [← hu]
  -- This is exactly `[X₀^3] w(X₀) = [X^3] w(X) = 1`.
  simpa [e30, WeierstrassCurve.formalPointMv, WeierstrassCurve.formalW,
    WeierstrassCurve.formalU, WeierstrassCurve.formalUCoeff_zero]
    using WeierstrassCurve.formalW_coeff_three (W := W)

/-- Pure coefficient calculation for the projective `negAddY` polynomial after substituting
`P = [X₀,-1,X₀³u₀]` and `Q = [X₁,-1,X₁³u₁]`. -/
private lemma coeff_e30_negAddY_cube_aux
    (a₁ a₂ a₃ a₄ a₆ u0 u1 : MvPowerSeries (Fin 2) R)
    (h0 : MvPowerSeries.coeff e30
      (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * u0) = 1) :
    MvPowerSeries.coeff e30
      ((⟨a₁, a₂, a₃, a₄, a₆⟩ :
          WeierstrassCurve.Projective (MvPowerSeries (Fin 2) R)).negAddY
        ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R),
          -1,
          ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * u0]
        ![(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R),
          -1,
          ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * u1]) = -1 := by
  classical
  let S := MvPowerSeries (Fin 2) R
  let X0 : S := MvPowerSeries.X (0 : Fin 2)
  let X1 : S := MvPowerSeries.X (1 : Fin 2)
  have hnorm :
      ((⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve.Projective S).negAddY
        ![X0, -1, X0 ^ 3 * u0]
        ![X1, -1, X1 ^ 3 * u1]) =
        - (X0 ^ 3 * u0)
        + ((X0 ^ 2 * X1 ^ 1) * (3 : S))
        - ((X0 ^ 1 * X1 ^ 2) * (3 : S))
        + (X1 ^ 3 * u1)
        + (X0 ^ 4 * (a₁ * u0))
        - (X1 ^ 4 * (a₁ * u1))
        + ((X0 ^ 2 * X1 ^ 3) * (a₂ * u1))
        - ((X0 ^ 3 * X1 ^ 2) * (a₂ * u0))
        - ((X0 ^ 1 * X1 ^ 4) * ((2 : S) * a₂ * u1))
        + ((X0 ^ 4 * X1 ^ 1) * ((2 : S) * a₂ * u0))
        - (X1 ^ 6 * (a₃ * u1 ^ 2))
        + (X0 ^ 6 * (a₃ * u0 ^ 2))
        - ((X0 ^ 1 * X1 ^ 6) * (a₄ * u1 ^ 2))
        + ((X0 ^ 4 * X1 ^ 3) * ((2 : S) * a₄ * u0 * u1))
        - ((X0 ^ 3 * X1 ^ 4) * ((2 : S) * a₄ * u0 * u1))
        + ((X0 ^ 6 * X1 ^ 1) * (a₄ * u0 ^ 2))
        - ((X0 ^ 3 * X1 ^ 6) * ((3 : S) * a₆ * u0 * u1 ^ 2))
        + ((X0 ^ 6 * X1 ^ 3) * ((3 : S) * a₆ * u0 ^ 2 * u1)) := by
    dsimp [X0, X1, S]
    unfold WeierstrassCurve.Projective.negAddY
    simp
    ring
  dsimp [X0, X1, S] at hnorm
  rw [hnorm]
  simp only [map_add, map_sub, map_neg]
  simp [coeff_e30_X0_pow_mul, coeff_e30_X1_pow_mul,
    coeff_e30_X0_pow_X1_pow_mul, e30, h0]

/-- Coefficient `(3,0)` of the projective raw `negAddY` numerator for the two formal points. -/
theorem coeff_e30_negAddY_formal (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single 0 3)
      ((W.map (MvPowerSeries.C (σ := Fin 2))).toProjective.negAddY
        (W.formalPointMv 0) (W.formalPointMv 1)) = -1 := by
  classical
  obtain ⟨u0, hz0, h0⟩ := formalPointMv_Z0_eq_X0_cube_mul_coeff (W := W)
  obtain ⟨u1, hz1⟩ := formalPointMv_Z_eq_X_cube_mul (W := W) (i := (1 : Fin 2))
  let S := MvPowerSeries (Fin 2) R
  let X0 : S := MvPowerSeries.X (0 : Fin 2)
  let X1 : S := MvPowerSeries.X (1 : Fin 2)
  have hP0 : W.formalPointMv (0 : Fin 2) = ![X0, -1, X0 ^ 3 * u0] := by
    ext j <;> fin_cases j <;> simp [X0, WeierstrassCurve.formalPointMv, hz0]
  have hP1 : W.formalPointMv (1 : Fin 2) = ![X1, -1, X1 ^ 3 * u1] := by
    ext j <;> fin_cases j <;> simp [X1, WeierstrassCurve.formalPointMv, hz1]
  rw [hP0, hP1]
  simpa [e30, S, X0, X1, WeierstrassCurve.toProjective, WeierstrassCurve.map] using
    coeff_e30_negAddY_cube_aux
      (a₁ := MvPowerSeries.C W.a₁)
      (a₂ := MvPowerSeries.C W.a₂)
      (a₃ := MvPowerSeries.C W.a₃)
      (a₄ := MvPowerSeries.C W.a₄)
      (a₆ := MvPowerSeries.C W.a₆)
      (u0 := u0) (u1 := u1) h0

end

end WeierstrassCurve
```
