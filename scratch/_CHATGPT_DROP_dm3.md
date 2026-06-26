# Q659 (dm3): degree-4 extraction for `(X₀ - X₁)^3 * q`

The cleanest proof is to avoid expanding all mixed terms in the coefficient computation.  For the `X₀`-axis coefficient, write

```text
(X₀ - X₁)^3 = X₀^3 + X₁ * A.
```

Then `X₁ * A * q` has zero coefficient on every pure `X₀`-axis monomial.  For the `X₁`-axis coefficient, write

```text
(X₀ - X₁)^3 = -X₁^3 + X₀ * B.
```

Then `X₀ * B * q` has zero coefficient on every pure `X₁`-axis monomial, and `-X₁^3 * q` shifts the `X₁`-axis coefficient by `3` with the minus sign.

Here is the Lean code I would add near your existing degree-3 extraction lemma.  It uses the current Mathlib API names from `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries.X_pow_eq`, `MvPowerSeries.coeff_add_monomial_mul`, and `MvPowerSeries.coeff_monomial_mul`.

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open Finsupp

namespace MvPowerSeries

section DegreeFourExtraction

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)
local notation "δ" => (X₀ - X₁)

private lemma not_e1_one_le_e0 (n : ℕ) : ¬ e₁ 1 ≤ e₀ n := by
  intro h
  have hcoord := h (1 : Fin 2)
  have h10 : 1 ≤ 0 := by
    simpa using hcoord
  exact (Nat.not_succ_le_zero 0) h10

private lemma not_e0_one_le_e1 (n : ℕ) : ¬ e₀ 1 ≤ e₁ n := by
  intro h
  have hcoord := h (0 : Fin 2)
  have h10 : 1 ≤ 0 := by
    simpa using hcoord
  exact (Nat.not_succ_le_zero 0) h10

/-- Multiplication by `X₁` kills pure `X₀`-axis coefficients. -/
private lemma coeff_axis0_X1_mul (q : S) (n : ℕ) :
    coeff R (e₀ n) (X₁ * q) = 0 := by
  classical
  have hle : ¬ e₁ 1 ≤ e₀ n := not_e1_one_le_e0 (R := R) n
  simpa [MvPowerSeries.X, hle] using
    (MvPowerSeries.coeff_monomial_mul
      (R := R) (m := e₀ n) (n := e₁ 1) (φ := q) (a := (1 : R)))

/-- Multiplication by `X₀` kills pure `X₁`-axis coefficients. -/
private lemma coeff_axis1_X0_mul (q : S) (n : ℕ) :
    coeff R (e₁ n) (X₀ * q) = 0 := by
  classical
  have hle : ¬ e₀ 1 ≤ e₁ n := not_e0_one_le_e1 (R := R) n
  simpa [MvPowerSeries.X, hle] using
    (MvPowerSeries.coeff_monomial_mul
      (R := R) (m := e₁ n) (n := e₀ 1) (φ := q) (a := (1 : R)))

/-- The pure `X₀^3` term shifts the `X₀`-axis coefficient down by `3`. -/
private lemma coeff_axis0_X0_pow3_mul (q : S) :
    coeff R (e₀ 4) (X₀ ^ 3 * q) = coeff R (e₀ 1) q := by
  classical
  simpa [MvPowerSeries.X_pow_eq, Finsupp.single_add] using
    (MvPowerSeries.coeff_add_monomial_mul
      (R := R) (m := e₀ 3) (n := e₀ 1) (φ := q) (a := (1 : R)))

/-- The pure `-X₁^3` term shifts the `X₁`-axis coefficient down by `3` and contributes a sign. -/
private lemma coeff_axis1_neg_X1_pow3_mul (q : S) :
    coeff R (e₁ 4) ((-X₁ ^ 3) * q) = - coeff R (e₁ 1) q := by
  classical
  have hmon :
      (-X₁ ^ 3 : S) = MvPowerSeries.monomial R (e₁ 3) (-1 : R) := by
    rw [MvPowerSeries.X_pow_eq]
    simpa using ((MvPowerSeries.monomial R (e₁ 3)).map_neg (1 : R)).symm
  rw [hmon]
  simpa [Finsupp.single_add, neg_mul] using
    (MvPowerSeries.coeff_add_monomial_mul
      (R := R) (m := e₁ 3) (n := e₁ 1) (φ := q) (a := (-1 : R)))

/-- Degree-4 extraction on the `X₀` axis:
`coeff_{(4,0)} ((X₀-X₁)^3*q) = coeff_{(1,0)} q`. -/
lemma coeff_single0_four_delta_cube_mul (q : S) :
    coeff R (e₀ 4) (δ ^ 3 * q) = coeff R (e₀ 1) q := by
  classical
  let A : S := -(3 : S) * X₀ ^ 2 + (3 : S) * (X₀ * X₁) - X₁ ^ 2
  have hδ : δ ^ 3 = X₀ ^ 3 + X₁ * A := by
    dsimp [A]
    ring
  rw [hδ, add_mul]
  simpa [mul_assoc, coeff_axis0_X0_pow3_mul, coeff_axis0_X1_mul]

/-- Degree-4 extraction on the `X₁` axis:
`coeff_{(0,4)} ((X₀-X₁)^3*q) = - coeff_{(0,1)} q`. -/
lemma coeff_single1_four_delta_cube_mul (q : S) :
    coeff R (e₁ 4) (δ ^ 3 * q) = - coeff R (e₁ 1) q := by
  classical
  let B : S := X₀ ^ 2 - (3 : S) * (X₀ * X₁) + (3 : S) * X₁ ^ 2
  have hδ : δ ^ 3 = -X₁ ^ 3 + X₀ * B := by
    dsimp [B]
    ring
  rw [hδ, add_mul]
  simpa [mul_assoc, coeff_axis1_neg_X1_pow3_mul, coeff_axis1_X0_mul]

end DegreeFourExtraction

end MvPowerSeries
```

## Applying this to `normalizedAddX`

Once you have the quotient equation in the orientation

```lean
hdiv : δ ^ 3 * W.normalizedAddX = W.formalAddX
```

the normalized coefficients follow by applying `coeff` to `hdiv`.

If your `choose_spec` is oriented as

```lean
W.formalAddX = δ ^ 3 * W.normalizedAddX
```

then use `.symm` when constructing `hdiv`.

A generic version, independent of the exact names in your curve namespace, is:

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open Finsupp

namespace MvPowerSeries

section ApplyDegreeFourExtraction

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)
local notation "δ" => (X₀ - X₁)

lemma normalizedAddX_coeff_X_from_cube
    {formalAddX normalizedAddX : S}
    (hdiv : δ ^ 3 * normalizedAddX = formalAddX)
    (h400 : coeff R (e₀ 4) formalAddX = -1) :
    coeff R (e₀ 1) normalizedAddX = -1 := by
  have h := congrArg (fun f : S => coeff R (e₀ 4) f) hdiv
  rw [MvPowerSeries.coeff_single0_four_delta_cube_mul] at h
  rw [h400] at h
  exact h

lemma normalizedAddX_coeff_Y_from_cube
    {formalAddX normalizedAddX : S}
    (hdiv : δ ^ 3 * normalizedAddX = formalAddX)
    (h040 : coeff R (e₁ 4) formalAddX = 1) :
    coeff R (e₁ 1) normalizedAddX = -1 := by
  have h := congrArg (fun f : S => coeff R (e₁ 4) f) hdiv
  rw [MvPowerSeries.coeff_single1_four_delta_cube_mul] at h
  rw [h040] at h
  -- h : - coeff R (e₁ 1) normalizedAddX = 1
  have h' := congrArg Neg.neg h
  simpa using h'

end ApplyDegreeFourExtraction

end MvPowerSeries
```

In your curve file, the final use should look like this, modulo the exact namespace names:

```lean
have hdiv : δ ^ 3 * W.normalizedAddX = W.formalAddX := by
  -- choose_spec may need `.symm`, depending on orientation.
  simpa [WeierstrassCurve.normalizedAddX] using
    W.formalAddX_dvd_cube.choose_spec.symm

have hx : coeff R (e₀ 1) W.normalizedAddX = -1 :=
  MvPowerSeries.normalizedAddX_coeff_X_from_cube
    (formalAddX := W.formalAddX)
    (normalizedAddX := W.normalizedAddX)
    hdiv W.formalAddX_coeff_400

have hy : coeff R (e₁ 1) W.normalizedAddX = -1 :=
  MvPowerSeries.normalizedAddX_coeff_Y_from_cube
    (formalAddX := W.formalAddX)
    (normalizedAddX := W.normalizedAddX)
    hdiv W.formalAddX_coeff_040
```

The key point is that the proof never unfolds `formalAddX_dvd_cube.choose`.  It only uses the defining product equation and extracts coefficients from it.
