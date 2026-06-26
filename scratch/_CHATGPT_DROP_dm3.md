# Q676 (dm3): pure-`X₀` coefficient vanishing for `X₁`-supported factors

## Bottom line

The right helper family is:

```lean
coeff (single 0 n) (X₁ * f) = 0
coeff (single 0 n) (f * X₁) = 0
coeff (single 0 n) (X₁ ^ k * f) = 0       -- when `0 < k`
coeff (single 0 n) ((X₁ * g) * f) = 0
```

For substituted one-variable series, the correct theorem is **not** unconditional:

```text
coeff_{(n,0)}(subst(X₁, g) * f)
  = constantCoeff(g) * coeff_{(n,0)}(f).
```

So it vanishes exactly when `constantCoeff(g) = 0`.  For your `w₁ = subst(X₁, formalW)`, this applies because `formalW = X^3 * formalU`, hence `constantCoeff formalW = 0`.

The easiest Lean proof of the substituted version is not to expand the coefficient sum.  Instead use

```lean
constantCoeff g = 0  ⇒  PowerSeries.X ∣ g,
```

so

```text
subst(X₁, g) = X₁ * subst(X₁, g/X).
```

Then the basic `X₁`-factor lemma kills the pure `X₀` coefficient.

---

## Lean helper lemmas

This code is designed to live in a small helper namespace near your formal-group coefficient proofs.  The names `PowerSeries.X_dvd_iff`, `MvPowerSeries.X_pow_eq`, and `MvPowerSeries.coeff_monomial_mul` are the only Mathlib API names that may need small local edits if your snapshot uses different names.

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open Finsupp

namespace MvPowerSeries

section PureX0Axis

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)

/-- `X₁^k` cannot divide a pure `X₀^n` monomial when `0 < k`. -/
private lemma not_e1_pos_le_e0 {k n : ℕ} (hk : 0 < k) :
    ¬ e₁ k ≤ e₀ n := by
  intro h
  have hcoord := h (1 : Fin 2)
  have hk0 : k ≤ 0 := by
    simpa using hcoord
  omega

/-- `X₀^k` cannot divide a pure `X₁^n` monomial when `0 < k`.  This is the
symmetric helper, useful if later you need pure-`X₁` coefficients. -/
private lemma not_e0_pos_le_e1 {k n : ℕ} (hk : 0 < k) :
    ¬ e₀ k ≤ e₁ n := by
  intro h
  have hcoord := h (0 : Fin 2)
  have hk0 : k ≤ 0 := by
    simpa using hcoord
  omega

/-- A positive power of `X₁` kills every pure `X₀` coefficient. -/
lemma coeff_axis0_X1_pow_mul {k n : ℕ} (hk : 0 < k) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (X₁ ^ k * f) = 0 := by
  classical
  have hle : ¬ e₁ k ≤ e₀ n := not_e1_pos_le_e0 (R := R) hk
  simpa [MvPowerSeries.X_pow_eq, hle] using
    (MvPowerSeries.coeff_monomial_mul
      (R := R) (m := e₀ n) (n := e₁ k) (φ := f) (a := (1 : R)))

/-- Multiplication by `X₁` on the left kills every pure `X₀` coefficient. -/
lemma coeff_axis0_X1_mul (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (X₁ * f) = 0 := by
  simpa using coeff_axis0_X1_pow_mul (R := R) (k := 1) (n := n) (by omega) f

/-- Multiplication by `X₁` on the right kills every pure `X₀` coefficient. -/
lemma coeff_axis0_mul_X1 (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (f * X₁) = 0 := by
  rw [mul_comm]
  exact coeff_axis0_X1_mul (R := R) n f

/-- A visible left `X₁` factor anywhere in a product kills pure `X₀` coefficients. -/
lemma coeff_axis0_X1_factor_left (n : ℕ) (g f : S) :
    MvPowerSeries.coeff R (e₀ n) ((X₁ * g) * f) = 0 := by
  rw [mul_assoc]
  exact coeff_axis0_X1_mul (R := R) n (g * f)

/-- A visible right `X₁` factor anywhere in a product kills pure `X₀` coefficients. -/
lemma coeff_axis0_X1_factor_right (n : ℕ) (g f : S) :
    MvPowerSeries.coeff R (e₀ n) (g * (X₁ * f)) = 0 := by
  rw [mul_comm g (X₁ * f), mul_assoc]
  exact coeff_axis0_X1_mul (R := R) n (f * g)

/-- A visible positive `X₁^k` factor kills pure `X₀` coefficients. -/
lemma coeff_axis0_X1_pow_factor_left {k n : ℕ} (hk : 0 < k) (g f : S) :
    MvPowerSeries.coeff R (e₀ n) ((X₁ ^ k * g) * f) = 0 := by
  rw [mul_assoc]
  exact coeff_axis0_X1_pow_mul (R := R) (k := k) (n := n) hk (g * f)

/-- If a series is known to be divisible by `X₁`, then it kills pure `X₀`
coefficients after multiplication on the left. -/
lemma coeff_axis0_mul_of_exists_X1_factor_left
    {s : S} (hs : ∃ t : S, s = X₁ * t) (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (s * f) = 0 := by
  rcases hs with ⟨t, rfl⟩
  exact coeff_axis0_X1_factor_left (R := R) n t f

/-- Same as the previous lemma, with the `X₁`-divisible series on the right. -/
lemma coeff_axis0_mul_of_exists_X1_factor_right
    {s : S} (hs : ∃ t : S, s = X₁ * t) (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (f * s) = 0 := by
  rw [mul_comm]
  exact coeff_axis0_mul_of_exists_X1_factor_left (R := R) hs n f

end PureX0Axis

end MvPowerSeries
```

If your `coeff_monomial_mul` theorem is only stated in the shifted form

```lean
coeff (m + n) (monomial m a * f) = a * coeff n f
```

rather than the arbitrary-target form, keep the theorem statements above and prove `coeff_axis0_X1_pow_mul` from `MvPowerSeries.coeff_mul` plus `Finsupp.mem_antidiagonal`.  Everything downstream stays the same.

---

## Substitution-at-`X₁` helpers

The cleanest version is abstract over whatever substitution hom your file uses.  Let

```lean
substX1 : PowerSeries R →+* MvPowerSeries (Fin 2) R
```

be the hom that sends the univariate variable to `X₁`.

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open Finsupp

namespace MvPowerSeries

section SubstX1

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)

/-- If a one-variable power series has zero constant coefficient, then its
substitution at `X₁` is divisible by `X₁`. -/
lemma exists_X1_factor_substX1_of_constantCoeff_eq_zero
    (substX1 : PowerSeries R →+* S)
    (hX : substX1 (PowerSeries.X : PowerSeries R) = X₁)
    (g : PowerSeries R)
    (hg0 : PowerSeries.coeff R 0 g = 0) :
    ∃ t : S, substX1 g = X₁ * t := by
  classical
  have hdiv : (PowerSeries.X : PowerSeries R) ∣ g := by
    -- If your snapshot states this using `PowerSeries.constantCoeff R g = 0`,
    -- replace `hg0` by that formulation or `simpa` between the two.
    exact (PowerSeries.X_dvd_iff (R := R) (φ := g)).2 hg0
  rcases hdiv with ⟨u, hu⟩
  refine ⟨substX1 u, ?_⟩
  rw [hu, map_mul, hX]

/-- Main substituted helper: if `constantCoeff g = 0`, then
`substX1 g * f` has no pure `X₀` coefficient. -/
lemma coeff_axis0_substX1_mul_of_constantCoeff_eq_zero
    (substX1 : PowerSeries R →+* S)
    (hX : substX1 (PowerSeries.X : PowerSeries R) = X₁)
    (g : PowerSeries R) (f : S) (n : ℕ)
    (hg0 : PowerSeries.coeff R 0 g = 0) :
    MvPowerSeries.coeff R (e₀ n) (substX1 g * f) = 0 := by
  classical
  have hs : ∃ t : S, substX1 g = X₁ * t :=
    exists_X1_factor_substX1_of_constantCoeff_eq_zero
      (R := R) substX1 hX g hg0
  exact MvPowerSeries.coeff_axis0_mul_of_exists_X1_factor_left
    (R := R) hs n f

/-- Same substituted helper with `substX1 g` on the right. -/
lemma coeff_axis0_mul_substX1_of_constantCoeff_eq_zero
    (substX1 : PowerSeries R →+* S)
    (hX : substX1 (PowerSeries.X : PowerSeries R) = X₁)
    (g : PowerSeries R) (f : S) (n : ℕ)
    (hg0 : PowerSeries.coeff R 0 g = 0) :
    MvPowerSeries.coeff R (e₀ n) (f * substX1 g) = 0 := by
  rw [mul_comm]
  exact coeff_axis0_substX1_mul_of_constantCoeff_eq_zero
    (R := R) substX1 hX g f n hg0

end SubstX1

end MvPowerSeries
```

### If your project uses `PowerSeries.constantCoeff`

If your zero-constant hypothesis is written as

```lean
PowerSeries.constantCoeff R g = 0
```

instead of

```lean
PowerSeries.coeff R 0 g = 0
```

add this wrapper:

```lean
lemma coeff_axis0_substX1_mul_of_constantCoeff_eq_zero'
    {R : Type*} [CommRing R]
    (substX1 : PowerSeries R →+* MvPowerSeries (Fin 2) R)
    (hX : substX1 (PowerSeries.X : PowerSeries R)
        = (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R))
    (g : PowerSeries R) (f : MvPowerSeries (Fin 2) R) (n : ℕ)
    (hg0 : PowerSeries.constantCoeff R g = 0) :
    MvPowerSeries.coeff R (Finsupp.single (0 : Fin 2) n) (substX1 g * f) = 0 := by
  exact MvPowerSeries.coeff_axis0_substX1_mul_of_constantCoeff_eq_zero
    (R := R) substX1 hX g f n (by simpa [PowerSeries.constantCoeff] using hg0)
```

---

## Applying this to `w₁ = subst(X₁, formalW)`

For your formal group files, the application should be tiny.

First prove the constant coefficient of `formalW` is zero:

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

namespace WeierstrassCurve

section FormalWSubstX1

variable {R : Type*} [CommRing R]

/-- `formalW = X^3 * formalU`, so its constant coefficient is zero. -/
theorem formalW_constantCoeff_zero (W : WeierstrassCurve R) :
    PowerSeries.coeff R 0 W.formalW = 0 := by
  classical
  -- Use your local theorem if you already have it.  This is the standard proof.
  -- `0 < 3`, so the coefficient below degree `3` of `X^3 * formalU` is zero.
  simpa [formalW] using
    (PowerSeries.coeff_X_pow_mul_of_lt
      (R := R) (n := 3) (m := 0) (φ := W.formalU) (by omega))

end FormalWSubstX1

end WeierstrassCurve
```

Then use the substituted helper.  The following is schematic because your actual substitution hom may be named `substX1`, `subst1`, `PowerSeries.subst`, or be hidden inside `formalPointMv 1`.

```lean
namespace WeierstrassCurve

section FormalW1Axis

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)

/-- The `w`-coordinate of the second formal point kills pure `X₀` coefficients. -/
theorem coeff_axis0_formalW1_mul
    (W : WeierstrassCurve R)
    (substX1 : PowerSeries R →+* S)
    (hX : substX1 (PowerSeries.X : PowerSeries R) = X₁)
    (hW1 : W.formalW1 = substX1 W.formalW)
    (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (W.formalW1 * f) = 0 := by
  rw [hW1]
  exact MvPowerSeries.coeff_axis0_substX1_mul_of_constantCoeff_eq_zero
    (R := R) substX1 hX W.formalW f n (W.formalW_constantCoeff_zero)

/-- Same with `formalW1` on the right. -/
theorem coeff_axis0_mul_formalW1
    (W : WeierstrassCurve R)
    (substX1 : PowerSeries R →+* S)
    (hX : substX1 (PowerSeries.X : PowerSeries R) = X₁)
    (hW1 : W.formalW1 = substX1 W.formalW)
    (n : ℕ) (f : S) :
    MvPowerSeries.coeff R (e₀ n) (f * W.formalW1) = 0 := by
  rw [mul_comm]
  exact coeff_axis0_formalW1_mul W substX1 hX hW1 n f

end FormalW1Axis

end WeierstrassCurve
```

In your actual file, `hW1` should probably be just `rfl` or a `simp [formalW1, formalPointMv]` fact.

---

## Optional stronger formula

If you later need the nonzero-constant case, prove the stronger theorem:

```lean
coeff (single 0 n) (substX1 g * f)
  = PowerSeries.coeff R 0 g * coeff (single 0 n) f
```

A clean proof is to decompose

```text
g = C (coeff 0 g) + X * tail(g),
```

map by `substX1`, and use the lemmas above:

```text
substX1 g * f
  = C (coeff 0 g) * f + (X₁ * substX1 tail(g)) * f.
```

The second summand has zero pure-`X₀` coefficient, and the first contributes exactly the scalar multiple.  For the current `formalW` use case, the zero-constant version is shorter and avoids setting up `tail(g)`.
