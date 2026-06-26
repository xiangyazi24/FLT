# Q670 (dm3): coefficient `coeff (single 0 3) formalAddY = 1`

## Bottom line

Yes, you can prove this by extracting the single contributing term.  The diagonal-vanishing idea is not enough to determine the coefficient `α = coeff_{(3,0)}`, but the one-term proof is exactly the right local proof.

The proof should be organized as follows:

1. Prove the one-variable fact

```lean
coeff 3 W.formalW = 1
```

from

```lean
W.formalW = PowerSeries.X ^ 3 * W.formalU
```

and `constantCoeff W.formalU = 1`.

2. Transfer this to the first formal point:

```lean
coeff (single 0 3) w₀ = 1
```

where `w₀` is `formalW` substituted into variable `0`.

3. Prove `coeff (single 0 3) negAddY_formal = -1` by unfolding `negAddY` only enough to isolate the term

```text
P[1] * Q[1]^2 * P[2] = (-1) * 1 * w₀ = -w₀.
```

All other terms have zero `(3,0)` coefficient because they either contain an `X₁` factor, contain `w₁`, contain `X₀^r * w₀` with `r > 0` and hence need a coefficient of `formalW` below degree `3`, or have total degree too high.

4. Use

```lean
formalAddY = -negAddY_formal - C(a₁) * addX_formal - C(a₃) * addZ_formal
```

plus `coeff_{(3,0)} addX = 0` and `coeff_{(3,0)} addZ = 0`.

Then

```text
coeff formalAddY
  = -(-1) - a₁*0 - a₃*0
  = 1.
```

This is simpler than trying to run `native_decide` through all of `formalAddY`, and it still avoids hand-simplifying all 18 terms.

---

## Core coefficient lemmas

Here is the support code I would put near your existing coefficient-extraction lemmas.  The names of `formalW`, `formalU`, `formalPointMv`, and the substitution maps may need small edits to match your files, but the proof shape is stable.

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open Finsupp

namespace WeierstrassCurve

section FormalAddYCoeff

variable {R : Type*} [CommRing R]

local notation "S" => MvPowerSeries (Fin 2) R
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : S)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : S)

/-- Shorthand for the coefficient we care about. -/
private abbrev coeff30 (f : S) : R :=
  MvPowerSeries.coeff R (e₀ 3) f

/-- Multiplication by `X₁` kills pure `X₀`-axis coefficients. -/
private lemma coeff30_X1_mul (f : S) :
    coeff30 (X₁ * f) = 0 := by
  classical
  have hle : ¬ e₁ 1 ≤ e₀ 3 := by
    intro h
    have hcoord := h (1 : Fin 2)
    have : 1 ≤ 0 := by simpa using hcoord
    exact Nat.not_succ_le_zero 0 this
  simpa [coeff30, MvPowerSeries.X, hle] using
    (MvPowerSeries.coeff_monomial_mul
      (R := R) (m := e₀ 3) (n := e₁ 1) (φ := f) (a := (1 : R)))

/-- Same as `coeff30_X1_mul`, but with the `X₁` factor on the right. -/
private lemma coeff30_mul_X1 (f : S) :
    coeff30 (f * X₁) = 0 := by
  rw [mul_comm]
  exact coeff30_X1_mul f

/-- Constants pull out of the `(3,0)` coefficient. -/
private lemma coeff30_C_mul (a : R) (f : S) :
    coeff30 ((MvPowerSeries.C R a) * f) = a * coeff30 f := by
  classical
  -- If your local API has this exact lemma, this is a one-line `simpa`.
  simpa [coeff30] using
    (MvPowerSeries.coeff_C_mul (R := R) (a := a) (n := e₀ 3) (φ := f))

private lemma coeff30_mul_C (a : R) (f : S) :
    coeff30 (f * (MvPowerSeries.C R a)) = coeff30 f * a := by
  rw [mul_comm]
  simpa [mul_comm] using coeff30_C_mul (R := R) a f
```

If your Mathlib snapshot does not have `MvPowerSeries.coeff_C_mul`, prove it from `MvPowerSeries.coeff_mul`; the antidiagonal of `e₀ 3` has many elements, but all terms vanish because `C a` has only coefficient `0` nonzero.

---

## One-variable `formalW` coefficient

This is the easy part.  The key is to prove both the degree-`3` coefficient and the lower-degree vanishings, because the latter kill terms like `X₀ * w₀` and `X₀^2 * w₀` when extracting coefficient `(3,0)`.

```lean
/-- `formalU` has constant coefficient `1`. -/
private lemma formalU_constantCoeff (W : WeierstrassCurve R) :
    PowerSeries.coeff R 0 W.formalU = 1 := by
  -- `formalU = PowerSeries.mk W.formalUCoeff` and `formalUCoeff 0 = 1`.
  simpa [formalU, formalUCoeff]

/-- Since `formalW = X^3 * formalU`, its degree-3 coefficient is `1`. -/
theorem formalW_coeff_three (W : WeierstrassCurve R) :
    PowerSeries.coeff R 3 W.formalW = 1 := by
  classical
  -- Use your local lemma name `coeff_X_pow_mul'`.
  -- The coefficient at degree `3 + 0` of `X^3 * formalU` is `coeff 0 formalU`.
  simpa [formalW, formalU_constantCoeff W] using
    (PowerSeries.coeff_X_pow_mul'
      (R := R) (n := 3) (m := 0) (φ := W.formalU))

/-- All coefficients of `formalW` below degree `3` vanish. -/
theorem formalW_coeff_lt_three (W : WeierstrassCurve R) {n : ℕ} (hn : n < 3) :
    PowerSeries.coeff R n W.formalW = 0 := by
  classical
  -- This is the complementary form of the same `X^3 * formalU` shift lemma.
  -- Use your local `coeff_X_pow_mul_of_lt`, or prove from coefficient support.
  simpa [formalW] using
    (PowerSeries.coeff_X_pow_mul_of_lt
      (R := R) (n := 3) (m := n) (φ := W.formalU) hn)
```

If your file already has a lemma like `formalW_eq_X_pow_three_mul_formalU`, use that instead of unfolding `formalW`.

---

## Axis substitution lemmas for `w₀` and `w₁`

Let `w₀` be `formalW` inserted in variable `0`, and `w₁` be `formalW` inserted in variable `1`.  Your project probably already has these as components of `formalPointMv 0` and `formalPointMv 1`.

The only facts needed are:

```lean
/-- The `w`-coordinate of the first formal point has `(3,0)` coefficient `1`. -/
theorem formalW0_coeff30 (W : WeierstrassCurve R) :
    coeff30 W.formalW0 = 1 := by
  -- Here `formalW0` means `formalW` substituted along `X ↦ X₀`.
  -- Replace `formalW0` and `coeff_subst0` by your local names.
  simpa [coeff30, formalW0] using
    (coeff_subst0_powerSeries
      (R := R) (n := 3) (f := W.formalW) ▸ W.formalW_coeff_three)

/-- Lower axis coefficients of `w₀` vanish below degree `3`. -/
theorem formalW0_coeff_lt_three (W : WeierstrassCurve R) {n : ℕ} (hn : n < 3) :
    MvPowerSeries.coeff R (e₀ n) W.formalW0 = 0 := by
  simpa [formalW0] using
    (coeff_subst0_powerSeries
      (R := R) (n := n) (f := W.formalW) ▸ W.formalW_coeff_lt_three hn)

/-- The second formal point has no pure `X₀`-axis degree-3 coefficient. -/
theorem formalW1_coeff30 (W : WeierstrassCurve R) :
    coeff30 W.formalW1 = 0 := by
  -- `formalW1` only involves `X₁`; its `(3,0)` coefficient is zero.
  -- Replace by your local substitution lemma.
  simpa [coeff30, formalW1]
```

In many developments, these are just `simp` after unfolding `formalPointMv` and the two substitution maps.

---

## Killing `X₀^r * w₀` terms

This is the lemma that makes the “one contributing term” proof painless.

```lean
/-- If a positive power of `X₀` multiplies `w₀`, then the `(3,0)` coefficient
vanishes, because it asks for a coefficient of `formalW` below degree `3`. -/
private lemma coeff30_X0_pow_mul_formalW0_eq_zero
    (W : WeierstrassCurve R) {r : ℕ} (hr : 0 < r) :
    coeff30 (X₀ ^ r * W.formalW0) = 0 := by
  classical
  by_cases hle : r ≤ 3
  · let k : ℕ := 3 - r
    have hk : k < 3 := by
      dsimp [k]
      omega
    have hadd : e₀ r + e₀ k = e₀ 3 := by
      ext i
      fin_cases i <;> simp [k]
      omega
    -- Coefficient shift by the monomial `X₀^r`.
    -- Replace the `X_pow_eq`/`coeff_add_monomial_mul` line by your local version.
    have hshift :
        coeff30 (X₀ ^ r * W.formalW0)
          = MvPowerSeries.coeff R (e₀ k) W.formalW0 := by
      simpa [coeff30, MvPowerSeries.X_pow_eq, hadd] using
        (MvPowerSeries.coeff_add_monomial_mul
          (R := R) (m := e₀ r) (n := e₀ k)
          (φ := W.formalW0) (a := (1 : R)))
    rw [hshift]
    exact formalW0_coeff_lt_three W hk
  · -- If `r > 3`, then `X₀^r` cannot divide `X₀^3`.
    have hnot : ¬ e₀ r ≤ e₀ 3 := by
      intro h
      have hcoord := h (0 : Fin 2)
      have : r ≤ 3 := by simpa using hcoord
      exact hle this
    simpa [coeff30, MvPowerSeries.X_pow_eq, hnot] using
      (MvPowerSeries.coeff_monomial_mul
        (R := R) (m := e₀ 3) (n := e₀ r)
        (φ := W.formalW0) (a := (1 : R)))
```

You usually only need `r = 1`, `2`, or `3`, so if this general lemma is annoying, prove the three special cases directly.

---

## The one-term proof for `negAddY_formal`

The best way to make Lean see the one-term contribution is to prove a coefficient-level split lemma.  You do not need to state a huge equality of power series; state that after applying `coeff30`, the full `negAddY` expression equals the coefficient of the single term.

The term is:

```lean
P[1] * Q[1]^2 * P[2]
```

where, for formal points,

```lean
P[1] = -1,
Q[1] = -1,
P[2] = w₀.
```

Hence the term is `-w₀`.

```lean
/-- The only contribution to `coeff (single 0 3)` of `negAddY` is
`P[1] * Q[1]^2 * P[2] = -w₀`. -/
private lemma negAddY_formal_coeff30_only_term (W : WeierstrassCurve R) :
    coeff30 W.negAddY_formal
      = coeff30
          ((W.formalPointMv 0 1) * (W.formalPointMv 1 1)^2 * (W.formalPointMv 0 2)) := by
  classical
  -- This is the only place where you unfold the 18-term `negAddY` formula.
  -- After unfolding, `simp` should kill all non-contributing terms using:
  --   * `coeff30_X1_mul`, `coeff30_mul_X1`
  --   * `formalW1_coeff30`
  --   * `coeff30_X0_pow_mul_formalW0_eq_zero`
  --   * coefficient add/sub/neg/mul-by-constant lemmas
  --   * min-degree facts for terms with `addX`/`addZ`, if they occur here
  unfold negAddY_formal
  unfold negAddY
  simp only [
    coeff30,
    MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_sub,
    MvPowerSeries.coeff_neg,
    coeff30_X1_mul,
    coeff30_mul_X1,
    formalW1_coeff30,
    coeff30_X0_pow_mul_formalW0_eq_zero,
    formalPointMv
  ]
  ring

/-- The coefficient of `negAddY` at `(3,0)` is `-1`. -/
theorem negAddY_formal_coeff30 (W : WeierstrassCurve R) :
    coeff30 W.negAddY_formal = -1 := by
  classical
  rw [negAddY_formal_coeff30_only_term W]

  -- Evaluate the single contributing term.
  have hterm :
      (W.formalPointMv 0 1) * (W.formalPointMv 1 1)^2 * (W.formalPointMv 0 2)
        = - W.formalW0 := by
    -- Replace the simp names by your local component lemmas, e.g.
    --   formalPointMv_Y, formalPointMv_Z, formalW0.
    simp [formalPointMv, formalW0]

  rw [hterm]
  simp [coeff30, formalW0_coeff30 W]
```

The important thing is that `negAddY_formal_coeff30_only_term` is allowed to unfold the 18-term definition, but it does **not** require you to reason about 18 terms manually.  Every non-contributing term dies by a small reusable coefficient lemma.

If `simp` does not kill all terms in one shot, do this instead:

```lean
  rw [negAddY_formal_expanded]
  repeat rw [MvPowerSeries.coeff_add]
  repeat rw [MvPowerSeries.coeff_sub]
  repeat rw [MvPowerSeries.coeff_neg]
  simp [
    coeff30_X1_mul,
    coeff30_mul_X1,
    formalW1_coeff30,
    coeff30_X0_pow_mul_formalW0_eq_zero,
    formalPointMv,
    formalW0_coeff30,
    formalW0_coeff_lt_three
  ]
  ring
```

That is still a one-term extraction proof: the proof engine sees the 18 terms, but all except `-w₀` are eliminated by generic lemmas.

---

## `formalAddY_coeff_e30`

Now prove the numerator coefficient.

```lean
/-- The raw numerator coefficient needed for `normalizedAddY_constantCoeff`. -/
theorem formalAddY_coeff_e30 (W : WeierstrassCurve R) :
    MvPowerSeries.coeff R (e₀ 3) W.formalAddY = 1 := by
  classical

  -- Use `addY` plus `negY_eq`.
  have hdef :
      W.formalAddY
        = - W.negAddY_formal
          - (MvPowerSeries.C R W.a₁) * W.formalAddX
          - (MvPowerSeries.C R W.a₃) * W.formalAddZ := by
    -- Depending on the local orientation of `negY_eq`, this may need `.symm`.
    -- The mapped coefficients are `(W.map C).a₁ = C W.a₁`, etc.; `simp` should close.
    simp [formalAddY, addY, negY_eq, map_weierstrassCurve, formalAddX, formalAddZ]

  have hX : MvPowerSeries.coeff R (e₀ 3) W.formalAddX = 0 := by
    -- Your min-degree-4 theorem for `formalAddX`.
    exact W.formalAddX_coeff_e30

  have hZ : MvPowerSeries.coeff R (e₀ 3) W.formalAddZ = 0 := by
    -- Your min-degree-6 theorem for `formalAddZ`.
    exact W.formalAddZ_coeff_e30

  rw [hdef]
  simp [
    coeff30,
    MvPowerSeries.coeff_neg,
    MvPowerSeries.coeff_sub,
    coeff30_C_mul,
    negAddY_formal_coeff30 W,
    hX,
    hZ
  ]
```

If the last `simp` leaves ring arithmetic like `-(-1) - W.a₁ * 0 - W.a₃ * 0`, finish with:

```lean
  ring
```

or:

```lean
  norm_num
```

---

## Final use: `normalizedAddY_constantCoeff`

With your existing extraction lemma

```lean
coeff (single 0 3) ((X₀ - X₁)^3 * q) = constantCoeff q
```

the normalized result is short.

```lean
/-- The constant coefficient of `normalizedAddY` is `1`. -/
theorem normalizedAddY_constantCoeff (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff R W.normalizedAddY = 1 := by
  classical

  local notation "δ" => (X₀ - X₁)

  have hdiv : W.formalAddY = δ ^ 3 * W.normalizedAddY := by
    -- Use the orientation supplied by your `choose_spec`.
    simpa [normalizedAddY] using W.formalAddY_dvd_cube.choose_spec

  calc
    MvPowerSeries.constantCoeff R W.normalizedAddY
        = MvPowerSeries.coeff R (e₀ 3) (δ ^ 3 * W.normalizedAddY) := by
            simpa using
              (coeff_e30_delta_cube_mul
                (R := R) (q := W.normalizedAddY)).symm
    _ = MvPowerSeries.coeff R (e₀ 3) W.formalAddY := by
            rw [← hdiv]
    _ = 1 := formalAddY_coeff_e30 W
```

If your `choose_spec` is oriented as

```lean
δ ^ 3 * W.normalizedAddY = W.formalAddY
```

then change the product equation to:

```lean
  have hdiv : δ ^ 3 * W.normalizedAddY = W.formalAddY := by
    simpa [normalizedAddY] using W.formalAddY_dvd_cube.choose_spec
```

and the middle line becomes:

```lean
    _ = MvPowerSeries.coeff R (e₀ 3) W.formalAddY := by
            rw [hdiv]
```

---

## Why this is better than the universal computation here

The universal-ring proof is still valid, but for this coefficient it is probably heavier than necessary.  You only need one coefficient of `negAddY`, and only one term contributes to that coefficient.  The proof above uses a single unfold of `negAddY`, then generic vanishing lemmas eliminate the rest.

So the practical answer is:

```text
Yes, prove it by extracting the single term `P[1] * Q[1]^2 * P[2]`.
Do not use diagonal vanishing to identify the coefficient.
Do not compute the quotient `normalizedAddY`.
Use `choose_spec` only after the raw numerator coefficient is proved.
```
