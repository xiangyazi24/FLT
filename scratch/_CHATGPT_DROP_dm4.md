# Q657 (dm4): `coeff (single 0 3) formalAddX = 0`

## Executive answer

For this coefficient, the direct `addX`-unfolding proof is the right one.  Do **not** try to deduce it from the `formalAddY` identity: that only gives the linear combination

```text
a₁ * coeff₍₃,₀₎ addX + a₃ * coeff₍₃,₀₎ addZ = 0,
```

and extracting the two coefficients separately would require a universal/free-coefficient argument that is much heavier than the target.

A Lean-friendly proof should exploit the fact that the requested monomial is the **pure `X₀` axis monomial** `X₀³`.  After substituting

```text
P = [X₀, -1, w₀],     Q = [X₁, -1, w₁]
w₀ = w(X₀),           w₁ = w(X₁),
```

almost every term in `Projective.addX` has either an explicit factor `X₁` or a factor `w₁`; both have zero pure-`X₀`-axis coefficients.  The only term without `X₁` or `w₁` is

```text
- X₀ * w₀,
```

and its `X₀³` coefficient is the `X₀²` coefficient of `w₀`, which is zero because `w(t)` starts with `t³`.

So for the axis coefficient `X₀³`, the proof needs only:

```lean
coeff (single 0 2) w₀ = 0
∀ n, coeff (single 0 n) w₁ = 0
∀ n, coeff (single 0 n) X₁ = 0
```

plus closure of the pure-axis-zero property under multiplication.

---

## The addX normal form to use

After unfolding the Mathlib formula for projective `addX`, the formal-point substitution gives this expression:

```text
formalAddX W
  = - X₀ * w₀
    + X₁ * w₁
    - 2 * X₀ * w₁
    + 2 * X₁ * w₀
    + a₁ * X₀^2 * w₁
    - a₁ * X₁^2 * w₀
    + a₂ * X₀^2 * X₁ * w₁
    - a₂ * X₀ * X₁^2 * w₀
    + a₃ * X₀ * w₁^2
    - a₃ * X₁ * w₀^2
    + 2 * a₃ * X₀ * w₀ * w₁
    - 2 * a₃ * X₁ * w₀ * w₁
    + a₄ * X₀^2 * w₁^2
    - a₄ * X₁^2 * w₀^2
    + 3 * a₆ * X₀ * w₀ * w₁^2
    - 3 * a₆ * X₁ * w₀^2 * w₁.
```

This is the expression I would prove as a local lemma, then use for coefficient extraction.

---

## Lean proof skeleton

The following is intentionally written as a robust proof skeleton.  Replace the `formalW...` coefficient lemma names by the actual lemmas in `FormalGroupW.lean` that say `w(X₀)` starts in degree `3` and `w(X₁)` has no pure `X₀`-axis coefficients.

```lean
import Mathlib
-- import the local file defining `formalAddX`, `formalPointMv`, and the formal `w` lemmas
-- import FLT.<path>.FormalGroupW

noncomputable section

open MvPowerSeries Finsupp
open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)

/-- A series has no pure `X₀`-axis coefficients. -/
private def Axis0Zero (f : MvPowerSeries (Fin 2) R) : Prop :=
  ∀ n : ℕ, MvPowerSeries.coeff (e₀ n) f = 0

private lemma Axis0Zero.coeff
    {f : MvPowerSeries (Fin 2) R} (hf : Axis0Zero f) (n : ℕ) :
    MvPowerSeries.coeff (e₀ n) f = 0 :=
  hf n

/-- `X₁` has no pure `X₀`-axis coefficients. -/
private lemma axis0Zero_X₁ :
    Axis0Zero (X₁ : MvPowerSeries (Fin 2) R) := by
  classical
  intro n
  simp [Axis0Zero, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]

/-- If the left factor has no pure `X₀`-axis coefficients, neither does the product.

The only point in the proof is that a decomposition of `e₀ n` in the antidiagonal
has both summands on the pure `X₀` axis. -/
private lemma Axis0Zero.mul_left
    {f g : MvPowerSeries (Fin 2) R} (hf : Axis0Zero f) :
    Axis0Zero (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rcases p with ⟨i, j⟩
  have hij : i + j = e₀ n := by
    simpa [Finset.mem_antidiagonal] using hp
  have hi_axis : ∃ k : ℕ, i = e₀ k := by
    refine ⟨i (0 : Fin 2), ?_⟩
    ext s
    fin_cases s
    · simp
    · have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hij
      have hi1 : i (1 : Fin 2) = 0 := by
        have : i (1 : Fin 2) + j (1 : Fin 2) = 0 := by simpa using hcoord
        exact Nat.eq_zero_of_add_eq_zero_left this
      simp [hi1]
  rcases hi_axis with ⟨k, rfl⟩
  simp [hf k]

private lemma Axis0Zero.mul_right
    {f g : MvPowerSeries (Fin 2) R} (hg : Axis0Zero g) :
    Axis0Zero (f * g) := by
  classical
  simpa [mul_comm] using (Axis0Zero.mul_left (f := g) (g := f) hg)

/-- Multiplying by `X₀` shifts pure-axis coefficients by one. -/
private lemma coeff_e03_X₀_mul_of_coeff_e02_zero
    {f : MvPowerSeries (Fin 2) R}
    (hf : MvPowerSeries.coeff (e₀ 2) f = 0) :
    MvPowerSeries.coeff (e₀ 3) (X₀ * f) = 0 := by
  classical
  simpa [X₀, Finsupp.single_add, hf] using
    (MvPowerSeries.coeff_add_monomial_mul
      (m := e₀ 1) (n := e₀ 2) (φ := f) (a := (1 : R)))
```

The two formal-`w` facts needed for the final coefficient are best packaged as follows:

```lean
-- Replace these proofs by the actual coefficient lemmas from the recursion defining `w`.
private lemma coeff_e02_w0
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 2) ((formalPointMv W 0) (2 : Fin 3)) = 0 := by
  -- `w(X₀) = X₀^3 + a₁ X₀^4 + ...`
  simpa [formalPointMv] using formalW_coeff_lt_three_axis0 (W := W) (i := 0) (n := 2)

private lemma axis0Zero_w1
    (W : WeierstrassCurve R) :
    Axis0Zero ((formalPointMv W 1) (2 : Fin 3)) := by
  intro n
  -- `w(X₁)` has only `X₁`-axis monomials, so every pure `X₀` coefficient is zero.
  simpa [Axis0Zero, formalPointMv] using formalW_axis0_coeff_of_index_one (W := W) (n := n)
```

Now prove a local normal form for `formalAddX`.  This keeps the final coefficient proof readable.

```lean
private lemma formalAddX_eq_expanded
    (W : WeierstrassCurve R) :
    let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
    let Wmv := W.map Cmv
    let w₀ : MvPowerSeries (Fin 2) R := (formalPointMv W 0) (2 : Fin 3)
    let w₁ : MvPowerSeries (Fin 2) R := (formalPointMv W 1) (2 : Fin 3)
    formalAddX W =
      - X₀ * w₀
      + X₁ * w₁
      - (2 : MvPowerSeries (Fin 2) R) * X₀ * w₁
      + (2 : MvPowerSeries (Fin 2) R) * X₁ * w₀
      + Wmv.a₁ * X₀ ^ 2 * w₁
      - Wmv.a₁ * X₁ ^ 2 * w₀
      + Wmv.a₂ * X₀ ^ 2 * X₁ * w₁
      - Wmv.a₂ * X₀ * X₁ ^ 2 * w₀
      + Wmv.a₃ * X₀ * w₁ ^ 2
      - Wmv.a₃ * X₁ * w₀ ^ 2
      + (2 : MvPowerSeries (Fin 2) R) * Wmv.a₃ * X₀ * w₀ * w₁
      - (2 : MvPowerSeries (Fin 2) R) * Wmv.a₃ * X₁ * w₀ * w₁
      + Wmv.a₄ * X₀ ^ 2 * w₁ ^ 2
      - Wmv.a₄ * X₁ ^ 2 * w₀ ^ 2
      + (3 : MvPowerSeries (Fin 2) R) * Wmv.a₆ * X₀ * w₀ * w₁ ^ 2
      - (3 : MvPowerSeries (Fin 2) R) * Wmv.a₆ * X₁ * w₀ ^ 2 * w₁ := by
  classical
  dsimp
  -- This is just the Mathlib polynomial formula for `Projective.addX` evaluated at
  -- `[X₀, -1, w₀]` and `[X₁, -1, w₁]`.
  simp [formalAddX, WeierstrassCurve.Projective.addX, formalPointMv]
  ring
```

Finally, use the normal form and kill every summand.

```lean
lemma formalAddX_coeff_X0_cube
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) (formalAddX W) = 0 := by
  classical
  let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
  let Wmv := W.map Cmv
  let w₀ : MvPowerSeries (Fin 2) R := (formalPointMv W 0) (2 : Fin 3)
  let w₁ : MvPowerSeries (Fin 2) R := (formalPointMv W 1) (2 : Fin 3)

  have hw₀₂ : MvPowerSeries.coeff (e₀ 2) w₀ = 0 := by
    simpa [w₀] using coeff_e02_w0 (W := W)

  have hX₀w₀ : MvPowerSeries.coeff (e₀ 3) (X₀ * w₀) = 0 :=
    coeff_e03_X₀_mul_of_coeff_e02_zero hw₀₂

  have hw₁ : Axis0Zero w₁ := by
    simpa [w₁] using axis0Zero_w1 (W := W)

  have hX₁ : Axis0Zero (X₁ : MvPowerSeries (Fin 2) R) := axis0Zero_X₁

  -- All terms except `-X₀*w₀` have either an `X₁` factor or a `w₁` factor.
  -- The following examples show the pattern; the final `simp` uses the same facts.
  have h_X₁_w₁ : MvPowerSeries.coeff (e₀ 3) (X₁ * w₁) = 0 :=
    (Axis0Zero.mul_left (f := X₁) (g := w₁) hX₁).coeff 3

  have h_X₀_w₁ : MvPowerSeries.coeff (e₀ 3) (X₀ * w₁) = 0 :=
    (Axis0Zero.mul_right (f := X₀) (g := w₁) hw₁).coeff 3

  have h_X₁_w₀ : MvPowerSeries.coeff (e₀ 3) (X₁ * w₀) = 0 :=
    (Axis0Zero.mul_left (f := X₁) (g := w₀) hX₁).coeff 3

  -- Rewrite to the substituted projective formula and let `simp` distribute `coeff`
  -- over addition/negation and use the zero coefficient facts above.
  rw [formalAddX_eq_expanded (W := W)]
  dsimp [Cmv, Wmv, w₀, w₁]

  -- In a real file, add the remaining summand-zero facts either explicitly, or register
  -- `Axis0Zero.coeff`, `Axis0Zero.mul_left`, and `Axis0Zero.mul_right` as local simp lemmas.
  -- The only non-axis-zero term is `X₀*w₀`, handled by `hX₀w₀`.
  simp [hX₀w₀, h_X₁_w₁, h_X₀_w₁, h_X₁_w₀,
    Axis0Zero.coeff,
    Axis0Zero.mul_left,
    Axis0Zero.mul_right,
    hX₁, hw₁]
```

---

## Practical version

If `simp` struggles with the final long expression, do not fight it.  Add one local lemma per term after the normal-form rewrite.  For example:

```lean
have h₁ : coeff (e₀ 3) (-X₀ * w₀) = 0 := by
  simpa using congrArg Neg.neg hX₀w₀

have h₂ : coeff (e₀ 3) (X₁ * w₁) = 0 :=
  (Axis0Zero.mul_left (f := X₁) (g := w₁) hX₁).coeff 3

have h₃ : coeff (e₀ 3) ((Wmv.a₁ * X₀ ^ 2) * w₁) = 0 :=
  (Axis0Zero.mul_right (f := Wmv.a₁ * X₀ ^ 2) (g := w₁) hw₁).coeff 3

have h₄ : coeff (e₀ 3) ((Wmv.a₃ * X₁) * w₀ ^ 2) = 0 :=
  (Axis0Zero.mul_left (f := X₁) (g := Wmv.a₃ * w₀ ^ 2) hX₁).coeff 3
```

Then finish with repeated rewriting of `map_add`, `map_neg`, `map_sub`, and those `hᵢ` facts.  This is usually more reliable than expecting one huge `simp` to solve all 16 terms.

The core mathematical point remains simple: for the pure `X₀³` coefficient, every summand in `addX` either has an `X₁`/`w₁` factor and vanishes on the `X₀` axis, or is the single term `X₀*w₀`, whose contribution would require an `X₀²` coefficient of `w₀`; that coefficient is zero because `w` starts at degree `3`.
