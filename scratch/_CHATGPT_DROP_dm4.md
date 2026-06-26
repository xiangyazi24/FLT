# Q671 (dm4): degree-4 `formalAddX` coefficients and normalized `X` linear terms

## Executive answer

For `coeff (single 0 4) formalAddX`, the direct term-by-term proof is the cleanest route.  The only pure `X₀⁴` contribution in the expanded projective `addX` formula is

```text
- X₀ * w₀,
```

and `coeff X₀³ w₀ = 1`, so

```text
coeff X₀⁴ formalAddX = -1.
```

Likewise, the only pure `X₁⁴` contribution is

```text
X₁ * w₁,
```

and `coeff X₁³ w₁ = 1`, so

```text
coeff X₁⁴ formalAddX = 1.
```

Then the quotient extraction lemmas for

```text
δ := X₀ - X₁,
formalAddX = δ^3 * normalizedAddX
```

give

```lean
coeff (single 0 1) normalizedAddX = -1
coeff (single 1 1) normalizedAddX = -1
```

because

```text
coeff X₀⁴ (δ^3 * q) = coeff X₀ q,
coeff X₁⁴ (δ^3 * q) = - coeff X₁ q.
```

---

## Lean code skeleton

This is the proof structure I would put in the coefficient file.  The only project-specific pieces you may need to rename are the formal-`w` coefficient lemmas and the multiplication equation relating `formalAddX` and `normalizedAddX`.

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.Tactic
-- import the local file defining `formalAddX`, `formalPointMv`, `normalizedAddX`, ...
-- import FLT.<path>.FormalGroupW

noncomputable section

open MvPowerSeries Finsupp
open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n

local notation "X₀" =>
  (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
local notation "X₁" =>
  (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)

local notation "δ" => (X₀ - X₁)
```

---

## Axis-zero bookkeeping

The degree-4 proof is much easier if you package the statement “no pure axis coefficients” once.

```lean
/-- A series has no pure `X₀`-axis coefficients. -/
private def Axis0Zero (f : MvPowerSeries (Fin 2) R) : Prop :=
  ∀ n : ℕ, MvPowerSeries.coeff (e₀ n) f = 0

/-- A series has no pure `X₁`-axis coefficients. -/
private def Axis1Zero (f : MvPowerSeries (Fin 2) R) : Prop :=
  ∀ n : ℕ, MvPowerSeries.coeff (e₁ n) f = 0

private lemma Axis0Zero.coeff
    {f : MvPowerSeries (Fin 2) R} (hf : Axis0Zero f) (n : ℕ) :
    MvPowerSeries.coeff (e₀ n) f = 0 :=
  hf n

private lemma Axis1Zero.coeff
    {f : MvPowerSeries (Fin 2) R} (hf : Axis1Zero f) (n : ℕ) :
    MvPowerSeries.coeff (e₁ n) f = 0 :=
  hf n

private lemma axis0Zero_X₁ :
    Axis0Zero (X₁ : MvPowerSeries (Fin 2) R) := by
  classical
  intro n
  simp [Axis0Zero, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]

private lemma axis1Zero_X₀ :
    Axis1Zero (X₀ : MvPowerSeries (Fin 2) R) := by
  classical
  intro n
  simp [Axis1Zero, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]

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

private lemma Axis1Zero.mul_left
    {f g : MvPowerSeries (Fin 2) R} (hf : Axis1Zero f) :
    Axis1Zero (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rcases p with ⟨i, j⟩
  have hij : i + j = e₁ n := by
    simpa [Finset.mem_antidiagonal] using hp
  have hi_axis : ∃ k : ℕ, i = e₁ k := by
    refine ⟨i (1 : Fin 2), ?_⟩
    ext s
    fin_cases s
    · have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hij
      have hi0 : i (0 : Fin 2) = 0 := by
        have : i (0 : Fin 2) + j (0 : Fin 2) = 0 := by simpa using hcoord
        exact Nat.eq_zero_of_add_eq_zero_left this
      simp [hi0]
    · simp
  rcases hi_axis with ⟨k, rfl⟩
  simp [hf k]

private lemma Axis1Zero.mul_right
    {f g : MvPowerSeries (Fin 2) R} (hg : Axis1Zero g) :
    Axis1Zero (f * g) := by
  classical
  simpa [mul_comm] using (Axis1Zero.mul_left (f := g) (g := f) hg)
```

---

## Shift lemmas for the two contributing terms

These are the actual coefficient computations for `X₀ * w₀` and `X₁ * w₁`.

```lean
private lemma coeff_e04_X₀_mul
    (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e₀ 4) (X₀ * f) =
      MvPowerSeries.coeff (e₀ 3) f := by
  classical
  simpa [X₀, Finsupp.single_add] using
    (MvPowerSeries.coeff_add_monomial_mul
      (m := e₀ 1) (n := e₀ 3) (φ := f) (a := (1 : R)))

private lemma coeff_e14_X₁_mul
    (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e₁ 4) (X₁ * f) =
      MvPowerSeries.coeff (e₁ 3) f := by
  classical
  simpa [X₁, Finsupp.single_add] using
    (MvPowerSeries.coeff_add_monomial_mul
      (m := e₁ 1) (n := e₁ 3) (φ := f) (a := (1 : R)))
```

---

## Formal-`w` coefficient facts needed

Use your existing recursion lemmas for `w(t)` to prove these.  The names below are placeholders; the important facts are the statements.

```lean
private lemma coeff_e03_w0
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 3) ((formalPointMv W 0) (2 : Fin 3)) = (1 : R) := by
  -- `w(X₀) = X₀^3 + a₁ X₀^4 + ...`
  simpa [formalPointMv] using formalW_coeff_axis_self_three (W := W) (i := (0 : Fin 2))

private lemma coeff_e13_w1
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₁ 3) ((formalPointMv W 1) (2 : Fin 3)) = (1 : R) := by
  -- `w(X₁) = X₁^3 + a₁ X₁^4 + ...`
  simpa [formalPointMv] using formalW_coeff_axis_self_three (W := W) (i := (1 : Fin 2))

private lemma axis0Zero_w1
    (W : WeierstrassCurve R) :
    Axis0Zero ((formalPointMv W 1) (2 : Fin 3)) := by
  intro n
  -- `w(X₁)` has only `X₁`-axis monomials, so no pure `X₀` coefficient.
  simpa [Axis0Zero, formalPointMv] using formalW_axis_coeff_ne
    (W := W) (source := (1 : Fin 2)) (target := (0 : Fin 2)) (n := n)

private lemma axis1Zero_w0
    (W : WeierstrassCurve R) :
    Axis1Zero ((formalPointMv W 0) (2 : Fin 3)) := by
  intro n
  -- `w(X₀)` has only `X₀`-axis monomials, so no pure `X₁` coefficient.
  simpa [Axis1Zero, formalPointMv] using formalW_axis_coeff_ne
    (W := W) (source := (0 : Fin 2)) (target := (1 : Fin 2)) (n := n)
```

If your `formalPointMv` is literally defined as `![X i, -1, formalW ...]`, the two axis-zero lemmas often prove by unfolding and then using the univariate support theorem for the substituted `w`.

---

## Expanded `formalAddX` normal form

This is the same normal form as in Q657, but now we use it at degree `4`.

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
  simp [formalAddX, WeierstrassCurve.Projective.addX, formalPointMv]
  ring
```

The proof works because `formalAddX W` unfolds to

```lean
(W.map MvPowerSeries.C).addX (formalPointMv W 0) (formalPointMv W 1)
```

and `Projective.addX` is a polynomial formula.

---

## Degree-4 coefficient of `formalAddX` on the `X₀` axis

```lean
lemma formalAddX_coeff_e04
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 4) (formalAddX W) = (-1 : R) := by
  classical
  let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
  let Wmv := W.map Cmv
  let w₀ : MvPowerSeries (Fin 2) R := (formalPointMv W 0) (2 : Fin 3)
  let w₁ : MvPowerSeries (Fin 2) R := (formalPointMv W 1) (2 : Fin 3)

  have hw₀3 : MvPowerSeries.coeff (e₀ 3) w₀ = (1 : R) := by
    simpa [w₀] using coeff_e03_w0 (W := W)
  have h_X₀w₀ : MvPowerSeries.coeff (e₀ 4) (X₀ * w₀) = (1 : R) := by
    simpa [hw₀3] using coeff_e04_X₀_mul (R := R) w₀

  have hX₁ : Axis0Zero (X₁ : MvPowerSeries (Fin 2) R) := axis0Zero_X₁
  have hw₁ : Axis0Zero w₁ := by
    simpa [w₁] using axis0Zero_w1 (W := W)

  -- These four examples are the patterns used by the final `simp`.
  have h_X₁_w₁ : MvPowerSeries.coeff (e₀ 4) (X₁ * w₁) = 0 :=
    (Axis0Zero.mul_left (f := X₁) (g := w₁) hX₁).coeff 4
  have h_X₀_w₁ : MvPowerSeries.coeff (e₀ 4) (X₀ * w₁) = 0 :=
    (Axis0Zero.mul_right (f := X₀) (g := w₁) hw₁).coeff 4
  have h_X₁_w₀ : MvPowerSeries.coeff (e₀ 4) (X₁ * w₀) = 0 :=
    (Axis0Zero.mul_left (f := X₁) (g := w₀) hX₁).coeff 4
  have h_w₁_sq : Axis0Zero (w₁ ^ 2) := by
    simpa [pow_two] using Axis0Zero.mul_left (f := w₁) (g := w₁) hw₁

  rw [formalAddX_eq_expanded (W := W)]
  dsimp [Cmv, Wmv, w₀, w₁]

  -- The only nonzero summand is `-X₀*w₀`; all remaining summands have an
  -- `X₁` or `w₁` factor and hence no pure `X₀`-axis coefficient.
  simp [h_X₀w₀, h_X₁_w₁, h_X₀_w₁, h_X₁_w₀,
    Axis0Zero.coeff,
    Axis0Zero.mul_left,
    Axis0Zero.mul_right,
    hX₁, hw₁, h_w₁_sq]
```

If the last `simp` does not close in your local file, replace it by explicit zero facts for the remaining terms.  For example:

```lean
have h_a₁ :
    MvPowerSeries.coeff (e₀ 4) (Wmv.a₁ * X₀ ^ 2 * w₁) = 0 :=
  (Axis0Zero.mul_right (f := Wmv.a₁ * X₀ ^ 2) (g := w₁) hw₁).coeff 4

have h_a₃ :
    MvPowerSeries.coeff (e₀ 4) (Wmv.a₃ * X₀ * w₁ ^ 2) = 0 :=
  (Axis0Zero.mul_right (f := Wmv.a₃ * X₀) (g := w₁ ^ 2) h_w₁_sq).coeff 4
```

Then include these facts in the final `simp` list.

---

## Degree-4 coefficient on the `X₁` axis

The proof is symmetric.  Now the single nonzero term is `X₁*w₁`.

```lean
lemma formalAddX_coeff_e14
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₁ 4) (formalAddX W) = (1 : R) := by
  classical
  let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
  let Wmv := W.map Cmv
  let w₀ : MvPowerSeries (Fin 2) R := (formalPointMv W 0) (2 : Fin 3)
  let w₁ : MvPowerSeries (Fin 2) R := (formalPointMv W 1) (2 : Fin 3)

  have hw₁3 : MvPowerSeries.coeff (e₁ 3) w₁ = (1 : R) := by
    simpa [w₁] using coeff_e13_w1 (W := W)
  have h_X₁w₁ : MvPowerSeries.coeff (e₁ 4) (X₁ * w₁) = (1 : R) := by
    simpa [hw₁3] using coeff_e14_X₁_mul (R := R) w₁

  have hX₀ : Axis1Zero (X₀ : MvPowerSeries (Fin 2) R) := axis1Zero_X₀
  have hw₀ : Axis1Zero w₀ := by
    simpa [w₀] using axis1Zero_w0 (W := W)

  have h_X₀_w₀ : MvPowerSeries.coeff (e₁ 4) (X₀ * w₀) = 0 :=
    (Axis1Zero.mul_left (f := X₀) (g := w₀) hX₀).coeff 4
  have h_X₀_w₁ : MvPowerSeries.coeff (e₁ 4) (X₀ * w₁) = 0 :=
    (Axis1Zero.mul_left (f := X₀) (g := w₁) hX₀).coeff 4
  have h_X₁_w₀ : MvPowerSeries.coeff (e₁ 4) (X₁ * w₀) = 0 :=
    (Axis1Zero.mul_right (f := X₁) (g := w₀) hw₀).coeff 4
  have h_w₀_sq : Axis1Zero (w₀ ^ 2) := by
    simpa [pow_two] using Axis1Zero.mul_left (f := w₀) (g := w₀) hw₀

  rw [formalAddX_eq_expanded (W := W)]
  dsimp [Cmv, Wmv, w₀, w₁]

  simp [h_X₁w₁, h_X₀_w₀, h_X₀_w₁, h_X₁_w₀,
    Axis1Zero.coeff,
    Axis1Zero.mul_left,
    Axis1Zero.mul_right,
    hX₀, hw₀, h_w₀_sq]
```

---

## Extraction from `formalAddX = δ^3 * normalizedAddX`

These are the generic degree-4 extraction lemmas.  You may already have them from the quotient-coefficient file; if so, reuse those instead of reproving them.

```lean
private lemma coeff_e04_delta3_mul
    (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e₀ 4) (δ ^ 3 * q) =
      MvPowerSeries.coeff (e₀ 1) q := by
  classical
  -- Expand `(X₀ - X₁)^3`.  Only the `X₀^3` summand can contribute to
  -- the pure `X₀^4` coefficient.
  have hδ : δ ^ 3 = X₀ ^ 3 - (3 : R) • (X₀ ^ 2 * X₁)
      + (3 : R) • (X₀ * X₁ ^ 2) - X₁ ^ 3 := by
    ring
  rw [hδ]
  simp [sub_eq_add_neg, add_mul, MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_neg, MvPowerSeries.coeff_smul,
    MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul,
    Finsupp.single_add, Finsupp.single_eq_single_iff]

private lemma coeff_e14_delta3_mul
    (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e₁ 4) (δ ^ 3 * q) =
      - MvPowerSeries.coeff (e₁ 1) q := by
  classical
  -- Only the `-X₁^3` summand contributes to the pure `X₁^4` coefficient.
  have hδ : δ ^ 3 = X₀ ^ 3 - (3 : R) • (X₀ ^ 2 * X₁)
      + (3 : R) • (X₀ * X₁ ^ 2) - X₁ ^ 3 := by
    ring
  rw [hδ]
  simp [sub_eq_add_neg, add_mul, MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_neg, MvPowerSeries.coeff_smul,
    MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul,
    Finsupp.single_add, Finsupp.single_eq_single_iff]
```

Depending on scalar-normalization in your local Mathlib revision, the `hδ` statement may prefer this equivalent shape:

```lean
have hδ : δ ^ 3 = X₀ ^ 3 - 3 * X₀ ^ 2 * X₁ + 3 * X₀ * X₁ ^ 2 - X₁ ^ 3 := by
  ring
```

Use whichever form `ring` and `simp` like better in the file.

---

## Normalized `X` linear coefficients

Assume the divisibility/normalization equation is packaged as follows.  Adjust the name and orientation to your local file.

```lean
lemma normalizedAddX_mul_delta3
    (W : WeierstrassCurve R) :
    δ ^ 3 * normalizedAddX W = formalAddX W := by
  -- Typical proof:
  --   simpa [normalizedAddX] using (normalizedAddX_dvd W).choose_spec
  -- or the same equation with `.symm`, depending on orientation.
  simpa [normalizedAddX]
    using (normalizedAddX_dvd W).choose_spec
```

Then the desired normalized coefficients are short.

```lean
lemma normalizedAddX_lin_coeff_X0
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 1) (normalizedAddX W) = (-1 : R) := by
  have hmul : δ ^ 3 * normalizedAddX W = formalAddX W :=
    normalizedAddX_mul_delta3 (W := W)
  have hcoeff := congrArg (fun f : MvPowerSeries (Fin 2) R =>
    MvPowerSeries.coeff (e₀ 4) f) hmul
  rw [coeff_e04_delta3_mul] at hcoeff
  rw [formalAddX_coeff_e04] at hcoeff
  simpa using hcoeff

lemma normalizedAddX_lin_coeff_X1
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₁ 1) (normalizedAddX W) = (-1 : R) := by
  have hmul : δ ^ 3 * normalizedAddX W = formalAddX W :=
    normalizedAddX_mul_delta3 (W := W)
  have hcoeff := congrArg (fun f : MvPowerSeries (Fin 2) R =>
    MvPowerSeries.coeff (e₁ 4) f) hmul
  rw [coeff_e14_delta3_mul] at hcoeff
  rw [formalAddX_coeff_e14] at hcoeff
  -- hcoeff : - coeff (e₁ 1) (normalizedAddX W) = 1
  have h := congrArg Neg.neg hcoeff
  simpa using h

end WeierstrassCurve
```

The sign in the `X₁` coefficient is the important point: `coeff X₁³ (X₀ - X₁)^3 = -1`, so the extraction lemma has a minus sign.  Since `formalAddX_coeff_e14 = 1`, the normalized coefficient is `-1`.

---

## Practical finishing advice

If the final `simp` in either `formalAddX_coeff_e04` or `formalAddX_coeff_e14` is too ambitious, the robust fallback is to add one zero lemma per summand after `rw [formalAddX_eq_expanded]`.  For example, in the `X₀` proof:

```lean
have h_a₁_left :
    MvPowerSeries.coeff (e₀ 4) (Wmv.a₁ * X₀ ^ 2 * w₁) = 0 :=
  (Axis0Zero.mul_right (f := Wmv.a₁ * X₀ ^ 2) (g := w₁) hw₁).coeff 4

have h_a₂_left :
    MvPowerSeries.coeff (e₀ 4) (Wmv.a₂ * X₀ ^ 2 * X₁ * w₁) = 0 := by
  have hterm : Axis0Zero (Wmv.a₂ * X₀ ^ 2 * X₁ * w₁) := by
    -- Use the explicit `X₁` factor, commuting factors as needed.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Axis0Zero.mul_left (f := X₁) (g := Wmv.a₂ * X₀ ^ 2 * w₁) hX₁
  exact hterm.coeff 4
```

Then include all of those facts in the last `simp`.  This is verbose but extremely stable, and it avoids any universal-ring argument.
