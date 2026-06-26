# Q675 (dm2): coefficients `(3,0)` of formal `addX` and `addZ`

## Executive answer

For these two lemmas, I would **not** expand `MvPowerSeries.coeff_mul` for every product.  Use the order API:

```lean
MvPowerSeries.coeff_of_lt_order
MvPowerSeries.le_order_mul
MvPowerSeries.min_order_le_add
```

The point is exactly your degree argument:

* `Pz = w₀` and `Qz = w₁` have order at least `3`;
* `X₀` and `X₁` have order at least `1`;
* every substituted `addX` term contains at least one factor `Xᵢ * Pz` or `Xᵢ * Qz`, so every term has order at least `4`;
* every substituted `addZ` term contains either an `Xᵢ * Pz`/`Xᵢ * Qz` factor or a `Pz * Qz`, `Pz^2`, or `Qz^2` factor, so every term has order at least `4` — in fact at least `6`, but `4` is enough.

Then coefficient `(3,0)` vanishes because `degree (single 0 3) = 3 < 4`.

Below is the Lean code I would add.  It is written in two layers:

1. a reusable polynomial-level lemma for arbitrary formal-coordinate-shaped `P` and `Q`;
2. the wrappers for your actual `formalPointMv` points, using `simp [formalPointMv]` plus your local proof that the `z` coordinates have order at least `3`.

---

## Lean code

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Tactic

open scoped BigOperators
open MvPowerSeries

namespace WeierstrassCurve
namespace Projective

variable {R : Type*} [CommRing R]

local abbrev Mv2 : Type _ := MvPowerSeries (Fin 2) R

local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : Mv2)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : Mv2)
local notation "e30" => (Finsupp.single (0 : Fin 2) 3 : Fin 2 →₀ ℕ)
local notation "c30" f => MvPowerSeries.coeff e30 f

/-- The target exponent has total degree `3`. -/
private lemma degree_e30 : Finsupp.degree e30 = 3 := by
  simp [e30]

/-- Any series of order at least `4` has zero coefficient at `X₀^3`. -/
private lemma coeff_e30_eq_zero_of_four_le_order {f : Mv2}
    (hf : (4 : ℕ∞) ≤ f.order) :
    c30 f = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by norm_num [degree_e30]) hf

/-- `X i` has order at least `1`.  This version is safe even over the zero ring. -/
private lemma one_le_order_X (i : Fin 2) :
    (1 : ℕ∞) ≤ (MvPowerSeries.X i : Mv2).order := by
  classical
  rw [MvPowerSeries.X_def, MvPowerSeries.order_monomial]
  by_cases h : (1 : R) = 0
  · simp [h]
  · simp [h]

private lemma four_le_order_X_mul_z {Z : Mv2} (i : Fin 2)
    (hZ : (3 : ℕ∞) ≤ Z.order) :
    (4 : ℕ∞) ≤ ((MvPowerSeries.X i : Mv2) * Z).order := by
  calc
    (4 : ℕ∞) = (1 : ℕ∞) + 3 := by norm_num
    _ ≤ (MvPowerSeries.X i : Mv2).order + Z.order :=
        add_le_add (one_le_order_X (R := R) i) hZ
    _ ≤ ((MvPowerSeries.X i : Mv2) * Z).order :=
        MvPowerSeries.le_order_mul

private lemma four_le_order_z_mul_X {Z : Mv2} (i : Fin 2)
    (hZ : (3 : ℕ∞) ≤ Z.order) :
    (4 : ℕ∞) ≤ (Z * (MvPowerSeries.X i : Mv2)).order := by
  simpa [mul_comm] using four_le_order_X_mul_z (R := R) i hZ

/-- Multiplying on the left by an arbitrary series cannot lower the order bound. -/
private lemma le_order_mul_left_of_le {f : Mv2} (A : Mv2) {n : ℕ∞}
    (hf : n ≤ f.order) :
    n ≤ (A * f).order := by
  calc
    n = (0 : ℕ∞) + n := by simp
    _ ≤ A.order + f.order := add_le_add (zero_le _) hf
    _ ≤ (A * f).order := MvPowerSeries.le_order_mul

/-- Multiplying on the right by an arbitrary series cannot lower the order bound. -/
private lemma le_order_mul_right_of_le {f : Mv2} (A : Mv2) {n : ℕ∞}
    (hf : n ≤ f.order) :
    n ≤ (f * A).order := by
  simpa [mul_comm] using le_order_mul_left_of_le (R := R) A hf

private lemma four_le_order_has_X_z_factor
    (A B : Mv2) (i : Fin 2) {Z : Mv2}
    (hZ : (3 : ℕ∞) ≤ Z.order) :
    (4 : ℕ∞) ≤ (A * (MvPowerSeries.X i : Mv2) * Z * B).order := by
  have hXZ : (4 : ℕ∞) ≤ ((MvPowerSeries.X i : Mv2) * Z).order :=
    four_le_order_X_mul_z (R := R) i hZ
  have h1 : (4 : ℕ∞) ≤ (A * ((MvPowerSeries.X i : Mv2) * Z)).order :=
    le_order_mul_left_of_le (R := R) A hXZ
  have h2 : (4 : ℕ∞) ≤ ((A * ((MvPowerSeries.X i : Mv2) * Z)) * B).order :=
    le_order_mul_right_of_le (R := R) B h1
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

private lemma four_le_order_z_z_factor
    (A B : Mv2) {Z₁ Z₂ : Mv2}
    (hZ₁ : (3 : ℕ∞) ≤ Z₁.order) (hZ₂ : (3 : ℕ∞) ≤ Z₂.order) :
    (4 : ℕ∞) ≤ (A * Z₁ * Z₂ * B).order := by
  have hZZ6 : (6 : ℕ∞) ≤ (Z₁ * Z₂).order := by
    calc
      (6 : ℕ∞) = (3 : ℕ∞) + 3 := by norm_num
      _ ≤ Z₁.order + Z₂.order := add_le_add hZ₁ hZ₂
      _ ≤ (Z₁ * Z₂).order := MvPowerSeries.le_order_mul
  have hZZ4 : (4 : ℕ∞) ≤ (Z₁ * Z₂).order := le_trans (by norm_num) hZZ6
  have h1 : (4 : ℕ∞) ≤ (A * (Z₁ * Z₂)).order :=
    le_order_mul_left_of_le (R := R) A hZZ4
  have h2 : (4 : ℕ∞) ≤ ((A * (Z₁ * Z₂)) * B).order :=
    le_order_mul_right_of_le (R := R) B h1
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

private lemma four_le_order_add {f g : Mv2} {n : ℕ∞}
    (hf : n ≤ f.order) (hg : n ≤ g.order) :
    n ≤ (f + g).order := by
  exact le_trans (le_min hf hg) MvPowerSeries.min_order_le_add

private lemma four_le_order_neg {f : Mv2} {n : ℕ∞}
    (hf : n ≤ f.order) :
    n ≤ (-f).order := by
  simpa using hf

private lemma four_le_order_sub {f g : Mv2} {n : ℕ∞}
    (hf : n ≤ f.order) (hg : n ≤ g.order) :
    n ≤ (f - g).order := by
  simpa [sub_eq_add_neg] using
    four_le_order_add (R := R) (n := n) hf (four_le_order_neg (R := R) hg)

/-- Compact record for the only facts about the formal points used in the computation. -/
private structure FormalCoords (P Q : Fin 3 → Mv2) : Prop where
  P0 : P 0 = X₀
  P1 : P 1 = (-1 : Mv2)
  Pz_order : (3 : ℕ∞) ≤ (P 2).order
  Q0 : Q 0 = X₁
  Q1 : Q 1 = (-1 : Mv2)
  Qz_order : (3 : ℕ∞) ≤ (Q 2).order

/--
Polynomial-level version: `addX` has no `X₀^3` term after substituting
`P = [X₀,-1,Pz]`, `Q = [X₁,-1,Qz]`, with `ord(Pz), ord(Qz) ≥ 3`.
-/
theorem coeff_e30_addX_of_formalCoords
    (W' : WeierstrassCurve.Projective Mv2) (P Q : Fin 3 → Mv2)
    (h : FormalCoords (R := R) P Q) :
    c30 (W'.addX P Q) = 0 := by
  apply coeff_e30_eq_zero_of_four_le_order (R := R)

  -- Unfold the 16-term Mathlib polynomial and substitute
  -- `P0 = X₀`, `P1 = -1`, `Q0 = X₁`, `Q1 = -1`.
  -- Every remaining summand has either an `Xᵢ*z` factor or a `z*z` factor.
  rw [Projective.addX]
  simp only [h.P0, h.P1, h.Q0, h.Q1]

  -- After the preceding simplification, `simp` normalizes powers of `-1` and
  -- coefficients, and the local order lemmas discharge each summand.
  -- The following `simpa` is intentionally order-based; it avoids any direct
  -- `MvPowerSeries.coeff_mul` expansion.
  repeat
    first
    | apply four_le_order_add
    | apply four_le_order_sub
    | apply four_le_order_neg
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Pz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Qz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Pz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Qz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Pz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Qz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Qz_order h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Qz_order h.Qz_order

/--
Polynomial-level version: `addZ` has no `X₀^3` term after substituting
`P = [X₀,-1,Pz]`, `Q = [X₁,-1,Qz]`, with `ord(Pz), ord(Qz) ≥ 3`.
-/
theorem coeff_e30_addZ_of_formalCoords
    (W' : WeierstrassCurve.Projective Mv2) (P Q : Fin 3 → Mv2)
    (h : FormalCoords (R := R) P Q) :
    c30 (W'.addZ P Q) = 0 := by
  apply coeff_e30_eq_zero_of_four_le_order (R := R)

  -- Unfold the 12-term Mathlib polynomial and substitute the formal coordinates.
  rw [Projective.addZ]
  simp only [h.P0, h.P1, h.Q0, h.Q1]

  -- The first two terms have `X*Z`; the remaining terms have either `X*Z`
  -- or at least two `z` factors.
  repeat
    first
    | apply four_le_order_add
    | apply four_le_order_sub
    | apply four_le_order_neg
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Pz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Qz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Pz_order
    | exact four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Qz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Pz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Qz_order
    | exact four_le_order_z_z_factor (R := R) 1 1 h.Qz_order h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (0 : Fin 2) h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_has_X_z_factor (R := R) 1 1 (1 : Fin 2) h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Pz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Pz_order h.Qz_order
    | simpa [pow_two, mul_assoc, mul_left_comm, mul_comm]
        using four_le_order_z_z_factor (R := R) 1 1 h.Qz_order h.Qz_order

end Projective
end WeierstrassCurve
```

---

## Wrappers for your actual `formalPointMv`

The previous two theorems are the polynomial-level proof.  The actual wrappers should be one-liners once you provide the two `z`-order facts.

Use whatever names you already have for the order facts; I will call them:

```lean
formalPointMv_z_order_ge_three
```

with expected shape:

```lean
formalPointMv_z_order_ge_three
    (W : WeierstrassCurve R) (i : Fin 2) :
    (3 : ℕ∞) ≤ (((formalPointMv W i) 2).order)
```

Then the wrappers are:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Tactic

open scoped BigOperators
open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local abbrev Mv2 : Type _ := MvPowerSeries (Fin 2) R
local notation "e30" => (Finsupp.single (0 : Fin 2) 3 : Fin 2 →₀ ℕ)
local notation "c30" f => MvPowerSeries.coeff e30 f

theorem addX_formal_coeff_e30
    (W : WeierstrassCurve R) :
    c30 (((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective).addX
      (formalPointMv W (0 : Fin 2))
      (formalPointMv W (1 : Fin 2))) = 0 := by
  apply Projective.coeff_e30_addX_of_formalCoords
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [formalPointMv]
  · simp [formalPointMv]
  · simpa using formalPointMv_z_order_ge_three W (0 : Fin 2)
  · simp [formalPointMv]
  · simp [formalPointMv]
  · simpa using formalPointMv_z_order_ge_three W (1 : Fin 2)

theorem addZ_formal_coeff_e30
    (W : WeierstrassCurve R) :
    c30 (((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective).addZ
      (formalPointMv W (0 : Fin 2))
      (formalPointMv W (1 : Fin 2))) = 0 := by
  apply Projective.coeff_e30_addZ_of_formalCoords
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [formalPointMv]
  · simp [formalPointMv]
  · simpa using formalPointMv_z_order_ge_three W (0 : Fin 2)
  · simp [formalPointMv]
  · simp [formalPointMv]
  · simpa using formalPointMv_z_order_ge_three W (1 : Fin 2)

end WeierstrassCurve
```

If your curve-over-power-series object is named differently, replace

```lean
((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).toProjective)
```

by your local `formalCoeffCurve W`/`Wformal` expression.  Nothing else in the proof depends on the coefficients of the curve; the only facts used are the four coordinate equalities and the two `z`-order bounds.

---

## If the `repeat first` block is too fragile

Lean sometimes normalizes the unfolded polynomial in a slightly different association.  In that case, keep the same proof but replace the `repeat first` block by direct coefficient simplification using the two zero lemmas below:

```lean
private lemma coeff_e30_has_X_z_factor
    (A B : MvPowerSeries (Fin 2) R) (i : Fin 2) {Z : MvPowerSeries (Fin 2) R}
    (hZ : (3 : ℕ∞) ≤ Z.order) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)
      (A * MvPowerSeries.X i * Z * B) = 0 := by
  apply Projective.coeff_e30_eq_zero_of_four_le_order
  exact Projective.four_le_order_has_X_z_factor A B i hZ

private lemma coeff_e30_has_z_z_factor
    (A B : MvPowerSeries (Fin 2) R) {Z₁ Z₂ : MvPowerSeries (Fin 2) R}
    (hZ₁ : (3 : ℕ∞) ≤ Z₁.order) (hZ₂ : (3 : ℕ∞) ≤ Z₂.order) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)
      (A * Z₁ * Z₂ * B) = 0 := by
  apply Projective.coeff_e30_eq_zero_of_four_le_order
  exact Projective.four_le_order_z_z_factor A B hZ₁ hZ₂
```

Then the final proof can be:

```lean
  simp [Projective.addX, Projective.addZ, formalPointMv,
    coeff_e30_has_X_z_factor, coeff_e30_has_z_z_factor,
    formalPointMv_z_order_ge_three,
    MvPowerSeries.coeff_add, MvPowerSeries.coeff_sub, MvPowerSeries.coeff_neg,
    mul_assoc, mul_left_comm, mul_comm]
```

This is the same proof, just pushed through `coeff` rather than through `order` of the whole sum.
