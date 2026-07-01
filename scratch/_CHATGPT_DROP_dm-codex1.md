# Q2890 (dm-codex1): performance plan for `tateC12_variableChange_eq_shortW`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Requested namespace: `MazurProof.KubertBridgeN12`

Current target:

```lean
theorem tateC12_variableChange_eq_shortW
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12ToShortVariableChange q hq1 • tateC12W q =
      shortW (A12 q) (B12 q)
```

The performance issue is caused by asking Lean to do five rational-function coefficient proofs plus all `VariableChange` unfolding in one `ext; simp; field_simp; ring_nf`.  The robust route is:

1. define scalar helper expressions `u`, `s`, and the five inner variable-change brackets;
2. prove four small zero/scale identities about those brackets;
3. prove each coefficient separately using `WeierstrassCurve.variableChange_a₁` through `variableChange_a₆`;
4. assemble the curve equality by `ext` with no algebra left.

Do **not** run a final global `simp` after `field_simp`; that is what tends to generate and then repeatedly normalize side goals like `1 + q = 0 ∨ True`.  Instead, provide denominator facts explicitly, clear denominators once inside each small lemma, and finish with `ring` rather than `ring_nf` whenever possible.

## 0. Recommended local setup

Use the existing local definitions if already present.  The following definitions are written so the coefficient lemmas can avoid unfolding the full `VariableChange` structure repeatedly.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

open scoped WeierstrassCurve

namespace MazurProof.KubertBridgeN12

noncomputable section

/-- Tate normal form `y² + (1-c)xy - b y = x³ - b x²`. -/
def tateW (b c : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 1 - c
    a₂ := -b
    a₃ := -b
    a₄ := 0
    a₆ := 0 }

def tateC12_b (q : ℚ) : ℚ :=
  q * (q - 1) * (q ^ 2 + 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 4

def tateC12_c (q : ℚ) : ℚ :=
  q * (q - 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 3

def tateC12W (q : ℚ) : WeierstrassCurve ℚ :=
  tateW (tateC12_b q) (tateC12_c q)

def tateC12_x6 (q : ℚ) : ℚ :=
  (q - 1) * (3 * q ^ 2 + 1) / (4 * (q + 1))

def tateC12_y6 (q : ℚ) : ℚ :=
  (q - 1) ^ 2 * (3 * q ^ 2 + 1) ^ 2 / (8 * (q + 1) ^ 3)

/-- The Mathlib variable-change scale.  Its inverse powers appear in the transformed coefficients. -/
def tateC12_u (q : ℚ) : ℚ :=
  1 / (2 * (q + 1) ^ 3)

/-- The shear killing `a₁`, since Mathlib has `a₁' = u⁻¹ * (a₁ + 2s)`. -/
def tateC12_s (q : ℚ) : ℚ :=
  (tateC12_c q - 1) / 2

lemma tateC12_u_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_u q ≠ 0 := by
  unfold tateC12_u
  exact div_ne_zero one_ne_zero
    (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 3 hq1))

noncomputable def tateC12ToShortVariableChange
    (q : ℚ) (hq1 : q + 1 ≠ 0) : WeierstrassCurve.VariableChange ℚ :=
  { u := Units.mk0 (tateC12_u q) (tateC12_u_ne_zero q hq1)
    r := tateC12_x6 q
    s := tateC12_s q
    t := tateC12_y6 q }
```

If these definitions already exist in your scratch test, keep the existing names and only add the helper lemmas below.

## 1. Denominator and cancellation helpers

The common failure mode is that `field_simp [hq1]` knows `q + 1 ≠ 0` but later sees denominators normalized as `1 + q`.  Add both orientations and the powers explicitly.

```lean
private lemma one_add_ne_zero_of_add_one_ne_zero {q : ℚ}
    (hq1 : q + 1 ≠ 0) : 1 + q ≠ 0 := by
  simpa [add_comm] using hq1

private lemma q_add_one_pow_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) (n : ℕ) :
    (q + 1) ^ n ≠ 0 :=
  pow_ne_zero n hq1

private lemma one_add_q_pow_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) (n : ℕ) :
    (1 + q) ^ n ≠ 0 :=
  pow_ne_zero n (one_add_ne_zero_of_add_one_ne_zero hq1)

private lemma two_mul_q_add_one_pow_three_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    2 * (q + 1) ^ 3 ≠ 0 := by
  exact mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 3 hq1)

private lemma four_mul_q_add_one_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    4 * (q + 1) ≠ 0 := by
  exact mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hq1

private lemma eight_mul_q_add_one_pow_three_ne_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    8 * (q + 1) ^ 3 ≠ 0 := by
  exact mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (pow_ne_zero 3 hq1)

private lemma inv_sq_mul_sq_cancel {x y : ℚ} (hx : x ≠ 0) :
    x⁻¹ ^ 2 * (x ^ 2 * y) = y := by
  field_simp [hx]
  ring

private lemma inv_four_mul_four_cancel {x y : ℚ} (hx : x ≠ 0) :
    x⁻¹ ^ 4 * (x ^ 4 * y) = y := by
  field_simp [hx]
  ring
```

In the coefficient algebra lemmas, start with this local block when `field_simp` needs denominator facts:

```lean
  have hq1' : 1 + q ≠ 0 := one_add_ne_zero_of_add_one_ne_zero hq1
  have hq1_2 : (q + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  have hq1_3 : (q + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hq1
  have hq1_4 : (q + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq1
  have h1q_2 : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hq1'
  have h1q_3 : (1 + q) ^ 3 ≠ 0 := pow_ne_zero 3 hq1'
  have h1q_4 : (1 + q) ^ 4 ≠ 0 := pow_ne_zero 4 hq1'
```

Then use:

```lean
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_u, tateC12_s,
    hq1, hq1', hq1_2, hq1_3, hq1_4, h1q_2, h1q_3, h1q_4,
    two_mul_q_add_one_pow_three_ne_zero q hq1,
    four_mul_q_add_one_ne_zero q hq1,
    eight_mul_q_add_one_pow_three_ne_zero q hq1]
  ring
```

Only use `ring_nf` if this exact `field_simp; ring` pair fails.  In my experience with this kind of goal, `ring` is faster after denominators are explicitly cleared.

## 2. Inner coefficient expressions

The Mathlib formulas are:

```lean
WeierstrassCurve.variableChange_a₁
WeierstrassCurve.variableChange_a₂
WeierstrassCurve.variableChange_a₃
WeierstrassCurve.variableChange_a₄
WeierstrassCurve.variableChange_a₆
```

For the Tate curve, the inner brackets are the following.  Prove identities about these definitions, not about the full transformed curve.

```lean
private def tateC12_a1_inner (q : ℚ) : ℚ :=
  (1 - tateC12_c q) + 2 * tateC12_s q

private def tateC12_a2_inner (q : ℚ) : ℚ :=
  -tateC12_b q - tateC12_s q * (1 - tateC12_c q) +
    3 * tateC12_x6 q - tateC12_s q ^ 2

private def tateC12_a3_inner (q : ℚ) : ℚ :=
  -tateC12_b q + tateC12_x6 q * (1 - tateC12_c q) +
    2 * tateC12_y6 q

private def tateC12_a4_inner (q : ℚ) : ℚ :=
  0 - tateC12_s q * (-tateC12_b q) +
    2 * tateC12_x6 q * (-tateC12_b q) -
    (tateC12_y6 q + tateC12_x6 q * tateC12_s q) * (1 - tateC12_c q) +
    3 * tateC12_x6 q ^ 2 - 2 * tateC12_s q * tateC12_y6 q

private def tateC12_a6_inner (q : ℚ) : ℚ :=
  0 + tateC12_x6 q * 0 + tateC12_x6 q ^ 2 * (-tateC12_b q) +
    tateC12_x6 q ^ 3 - tateC12_y6 q * (-tateC12_b q) -
    tateC12_y6 q ^ 2 - tateC12_x6 q * tateC12_y6 q * (1 - tateC12_c q)
```

The five desired identities are:

```lean
private lemma tateC12_a1_inner_zero (q : ℚ) :
    tateC12_a1_inner q = 0 := by
  unfold tateC12_a1_inner tateC12_s
  ring

private lemma tateC12_a3_inner_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_a3_inner q = 0 := by
  unfold tateC12_a3_inner
  have hq1' : 1 + q ≠ 0 := one_add_ne_zero_of_add_one_ne_zero hq1
  have hq1_2 : (q + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  have hq1_3 : (q + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hq1
  have hq1_4 : (q + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq1
  have h1q_2 : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hq1'
  have h1q_3 : (1 + q) ^ 3 ≠ 0 := pow_ne_zero 3 hq1'
  have h1q_4 : (1 + q) ^ 4 ≠ 0 := pow_ne_zero 4 hq1'
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_u, tateC12_s,
    hq1, hq1', hq1_2, hq1_3, hq1_4, h1q_2, h1q_3, h1q_4,
    two_mul_q_add_one_pow_three_ne_zero q hq1,
    four_mul_q_add_one_ne_zero q hq1,
    eight_mul_q_add_one_pow_three_ne_zero q hq1]
  ring

private lemma tateC12_a6_inner_zero (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_a6_inner q = 0 := by
  unfold tateC12_a6_inner
  have hq1' : 1 + q ≠ 0 := one_add_ne_zero_of_add_one_ne_zero hq1
  have hq1_2 : (q + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  have hq1_3 : (q + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hq1
  have hq1_4 : (q + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq1
  have h1q_2 : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hq1'
  have h1q_3 : (1 + q) ^ 3 ≠ 0 := pow_ne_zero 3 hq1'
  have h1q_4 : (1 + q) ^ 4 ≠ 0 := pow_ne_zero 4 hq1'
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_u, tateC12_s,
    hq1, hq1', hq1_2, hq1_3, hq1_4, h1q_2, h1q_3, h1q_4,
    two_mul_q_add_one_pow_three_ne_zero q hq1,
    four_mul_q_add_one_ne_zero q hq1,
    eight_mul_q_add_one_pow_three_ne_zero q hq1]
  ring

/-- `a₂' = u⁻² * inner = A12`; prove the scaled inner form first. -/
private lemma tateC12_a2_inner_scaled (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_a2_inner q = tateC12_u q ^ 2 * A12 q := by
  unfold tateC12_a2_inner
  have hq1' : 1 + q ≠ 0 := one_add_ne_zero_of_add_one_ne_zero hq1
  have hq1_2 : (q + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  have hq1_3 : (q + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hq1
  have hq1_4 : (q + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq1
  have h1q_2 : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hq1'
  have h1q_3 : (1 + q) ^ 3 ≠ 0 := pow_ne_zero 3 hq1'
  have h1q_4 : (1 + q) ^ 4 ≠ 0 := pow_ne_zero 4 hq1'
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_u, tateC12_s, A12,
    hq1, hq1', hq1_2, hq1_3, hq1_4, h1q_2, h1q_3, h1q_4,
    two_mul_q_add_one_pow_three_ne_zero q hq1,
    four_mul_q_add_one_ne_zero q hq1,
    eight_mul_q_add_one_pow_three_ne_zero q hq1]
  ring

/-- `a₄' = u⁻⁴ * inner = B12`; prove the scaled inner form first. -/
private lemma tateC12_a4_inner_scaled (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_a4_inner q = tateC12_u q ^ 4 * B12 q := by
  unfold tateC12_a4_inner
  have hq1' : 1 + q ≠ 0 := one_add_ne_zero_of_add_one_ne_zero hq1
  have hq1_2 : (q + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  have hq1_3 : (q + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hq1
  have hq1_4 : (q + 1) ^ 4 ≠ 0 := pow_ne_zero 4 hq1
  have h1q_2 : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hq1'
  have h1q_3 : (1 + q) ^ 3 ≠ 0 := pow_ne_zero 3 hq1'
  have h1q_4 : (1 + q) ^ 4 ≠ 0 := pow_ne_zero 4 hq1'
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_u, tateC12_s, B12,
    hq1, hq1', hq1_2, hq1_3, hq1_4, h1q_2, h1q_3, h1q_4,
    two_mul_q_add_one_pow_three_ne_zero q hq1,
    four_mul_q_add_one_ne_zero q hq1,
    eight_mul_q_add_one_pow_three_ne_zero q hq1]
  ring
```

If one of the scaled lemmas is still slow, use this further split:

```lean
-- Instead of proving the full `a4_inner_scaled` directly, prove denominator-cleared form:
private lemma tateC12_a4_inner_scaled_cleared (q : ℚ) :
    (2 * (q + 1) ^ 3) ^ 4 * tateC12_a4_inner q = B12 q := by
  -- Here there are no inverse powers of `u`; this often reduces faster.
  -- Then derive `tateC12_a4_inner_scaled` using `field_simp [tateC12_u, hq1]`.
  unfold tateC12_a4_inner
  -- field_simp [...]
  -- ring
  admit
```

Use that only if needed; the main scaled lemma above is usually enough once the five coefficient goals are separated.

## 3. Coefficient lemmas using Mathlib's `variableChange_aᵢ`

These are intentionally tiny.  If a coefficient lemma fails, it pinpoints either a formula mismatch or a Mathlib convention mismatch.

The only mildly fragile line is the `simp only [Units.val_mk0, Units.val_inv_eq_inv_val]`.  If your local Mathlib names the unit-coercion simp lemma differently, remove that line and replace the following `change` by whatever Lean prints after `rw [WeierstrassCurve.variableChange_a₂]`.

```lean
private lemma tateC12_variableChange_a1
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12ToShortVariableChange q hq1 • tateC12W q).a₁ =
      (shortW (A12 q) (B12 q)).a₁ := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp only [shortW, tateC12ToShortVariableChange, tateC12W, tateW,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  change (tateC12_u q)⁻¹ * tateC12_a1_inner q = 0
  rw [tateC12_a1_inner_zero q]
  ring

private lemma tateC12_variableChange_a2
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12ToShortVariableChange q hq1 • tateC12W q).a₂ =
      (shortW (A12 q) (B12 q)).a₂ := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp only [shortW, tateC12ToShortVariableChange, tateC12W, tateW,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  change (tateC12_u q)⁻¹ ^ 2 * tateC12_a2_inner q = A12 q
  rw [tateC12_a2_inner_scaled q hq1]
  exact inv_sq_mul_sq_cancel (x := tateC12_u q) (y := A12 q)
    (tateC12_u_ne_zero q hq1)

private lemma tateC12_variableChange_a3
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12ToShortVariableChange q hq1 • tateC12W q).a₃ =
      (shortW (A12 q) (B12 q)).a₃ := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp only [shortW, tateC12ToShortVariableChange, tateC12W, tateW,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  change (tateC12_u q)⁻¹ ^ 3 * tateC12_a3_inner q = 0
  rw [tateC12_a3_inner_zero q hq1]
  ring

private lemma tateC12_variableChange_a4
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12ToShortVariableChange q hq1 • tateC12W q).a₄ =
      (shortW (A12 q) (B12 q)).a₄ := by
  rw [WeierstrassCurve.variableChange_a₄]
  simp only [shortW, tateC12ToShortVariableChange, tateC12W, tateW,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  change (tateC12_u q)⁻¹ ^ 4 * tateC12_a4_inner q = B12 q
  rw [tateC12_a4_inner_scaled q hq1]
  exact inv_four_mul_four_cancel (x := tateC12_u q) (y := B12 q)
    (tateC12_u_ne_zero q hq1)

private lemma tateC12_variableChange_a6
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    (tateC12ToShortVariableChange q hq1 • tateC12W q).a₆ =
      (shortW (A12 q) (B12 q)).a₆ := by
  rw [WeierstrassCurve.variableChange_a₆]
  simp only [shortW, tateC12ToShortVariableChange, tateC12W, tateW,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  change (tateC12_u q)⁻¹ ^ 6 * tateC12_a6_inner q = 0
  rw [tateC12_a6_inner_zero q hq1]
  ring
```

Now the final theorem is just structure extensionality.  There should be no `field_simp`, no `ring_nf`, and no global `simp` here.

```lean
theorem tateC12_variableChange_eq_shortW
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12ToShortVariableChange q hq1 • tateC12W q =
      shortW (A12 q) (B12 q) := by
  ext
  · exact tateC12_variableChange_a1 q hq1
  · exact tateC12_variableChange_a2 q hq1
  · exact tateC12_variableChange_a3 q hq1
  · exact tateC12_variableChange_a4 q hq1
  · exact tateC12_variableChange_a6 q hq1

end
end MazurProof.KubertBridgeN12
```

If `ext` produces goals in a different order, Lean will show it immediately.  Reorder the five `exact` lines accordingly; the coefficient theorem names make this painless.

## 4. Detecting a direction or scaling mismatch

The coefficient lemmas are also diagnostics.

### `a₁` failure

Mathlib's convention is:

```text
a₁' = u⁻¹ * (a₁ + 2s)
```

For Tate C12, `a₁ = 1 - c`, so killing `a₁` requires:

```text
s = (c - 1)/2
```

If `a₁` fails and the residual is `2 - 2c` or similar, the sign of `s` is wrong.  Do **not** debug `a₂/a₄` until `a₁` is exactly zero.

### `a₃` failure

Mathlib's convention is:

```text
a₃' = u⁻³ * (a₃ + r*a₁ + 2t)
```

With `a₃ = -b`, this says the point used for translation must satisfy:

```text
-b + x6*(1-c) + 2*y6 = 0.
```

If `a₃` fails by a sign, try `t := -tateC12_y6 q`.  If it fails by a different rational factor, the formula for `y6` is mismatched with the `q`-parameter.

### `a₆` failure

The `a₆` bracket is the translated point equation.  If `a₁` and `a₃` pass but `a₆` fails, then `(x6,y6)` is not actually the point being translated to the origin under the Mathlib direction.  The likely fixes are:

```text
r := x6,  t := y6      -- current Mathlib direction: old X,Y = u²X + r, u³Y + u²sX + t
r := x6,  t := -y6     -- if the listed y-coordinate uses the opposite branch
r := -x6, t := -y6     -- if the translation direction was read backwards
```

Only one of these should make `a₃_inner_zero` and `a₆_inner_zero` both true.

### `a₂/a₄` failure after `a₁/a₃/a₆` pass

Then the translation is right and only the scale `u` is wrong.  Since Mathlib has:

```text
a₂' = u⁻² * inner₂
a₄' = u⁻⁴ * inner₄
```

if the result differs by powers of `2*(q+1)^3`, invert `u`:

```lean
def tateC12_u_alt (q : ℚ) : ℚ := 2 * (q + 1) ^ 3
```

The scaled inner lemmas will make the mismatch visible:

```lean
tateC12_a2_inner q = tateC12_u q ^ 2 * A12 q
tateC12_a4_inner q = tateC12_u q ^ 4 * B12 q
```

If these become instead `u⁻² * A12` and `u⁻⁴ * B12`, the direction of scaling is reversed.

## 5. Extra performance notes

1. Mark the big algebra lemmas `private`, but **do not** mark them `[simp]`.  Large `[simp]` lemmas over rational functions will slow unrelated goals.
2. Use `simp only [...]` in coefficient lemmas.  Avoid `simp [defs]` there; it can unfold `A12`, `B12`, and the entire curve structure unnecessarily.
3. Keep `field_simp` inside the inner lemmas only.  The final theorem should be linear-time elaboration.
4. If one inner lemma is still slow, make a denominator-cleared theorem first, for example:

```lean
private lemma tateC12_a2_inner_scaled_cleared (q : ℚ) :
    (2 * (q + 1) ^ 3) ^ 2 * tateC12_a2_inner q = A12 q := by
  unfold tateC12_a2_inner
  field_simp [tateC12_b, tateC12_c, tateC12_x6, tateC12_y6,
    tateC12_s, A12]
  ring
```

then derive `tateC12_a2_inner_scaled` with one small `field_simp [tateC12_u, hq1]` proof.  This sometimes beats asking `field_simp` to clear both the Tate denominators and the `u^2` denominator in the same pass.

5. For profiling, temporarily wrap only the slow inner lemma:

```lean
set_option profiler true in
private lemma tateC12_a4_inner_scaled ... := by
  ...
```

Do not profile the final `ext` theorem; if the plan above is followed, it should not be the bottleneck.
