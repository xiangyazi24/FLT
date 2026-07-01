# Q3012 (dm-codex1): C10 Tate-to-short variable-change algebra, N12 style

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`, with the generic point-equivalence block moved/copied from `KubertBridgeN12.lean` to `KubertTateCommon.lean`.

I could not fetch the exact working files through the connector, so this is written against the definitions in the prompt and the standard Mathlib/N12 convention for `WeierstrassCurve.VariableChange`:

```text
x_old = u^2*x_new + r
y_old = u^3*y_new + u^2*s*x_new + t
```

with coefficient formulas equivalent to:

```text
u*a1' = a1 + 2s
u^2*a2' = a2 - s*a1 + 3r - s^2
u^3*a3' = a3 + r*a1 + 2t
u^4*a4' = a4 - s*a3 + 2r*a2 - (t+r*s)*a1 + 3r^2 - 2s*t
u^6*a6' = a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1
```

Under that convention, the Q3011 variable change is correct.  Because Mathlib’s `VariableChange.u` is a unit, I recommend making the VC depend on the two nonzero proofs:

```lean
tateC10_pToShortVC p hden hpT
```

rather than trying to define a proof-free unit.

## Patchable Lean snippet

Put this inside `namespace MazurProof.KubertBridgeN10`, after the C10 definitions and after the already-compiled `pToShort_sq_sub_one`, `pToShort_shortQ`, `pToShort_phi` lemmas.

```lean
/-- The corrected short-family parameter attached to the C10 Tate-row parameter. -/
def tateC10_pToShortParam (p : ℚ) : ℚ :=
  1 / (1 - 2 * p)

/-- Rational value of the `u` part of the C10 Tate-to-short variable change. -/
def tateC10_u (p : ℚ) : ℚ :=
  (2 * p - 1) ^ 3 / (8 * tateC10_den p)

/-- `r` part of the C10 Tate-to-short variable change. -/
def tateC10_r (p : ℚ) : ℚ :=
  -p ^ 3 * (p - 1) / tateC10_den p

/-- `s` part of the C10 Tate-to-short variable change. -/
def tateC10_s (p : ℚ) : ℚ :=
  (tateC10_c p - 1) / 2

/-- `t` part of the C10 Tate-to-short variable change. -/
def tateC10_vc_t (p : ℚ) : ℚ :=
  (tateC10_b p - tateC10_r p * (1 - tateC10_c p)) / 2

lemma tateC10_two_mul_sub_one_ne_zero
    {p : ℚ} (hpT : 1 - 2 * p ≠ 0) :
    2 * p - 1 ≠ 0 := by
  intro h
  apply hpT
  linarith

lemma tateC10_eight_mul_den_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    8 * tateC10_den p ≠ 0 := by
  exact mul_ne_zero (by norm_num) hden

lemma tateC10_u_ne_zero
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_u p ≠ 0 := by
  have h2 : 2 * p - 1 ≠ 0 := tateC10_two_mul_sub_one_ne_zero hpT
  dsimp [tateC10_u]
  exact div_ne_zero
    (pow_ne_zero 3 h2)
    (tateC10_eight_mul_den_ne_zero hden)

noncomputable def tateC10_pToShortVC
    (p : ℚ)
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  { u := Units.mk0 (tateC10_u p) (tateC10_u_ne_zero hden hpT)
    r := tateC10_r p
    s := tateC10_s p
    t := tateC10_vc_t p }

@[simp] lemma tateC10_pToShortVC_u_coe
    {p : ℚ} {hden : tateC10_den p ≠ 0} {hpT : 1 - 2 * p ≠ 0} :
    ((tateC10_pToShortVC p hden hpT).u : ℚ) = tateC10_u p := rfl

@[simp] lemma tateC10_pToShortVC_r
    {p : ℚ} {hden : tateC10_den p ≠ 0} {hpT : 1 - 2 * p ≠ 0} :
    (tateC10_pToShortVC p hden hpT).r = tateC10_r p := rfl

@[simp] lemma tateC10_pToShortVC_s
    {p : ℚ} {hden : tateC10_den p ≠ 0} {hpT : 1 - 2 * p ≠ 0} :
    (tateC10_pToShortVC p hden hpT).s = tateC10_s p := rfl

@[simp] lemma tateC10_pToShortVC_t
    {p : ℚ} {hden : tateC10_den p ≠ 0} {hpT : 1 - 2 * p ≠ 0} :
    (tateC10_pToShortVC p hden hpT).t = tateC10_vc_t p := rfl
```

If the local `VariableChange` field is not named `t`, rename only the last field and the last simp lemma.

## Inner coefficient expressions

These are the five numerators appearing before division by `u^k` in Mathlib’s variable-change formulas.  They avoid repeatedly expanding `VariableChange` inside algebra proofs.

```lean
private def tateC10_a1Inner (p : ℚ) : ℚ :=
  (1 - tateC10_c p) + 2 * tateC10_s p

private def tateC10_a2Inner (p : ℚ) : ℚ :=
  (-tateC10_b p)
    - tateC10_s p * (1 - tateC10_c p)
    + 3 * tateC10_r p
    - tateC10_s p ^ 2

private def tateC10_a3Inner (p : ℚ) : ℚ :=
  (-tateC10_b p)
    + tateC10_r p * (1 - tateC10_c p)
    + 2 * tateC10_vc_t p

private def tateC10_a4Inner (p : ℚ) : ℚ :=
  - tateC10_s p * (-tateC10_b p)
    + 2 * tateC10_r p * (-tateC10_b p)
    - (tateC10_vc_t p + tateC10_r p * tateC10_s p) * (1 - tateC10_c p)
    + 3 * tateC10_r p ^ 2
    - 2 * tateC10_s p * tateC10_vc_t p

private def tateC10_a6Inner (p : ℚ) : ℚ :=
  tateC10_r p ^ 2 * (-tateC10_b p)
    + tateC10_r p ^ 3
    - tateC10_vc_t p * (-tateC10_b p)
    - tateC10_vc_t p ^ 2
    - tateC10_r p * tateC10_vc_t p * (1 - tateC10_c p)
```

The `a1` and `a3` vanish by construction, before any C10-specific expansion:

```lean
private lemma tateC10_a1Inner_eq_zero (p : ℚ) :
    tateC10_a1Inner p = 0 := by
  dsimp [tateC10_a1Inner, tateC10_s]
  ring

private lemma tateC10_a3Inner_eq_zero (p : ℚ) :
    tateC10_a3Inner p = 0 := by
  dsimp [tateC10_a3Inner, tateC10_vc_t]
  ring
```

## Scaled targets for `a2` and `a4`

The point is to prove inner-expression identities

```text
a2Inner = u^2 * A10(T),
a4Inner = u^4 * B10(T),
```

instead of expanding the final changed coefficients all at once.

For `a2`, use the following small target.  Let `e = 2p-1`.  Since `T = -1/e`,

```text
u^2 * A10(T)
= -(e^6 - 2e^5 - 5e^4 - 5e^2 + 2e + 1)/(32*den^2).
```

```lean
private def tateC10_a2ScaledTarget (p : ℚ) : ℚ :=
  -((2 * p - 1) ^ 6
      - 2 * (2 * p - 1) ^ 5
      - 5 * (2 * p - 1) ^ 4
      - 5 * (2 * p - 1) ^ 2
      + 2 * (2 * p - 1)
      + 1) / (32 * (tateC10_den p) ^ 2)

private def tateC10_a4ScaledTarget (p : ℚ) : ℚ :=
  p ^ 5 * (p - 1) ^ 5 / (tateC10_den p) ^ 3
```

Now prove the two target-evaluation lemmas.  These are the only places where `T=1/(1-2p)` is expanded.

```lean
private lemma tateC10_u_sq_mul_A10_eq_a2Target
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p) =
      tateC10_a2ScaledTarget p := by
  have h2 : 2 * p - 1 ≠ 0 := tateC10_two_mul_sub_one_ne_zero hpT
  dsimp [tateC10_u, tateC10_pToShortParam,
    tateC10_a2ScaledTarget, A10, F10]
  field_simp [hden, hpT, h2]
  ring

private lemma tateC10_u_pow4_mul_B10_eq_a4Target
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_u p ^ 4 * B10 (tateC10_pToShortParam p) =
      tateC10_a4ScaledTarget p := by
  have h2 : 2 * p - 1 ≠ 0 := tateC10_two_mul_sub_one_ne_zero hpT
  -- Prefer the already-compiled p-to-short identities over expanding `T` here.
  rw [B10]
  rw [pToShort_sq_sub_one (p := p) hpT]
  rw [pToShort_shortQ (p := p) hpT]
  dsimp [tateC10_u, tateC10_a4ScaledTarget]
  field_simp [hden, h2]
  ring
```

If the local theorem names/argument order for `pToShort_sq_sub_one` and `pToShort_shortQ` differ, use the local versions.  The intended identities are:

```lean
(tateC10_pToShortParam p)^2 - 1
  = -4*p*(p-1)/(2*p-1)^2

(tateC10_pToShortParam p)^2 - 4*tateC10_pToShortParam p - 1
  = -4*tateC10_den p/(2*p-1)^2
```

## Inner algebra lemmas

These contain no `T`; they only clear powers of `tateC10_den p`.

```lean
private lemma tateC10_a2Inner_eq_a2Target
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a2Inner p = tateC10_a2ScaledTarget p := by
  dsimp [tateC10_a2Inner, tateC10_a2ScaledTarget,
    tateC10_b, tateC10_c, tateC10_r, tateC10_s, tateC10_den]
  field_simp [hden]
  ring

private lemma tateC10_a4Inner_eq_a4Target
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a4Inner p = tateC10_a4ScaledTarget p := by
  dsimp [tateC10_a4Inner, tateC10_a4ScaledTarget,
    tateC10_b, tateC10_c, tateC10_r, tateC10_s, tateC10_vc_t, tateC10_den]
  field_simp [hden]
  ring

private lemma tateC10_a6Inner_eq_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a6Inner p = 0 := by
  dsimp [tateC10_a6Inner,
    tateC10_b, tateC10_c, tateC10_r, tateC10_s, tateC10_vc_t, tateC10_den]
  field_simp [hden]
  ring
```

If `a4` or `a6` is still too slow, split exactly as in Q3010: introduce `D`, `B`, `C`, `R`, `S`, `V` local numerator variables and first prove generic clearing lemmas.  In my view, try the displayed version first; the expressions are much smaller than one full curve `ext` proof.

Now combine target-evaluation and inner algebra:

```lean
private lemma tateC10_a2Inner_eq_u_sq_A10
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_a2Inner p =
      tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p) := by
  rw [tateC10_a2Inner_eq_a2Target hden]
  rw [tateC10_u_sq_mul_A10_eq_a2Target hden hpT]

private lemma tateC10_a4Inner_eq_u_pow4_B10
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_a4Inner p =
      tateC10_u p ^ 4 * B10 (tateC10_pToShortParam p) := by
  rw [tateC10_a4Inner_eq_a4Target hden]
  rw [tateC10_u_pow4_mul_B10_eq_a4Target hden hpT]
```

## Tiny cancellation lemmas

These keep the coefficient proofs independent of `field_simp` on large rational expressions.

```lean
private lemma inv_mul_self_mul_cancel
    {u x : ℚ} (hu : u ≠ 0) :
    u⁻¹ * (u * x) = x := by
  field_simp [hu]

private lemma inv_sq_mul_sq_mul_cancel
    {u x : ℚ} (hu : u ≠ 0) :
    u⁻¹ ^ 2 * (u ^ 2 * x) = x := by
  field_simp [hu]
  ring

private lemma inv_pow3_mul_zero (u : ℚ) :
    u⁻¹ ^ 3 * 0 = 0 := by ring

private lemma inv_pow4_mul_pow4_mul_cancel
    {u x : ℚ} (hu : u ≠ 0) :
    u⁻¹ ^ 4 * (u ^ 4 * x) = x := by
  field_simp [hu]
  ring

private lemma inv_pow6_mul_zero (u : ℚ) :
    u⁻¹ ^ 6 * 0 = 0 := by ring
```

## Five coefficient lemmas

These are written to match Mathlib’s standard `variableChange_a₁` etc. theorem shapes.  If your local lemmas state division by `u^k` instead of multiplication by `u⁻¹^k`, replace the `change` line with the corresponding division form; the inner lemmas remain the same.

```lean
theorem tateC10_variableChange_a₁
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p)).a₁ =
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).a₁ := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp [tateW, shortW, tateC10_pToShortVC,
    tateC10_a1Inner, tateC10_a1Inner_eq_zero]

theorem tateC10_variableChange_a₂
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p)).a₂ =
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).a₂ := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [tateW, shortW, tateC10_pToShortVC,
    tateC10_a2Inner]
  change (tateC10_u p)⁻¹ ^ 2 * tateC10_a2Inner p =
    A10 (tateC10_pToShortParam p)
  rw [tateC10_a2Inner_eq_u_sq_A10 hden hpT]
  exact inv_sq_mul_sq_mul_cancel (tateC10_u_ne_zero hden hpT)

theorem tateC10_variableChange_a₃
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p)).a₃ =
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).a₃ := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [tateW, shortW, tateC10_pToShortVC,
    tateC10_a3Inner, tateC10_a3Inner_eq_zero]

theorem tateC10_variableChange_a₄
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p)).a₄ =
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).a₄ := by
  rw [WeierstrassCurve.variableChange_a₄]
  simp [tateW, shortW, tateC10_pToShortVC,
    tateC10_a4Inner]
  change (tateC10_u p)⁻¹ ^ 4 * tateC10_a4Inner p =
    B10 (tateC10_pToShortParam p)
  rw [tateC10_a4Inner_eq_u_pow4_B10 hden hpT]
  exact inv_pow4_mul_pow4_mul_cancel (tateC10_u_ne_zero hden hpT)

theorem tateC10_variableChange_a₆
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p)).a₆ =
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).a₆ := by
  rw [WeierstrassCurve.variableChange_a₆]
  simp [tateW, shortW, tateC10_pToShortVC,
    tateC10_a6Inner]
  change (tateC10_u p)⁻¹ ^ 6 * tateC10_a6Inner p = 0
  rw [tateC10_a6Inner_eq_zero hden]
  ring
```

## Final curve equality

```lean
theorem tateC10_variableChange_eq_shortW
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_pToShortVC p hden hpT •
        tateW (tateC10_b p) (tateC10_c p) =
      shortW (A10 (tateC10_pToShortParam p))
             (B10 (tateC10_pToShortParam p)) := by
  ext <;>
    simp [tateC10_variableChange_a₁ hden hpT,
      tateC10_variableChange_a₂ hden hpT,
      tateC10_variableChange_a₃ hden hpT,
      tateC10_variableChange_a₄ hden hpT,
      tateC10_variableChange_a₆ hden hpT]
```

If `ext` does not pick up the coefficient fields in the local Mathlib version, use the generated ext theorem directly, usually one of:

```lean
  apply WeierstrassCurve.ext
  · exact tateC10_variableChange_a₁ hden hpT
  · exact tateC10_variableChange_a₂ hden hpT
  · exact tateC10_variableChange_a₃ hden hpT
  · exact tateC10_variableChange_a₄ hden hpT
  · exact tateC10_variableChange_a₆ hden hpT
```

or the local N12 pattern.

## Verification checklist

1. First check only the definitions and nonzero lemmas:

```bash
lake env lean FLT/Assumptions/MazurProof/KubertBridgeN10.lean
```

2. Then add/check the inner lemmas in this order:

```text
tateC10_a1Inner_eq_zero
tateC10_a3Inner_eq_zero
tateC10_u_sq_mul_A10_eq_a2Target
tateC10_a2Inner_eq_a2Target
tateC10_u_pow4_mul_B10_eq_a4Target
tateC10_a4Inner_eq_a4Target
tateC10_a6Inner_eq_zero
```

3. Then check the five coefficient lemmas.  Any failure here is likely only a mismatch with the exact local shape of `WeierstrassCurve.variableChange_aᵢ`; the inner algebra should not need to change.

4. Finally run:

```lean
#print axioms tateC10_variableChange_eq_shortW
```

Expected: no new axioms.  The only imported axioms should be whatever the surrounding file already has; the variable-change equality itself should be pure definitions plus `ring`/`field_simp`.
