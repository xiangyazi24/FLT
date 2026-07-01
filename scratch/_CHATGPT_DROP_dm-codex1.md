# Q3013 (dm-codex1): robust C10 a2 numerator-clearing proof

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

This is a patchable a2-only replacement.  The key point is: **do not expand `tateC10_den p` while denominators are present**.  Clear denominators in a generic lemma with a local denominator variable `D`; only after the expression is polynomial should `tateC10_den` be unfolded and discharged by `ring`.

The final lemma you want for the a2 coefficient proof is:

```lean
private lemma tateC10_a2Inner_eq_u_sq_A10
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_a2Inner p =
      tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p)
```

## Complete Lean code

Insert this after the existing definitions of `tateC10_a2Inner` and the light C10 VC layer.

```lean
/-- Stable spelling of the denominator form sometimes produced by `ring_nf`/`field_simp`. -/
private lemma tateC10_den_alt (p : ℚ) :
    1 - p * 3 + p ^ 2 = tateC10_den p := by
  dsimp [tateC10_den]
  ring

private lemma tateC10_den_alt_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    1 - p * 3 + p ^ 2 ≠ 0 := by
  rw [tateC10_den_alt p]
  exact hden

/-- Stable spelling of the square of the denominator sometimes produced by normalization. -/
private lemma tateC10_den_sq_alt (p : ℚ) :
    1 - p * 6 + 11 * p ^ 2 - 6 * p ^ 3 + p ^ 4 =
      (tateC10_den p) ^ 2 := by
  dsimp [tateC10_den]
  ring

private lemma tateC10_den_sq_alt_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    1 - p * 6 + 11 * p ^ 2 - 6 * p ^ 3 + p ^ 4 ≠ 0 := by
  rw [tateC10_den_sq_alt p]
  exact pow_ne_zero 2 hden

private lemma tateC10_two_mul_sub_one_ne_zero_of_hpT
    {p : ℚ} (hpT : 1 - 2 * p ≠ 0) :
    2 * p - 1 ≠ 0 := by
  rw [show 2 * p - 1 = -(1 - 2 * p) by ring]
  exact neg_ne_zero.mpr hpT

/-- Polynomial numerator for the scaled a2 target. -/
private def tateC10_a2Num (p : ℚ) : ℚ :=
  -((2 * p - 1) ^ 6
      - 2 * (2 * p - 1) ^ 5
      - 5 * (2 * p - 1) ^ 4
      - 5 * (2 * p - 1) ^ 2
      + 2 * (2 * p - 1)
      + 1)

private def tateC10_a2Bnum (p : ℚ) : ℚ :=
  p ^ 3 * (p - 1) * (2 * p - 1)

private def tateC10_a2Cnum (p : ℚ) : ℚ :=
  -p * (p - 1) * (2 * p - 1)

private def tateC10_a2Rnum (p : ℚ) : ℚ :=
  -p ^ 3 * (p - 1)

/-- Generic a2 inner expression with a symbolic denominator `D`.
Do not unfold `D` here. -/
private def tateC10_a2Generic (B C R D : ℚ) : ℚ :=
  -(B / D ^ 2)
    - ((C / D - 1) / 2) * (1 - C / D)
    + 3 * (R / D)
    - ((C / D - 1) / 2) ^ 2

/-- Generic numerator after clearing `32*D^2` from the a2 inner expression. -/
private def tateC10_a2GenericNum (B C R D : ℚ) : ℚ :=
  -32 * B + 96 * R * D + 8 * (C - D) ^ 2

/-- Denominator clearing for the generic a2 expression.  This is the only
`field_simp` step for the inner side, and it only sees the variable `D`, not
`tateC10_den p` expanded as a polynomial. -/
private lemma tateC10_a2Generic_clear
    (B C R D : ℚ) (hD : D ≠ 0) :
    32 * D ^ 2 * tateC10_a2Generic B C R D =
      tateC10_a2GenericNum B C R D := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  dsimp [tateC10_a2Generic, tateC10_a2GenericNum]
  field_simp [hD, hD2]
  ring

/-- The existing `tateC10_a2Inner` is exactly the generic expression with
`B,C,R,D` specialized.  This should be definitional after unfolding the C10
light layer. -/
private lemma tateC10_a2Inner_eq_generic (p : ℚ) :
    tateC10_a2Inner p =
      tateC10_a2Generic
        (tateC10_a2Bnum p)
        (tateC10_a2Cnum p)
        (tateC10_a2Rnum p)
        (tateC10_den p) := by
  rfl

/-- Cleared a2 inner expression, still in compact `B,C,R,D` form. -/
private lemma tateC10_a2Inner_clear_genericNum
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    32 * (tateC10_den p) ^ 2 * tateC10_a2Inner p =
      tateC10_a2GenericNum
        (tateC10_a2Bnum p)
        (tateC10_a2Cnum p)
        (tateC10_a2Rnum p)
        (tateC10_den p) := by
  rw [tateC10_a2Inner_eq_generic p]
  exact tateC10_a2Generic_clear
    (tateC10_a2Bnum p)
    (tateC10_a2Cnum p)
    (tateC10_a2Rnum p)
    (tateC10_den p)
    hden

/-- Once denominators are cleared, the numerator identity is pure polynomial algebra. -/
private lemma tateC10_a2GenericNum_eq_a2Num (p : ℚ) :
    tateC10_a2GenericNum
        (tateC10_a2Bnum p)
        (tateC10_a2Cnum p)
        (tateC10_a2Rnum p)
        (tateC10_den p) =
      tateC10_a2Num p := by
  dsimp [tateC10_a2GenericNum, tateC10_a2Bnum,
    tateC10_a2Cnum, tateC10_a2Rnum, tateC10_a2Num, tateC10_den]
  ring

/-- Cleared numerator identity for the a2 inner expression. -/
private lemma tateC10_a2Inner_num
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    32 * (tateC10_den p) ^ 2 * tateC10_a2Inner p =
      tateC10_a2Num p := by
  rw [tateC10_a2Inner_clear_genericNum hden]
  exact tateC10_a2GenericNum_eq_a2Num p

/-- Generic clearing for the `u^2 * A` side.  Again, the denominator is a
symbolic variable `D`, not the expanded C10 denominator. -/
private lemma tateC10_u_sq_clear_generic
    (e D A : ℚ) (hD : D ≠ 0) :
    32 * D ^ 2 * ((e ^ 3 / (8 * D)) ^ 2 * A) =
      (e ^ 6 / 2) * A := by
  have h8D : 8 * D ≠ 0 := mul_ne_zero (by norm_num) hD
  dsimp
  field_simp [hD, h8D]
  ring

private lemma tateC10_pToShortParam_eq_neg_inv_e
    {p : ℚ} (hpT : 1 - 2 * p ≠ 0) :
    tateC10_pToShortParam p = -(2 * p - 1)⁻¹ := by
  have h2 : 2 * p - 1 ≠ 0 :=
    tateC10_two_mul_sub_one_ne_zero_of_hpT hpT
  dsimp [tateC10_pToShortParam]
  rw [show 1 - 2 * p = -(2 * p - 1) by ring]
  field_simp [h2]
  ring

/-- Evaluation of `A10` at `T=-1/e`, written with a symbolic nonzero `e`. -/
private lemma tateC10_A10_eval_by_e
    (e : ℚ) (he : e ≠ 0) :
    (e ^ 6 / 2) * A10 (-e⁻¹) =
      -(e ^ 6 - 2 * e ^ 5 - 5 * e ^ 4 - 5 * e ^ 2 + 2 * e + 1) := by
  dsimp [A10, F10]
  field_simp [he]
  ring

/-- Evaluation of the scaled `A10(T)` side to the same numerator. -/
private lemma tateC10_A10_eval_a2Num
    {p : ℚ} (hpT : 1 - 2 * p ≠ 0) :
    ((2 * p - 1) ^ 6 / 2) * A10 (tateC10_pToShortParam p) =
      tateC10_a2Num p := by
  let e : ℚ := 2 * p - 1
  have he : e ≠ 0 := by
    simpa [e] using tateC10_two_mul_sub_one_ne_zero_of_hpT hpT
  have hT : tateC10_pToShortParam p = -e⁻¹ := by
    simpa [e] using tateC10_pToShortParam_eq_neg_inv_e hpT
  rw [hT]
  change (e ^ 6 / 2) * A10 (-e⁻¹) = tateC10_a2Num p
  rw [tateC10_A10_eval_by_e e he]
  dsimp [tateC10_a2Num, e]
  ring

/-- Cleared numerator identity for the `u^2 * A10(T)` side. -/
private lemma tateC10_u_sq_A10_num
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    32 * (tateC10_den p) ^ 2 *
        (tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p)) =
      tateC10_a2Num p := by
  let e : ℚ := 2 * p - 1
  let D : ℚ := tateC10_den p
  have hD : D ≠ 0 := by
    simpa [D] using hden
  calc
    32 * (tateC10_den p) ^ 2 *
        (tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p))
        = 32 * D ^ 2 *
            ((e ^ 3 / (8 * D)) ^ 2 * A10 (tateC10_pToShortParam p)) := by
            simp [D, e, tateC10_u]
    _ = (e ^ 6 / 2) * A10 (tateC10_pToShortParam p) := by
            exact tateC10_u_sq_clear_generic
              e D (A10 (tateC10_pToShortParam p)) hD
    _ = tateC10_a2Num p := by
            simpa [e] using tateC10_A10_eval_a2Num hpT

private lemma tateC10_a2Scale_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    32 * (tateC10_den p) ^ 2 ≠ 0 := by
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hden)

/-- Local cancellation helper over `ℚ`, avoiding reliance on a particular
`mul_left_cancel₀` import/name. -/
private lemma tateC10_eq_of_mul_eq_mul_left
    {k x y : ℚ} (hk : k ≠ 0) (h : k * x = k * y) :
    x = y := by
  have h' : k⁻¹ * (k * x) = k⁻¹ * (k * y) := by
    rw [h]
  calc
    x = k⁻¹ * (k * x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
    _ = k⁻¹ * (k * y) := h'
    _ = y := by
      rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-- Final robust a2 identity.  Use this in the a2 coefficient proof. -/
private lemma tateC10_a2Inner_eq_u_sq_A10
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_a2Inner p =
      tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p) := by
  let K : ℚ := 32 * (tateC10_den p) ^ 2
  have hK : K ≠ 0 := by
    simpa [K] using tateC10_a2Scale_ne_zero hden
  apply tateC10_eq_of_mul_eq_mul_left (k := K) hK
  calc
    K * tateC10_a2Inner p = tateC10_a2Num p := by
      simpa [K] using tateC10_a2Inner_num hden
    _ = K * (tateC10_u p ^ 2 * A10 (tateC10_pToShortParam p)) := by
      symm
      simpa [K] using tateC10_u_sq_A10_num hden hpT
```

## If `rfl` fails in `tateC10_a2Inner_eq_generic`

If your local definitions have slightly different associativity than the prompt, replace that proof by this more tolerant version:

```lean
private lemma tateC10_a2Inner_eq_generic (p : ℚ) :
    tateC10_a2Inner p =
      tateC10_a2Generic
        (tateC10_a2Bnum p)
        (tateC10_a2Cnum p)
        (tateC10_a2Rnum p)
        (tateC10_den p) := by
  dsimp [tateC10_a2Inner, tateC10_a2Generic,
    tateC10_b, tateC10_c, tateC10_r, tateC10_s,
    tateC10_a2Bnum, tateC10_a2Cnum, tateC10_a2Rnum]
  ring
```

That `ring` is safe: it is not clearing denominators; it is only rearranging identical rational expressions.

## How to use in the coefficient proof

After `rw [WeierstrassCurve.variableChange_a₂]` and simplification down to the standard Mathlib formula, you should aim for the scaled form:

```lean
change (tateC10_u p)⁻¹ ^ 2 * tateC10_a2Inner p =
  A10 (tateC10_pToShortParam p)
rw [tateC10_a2Inner_eq_u_sq_A10 hden hpT]
field_simp [tateC10_u_ne_zero hden hpT]
ring
```

If you want to avoid even this last small `field_simp`, use your existing cancellation lemma:

```lean
have hu : tateC10_u p ≠ 0 := tateC10_u_ne_zero hden hpT
rw [tateC10_a2Inner_eq_u_sq_A10 hden hpT]
field_simp [hu]
ring
```

This final field simplification only sees the single nonzero value `tateC10_u p`; it does not involve the C10 denominator polynomial.
