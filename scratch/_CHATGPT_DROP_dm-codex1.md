# Q3014 (dm-codex1): robust C10 a4/a6 numerator-clearing proofs

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

This mirrors the successful a2 proof: keep the C10 denominator as a symbolic `D` while clearing denominators, then unfold the polynomial definitions only after all denominators are gone.

I did not run local Lean, but the code below is designed to be patchable in the same style as your checked a2 layer.  It avoids `native_decide`, `sorry`, and new axioms.

## 0. Inner definitions, if not already present

Use these only if the file does not already contain them.

```lean
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

## 1. Common numerator layer for a4/a6

These are intentionally named `a46...` to avoid collisions with the a2 proof helpers.

```lean
private def tateC10_a46Bnum (p : ℚ) : ℚ :=
  p ^ 3 * (p - 1) * (2 * p - 1)

private def tateC10_a46Cnum (p : ℚ) : ℚ :=
  -p * (p - 1) * (2 * p - 1)

private def tateC10_a46Rnum (p : ℚ) : ℚ :=
  -p ^ 3 * (p - 1)

/-- Numerator of `tateC10_vc_t p`, with denominator `2*D^2`. -/
private def tateC10_a46Vnum (p : ℚ) : ℚ :=
  tateC10_a46Bnum p
    - tateC10_a46Rnum p * (tateC10_den p - tateC10_a46Cnum p)

private lemma tateC10_two_mul_sub_one_ne_zero_of_hpT_a46
    {p : ℚ} (hpT : 1 - 2 * p ≠ 0) :
    2 * p - 1 ≠ 0 := by
  rw [show 2 * p - 1 = -(1 - 2 * p) by ring]
  exact neg_ne_zero.mpr hpT

/-- Generic proof that the `t` translation has numerator `B - R*(D-C)`. -/
private lemma tateC10_vc_t_generic
    (B C R D : ℚ) (hD : D ≠ 0) :
    (B / D ^ 2 - (R / D) * (1 - C / D)) / 2 =
      (B - R * (D - C)) / (2 * D ^ 2) := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  dsimp
  field_simp [hD, hD2]
  ring

private lemma tateC10_vc_t_eq_Vnum_div
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_vc_t p =
      tateC10_a46Vnum p / (2 * (tateC10_den p) ^ 2) := by
  let D : ℚ := tateC10_den p
  let B : ℚ := tateC10_a46Bnum p
  let C : ℚ := tateC10_a46Cnum p
  let R : ℚ := tateC10_a46Rnum p
  have hD : D ≠ 0 := by
    simpa [D] using hden
  calc
    tateC10_vc_t p
        = (B / D ^ 2 - (R / D) * (1 - C / D)) / 2 := by
            simp [D, B, C, R, tateC10_vc_t, tateC10_b, tateC10_c,
              tateC10_r, tateC10_a46Bnum, tateC10_a46Cnum,
              tateC10_a46Rnum]
    _ = (B - R * (D - C)) / (2 * D ^ 2) :=
            tateC10_vc_t_generic B C R D hD
    _ = tateC10_a46Vnum p / (2 * (tateC10_den p) ^ 2) := by
            simp [D, B, C, R, tateC10_a46Vnum]
```

## 2. Robust a4 proof

The generic a4 expression uses:

```text
b = B/D^2,
c = C/D,
r = R/D,
s = (C/D - 1)/2,
t = V/(2D^2).
```

The key cancellation is that the `V` terms disappear from the a4 numerator.

```lean
private def tateC10_a4Generic (B C R V D : ℚ) : ℚ :=
  - ((C / D - 1) / 2) * (-(B / D ^ 2))
    + 2 * (R / D) * (-(B / D ^ 2))
    - (V / (2 * D ^ 2) + (R / D) * ((C / D - 1) / 2)) * (1 - C / D)
    + 3 * (R / D) ^ 2
    - 2 * ((C / D - 1) / 2) * (V / (2 * D ^ 2))

/-- Cleared a4 numerator.  With `S=C-D`, this is
`S*B - 4*R*B + R*S^2 + 6*R^2*D`. -/
private def tateC10_a4GenericNum (B C R D : ℚ) : ℚ :=
  (C - D) * B - 4 * R * B + R * (C - D) ^ 2 + 6 * R ^ 2 * D

private lemma tateC10_a4Generic_clear
    (B C R V D : ℚ) (hD : D ≠ 0) :
    2 * D ^ 3 * tateC10_a4Generic B C R V D =
      tateC10_a4GenericNum B C R D := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  dsimp [tateC10_a4Generic, tateC10_a4GenericNum]
  field_simp [hD, hD2, hD3]
  ring

private lemma tateC10_a4Inner_eq_generic
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a4Inner p =
      tateC10_a4Generic
        (tateC10_a46Bnum p)
        (tateC10_a46Cnum p)
        (tateC10_a46Rnum p)
        (tateC10_a46Vnum p)
        (tateC10_den p) := by
  rw [tateC10_vc_t_eq_Vnum_div hden]
  dsimp [tateC10_a4Inner, tateC10_a4Generic,
    tateC10_b, tateC10_c, tateC10_r, tateC10_s,
    tateC10_a46Bnum, tateC10_a46Cnum, tateC10_a46Rnum]
  ring

private def tateC10_a4Num (p : ℚ) : ℚ :=
  2 * p ^ 5 * (p - 1) ^ 5

private lemma tateC10_a4GenericNum_eq_a4Num (p : ℚ) :
    tateC10_a4GenericNum
        (tateC10_a46Bnum p)
        (tateC10_a46Cnum p)
        (tateC10_a46Rnum p)
        (tateC10_den p) =
      tateC10_a4Num p := by
  dsimp [tateC10_a4GenericNum, tateC10_a4Num,
    tateC10_a46Bnum, tateC10_a46Cnum, tateC10_a46Rnum, tateC10_den]
  ring

private lemma tateC10_a4Inner_num
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    2 * (tateC10_den p) ^ 3 * tateC10_a4Inner p =
      tateC10_a4Num p := by
  rw [tateC10_a4Inner_eq_generic hden]
  rw [tateC10_a4Generic_clear
    (tateC10_a46Bnum p)
    (tateC10_a46Cnum p)
    (tateC10_a46Rnum p)
    (tateC10_a46Vnum p)
    (tateC10_den p)
    hden]
  exact tateC10_a4GenericNum_eq_a4Num p
```

Now prove the target side using the already checked `pToShort_sq_sub_one` and `pToShort_shortQ` identities.

```lean
private lemma tateC10_u_pow4_B10_num
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    2 * (tateC10_den p) ^ 3 *
        (tateC10_u p ^ 4 * B10 (tateC10_pToShortParam p)) =
      tateC10_a4Num p := by
  have h2 : 2 * p - 1 ≠ 0 :=
    tateC10_two_mul_sub_one_ne_zero_of_hpT_a46 hpT
  have h2sq : (2 * p - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h2
  dsimp [B10]
  rw [pToShort_sq_sub_one (p := p) hpT]
  rw [pToShort_shortQ (p := p) hpT]
  dsimp [tateC10_u, tateC10_a4Num]
  field_simp [hden, h2, h2sq]
  ring

private lemma tateC10_a4Scale_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    2 * (tateC10_den p) ^ 3 ≠ 0 := by
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hden)

private lemma tateC10_a46_eq_of_mul_eq_mul_left
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

private lemma tateC10_a4Inner_eq_u_pow4_B10
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_a4Inner p =
      tateC10_u p ^ 4 * B10 (tateC10_pToShortParam p) := by
  let K : ℚ := 2 * (tateC10_den p) ^ 3
  have hK : K ≠ 0 := by
    simpa [K] using tateC10_a4Scale_ne_zero hden
  apply tateC10_a46_eq_of_mul_eq_mul_left (k := K) hK
  calc
    K * tateC10_a4Inner p = tateC10_a4Num p := by
      simpa [K] using tateC10_a4Inner_num hden
    _ = K * (tateC10_u p ^ 4 * B10 (tateC10_pToShortParam p)) := by
      symm
      simpa [K] using tateC10_u_pow4_B10_num hden hpT
```

## 3. Robust a6 proof

For a6, clear `4*D^4`; the resulting polynomial numerator is zero after substitution.

```lean
private def tateC10_a6Generic (B C R V D : ℚ) : ℚ :=
  (R / D) ^ 2 * (-(B / D ^ 2))
    + (R / D) ^ 3
    - (V / (2 * D ^ 2)) * (-(B / D ^ 2))
    - (V / (2 * D ^ 2)) ^ 2
    - (R / D) * (V / (2 * D ^ 2)) * (1 - C / D)

/-- Cleared a6 numerator.  With `S=C-D`, this is
`-4R^2B + 4R^3D + 2VB - V^2 + 2RVS`. -/
private def tateC10_a6GenericNum (B C R V D : ℚ) : ℚ :=
  -4 * R ^ 2 * B + 4 * R ^ 3 * D + 2 * V * B - V ^ 2 +
    2 * R * V * (C - D)

private lemma tateC10_a6Generic_clear
    (B C R V D : ℚ) (hD : D ≠ 0) :
    4 * D ^ 4 * tateC10_a6Generic B C R V D =
      tateC10_a6GenericNum B C R V D := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hD4 : D ^ 4 ≠ 0 := pow_ne_zero 4 hD
  dsimp [tateC10_a6Generic, tateC10_a6GenericNum]
  field_simp [hD, hD2, hD3, hD4]
  ring

private lemma tateC10_a6Inner_eq_generic
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a6Inner p =
      tateC10_a6Generic
        (tateC10_a46Bnum p)
        (tateC10_a46Cnum p)
        (tateC10_a46Rnum p)
        (tateC10_a46Vnum p)
        (tateC10_den p) := by
  rw [tateC10_vc_t_eq_Vnum_div hden]
  dsimp [tateC10_a6Inner, tateC10_a6Generic,
    tateC10_b, tateC10_c, tateC10_r,
    tateC10_a46Bnum, tateC10_a46Cnum, tateC10_a46Rnum]
  ring

private lemma tateC10_a6GenericNum_eq_zero (p : ℚ) :
    tateC10_a6GenericNum
        (tateC10_a46Bnum p)
        (tateC10_a46Cnum p)
        (tateC10_a46Rnum p)
        (tateC10_a46Vnum p)
        (tateC10_den p) = 0 := by
  dsimp [tateC10_a6GenericNum,
    tateC10_a46Bnum, tateC10_a46Cnum, tateC10_a46Rnum,
    tateC10_a46Vnum, tateC10_den]
  ring

private lemma tateC10_a6Inner_num_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    4 * (tateC10_den p) ^ 4 * tateC10_a6Inner p = 0 := by
  rw [tateC10_a6Inner_eq_generic hden]
  rw [tateC10_a6Generic_clear
    (tateC10_a46Bnum p)
    (tateC10_a46Cnum p)
    (tateC10_a46Rnum p)
    (tateC10_a46Vnum p)
    (tateC10_den p)
    hden]
  exact tateC10_a6GenericNum_eq_zero p

private lemma tateC10_a6Scale_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    4 * (tateC10_den p) ^ 4 ≠ 0 := by
  exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hden)

private lemma tateC10_eq_zero_of_mul_eq_zero_left
    {k x : ℚ} (hk : k ≠ 0) (h : k * x = 0) :
    x = 0 := by
  exact (mul_eq_zero.mp h).resolve_left hk

private lemma tateC10_a6Inner_eq_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    tateC10_a6Inner p = 0 := by
  let K : ℚ := 4 * (tateC10_den p) ^ 4
  have hK : K ≠ 0 := by
    simpa [K] using tateC10_a6Scale_ne_zero hden
  exact tateC10_eq_zero_of_mul_eq_zero_left hK
    (by simpa [K] using tateC10_a6Inner_num_zero hden)
```

## 4. Coefficient lemmas

These assume your a1/a2/a3 coefficient proofs already follow the local N12/Mathlib style.  If the exact RHS after `rw [WeierstrassCurve.variableChange_a₄]` differs syntactically, keep the numerator lemmas above and adjust only the `change` line.

```lean
theorem tateC10_variableChange_a4
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
  field_simp [tateC10_u_ne_zero hden hpT]
  ring

theorem tateC10_variableChange_a6
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

## 5. If a generic-clear lemma still times out

The likely bottleneck, if any, is not the final polynomial identity but the generic `field_simp`.  In that case, keep the same statements and replace the generic-clear proof body with:

```lean
  dsimp [tateC10_a4Generic, tateC10_a4GenericNum]
  ring_nf
  field_simp [hD]
  ring
```

or similarly for a6.  Since the generic lemmas are in variables `B C R V D`, this is still far smaller and safer than expanding `tateC10_den p` inside the rational expression.
