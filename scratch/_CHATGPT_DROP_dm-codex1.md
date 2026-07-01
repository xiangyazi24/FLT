# Q2944 (dm-codex1): pure algebra parametrization for `tateC12_K = 0`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

## Main answer

Use the inverse parameter

```lean
q = -1 - 2 * (b - c)^2 / (c * (b - c - c^2))
```

Equivalently, with

```lean
r = (b - c) / c,
```

this is

```lean
q = (2 * r^2 + r - c) / (c - r).
```

The denominator needed for the displayed inverse formula is exactly

```lean
c * (b - c - c^2) ≠ 0,
```

so the hypotheses `hc : c ≠ 0` and `h6 : b - c - c^2 ≠ 0` are the right pole-removal hypotheses.  The remaining denominator `q + 1` is nonzero because `hK` and `hc` imply `b - c ≠ 0`, equivalently `r ≠ 0`, and then

```lean
q + 1 = 2 * r^2 / (c - r).
```

No extra side condition is needed for the rational parametrization over `ℚ` beyond the current `hb`, `hc`, `h6`, and `hK`.  The only caveat is the field

```lean
hthree_q_sq_sub_one : 3 * q^2 - 1 ≠ 0
```

inside `TateC12Good`: over `ℚ` this is an independent rational no-square lemma, not a consequence of the quartic algebra.  If this parametrization is ever generalized from `ℚ` to an arbitrary field containing `sqrt (1/3)`, then `3*q^2 - 1 ≠ 0` must be supplied by the exact-order side condition; `K=0`, `b≠0`, `c≠0`, and `b-c-c^2≠0` do not force it over such a field.

The core algebra is best done through the auxiliary variable `r = (b-c)/c`.  The quartic becomes a quadratic-in-`c` relation:

```lean
tateC12_K b c =
  c^4 *
    (c^2 - c * r * (r^2 + 3*r + 2) +
      r^2 * (3*r^2 + 3*r + 1)).
```

For

```lean
q = (2*r^2 + r - c)/(c-r),
```

the two decisive identities are

```lean
q * (q - 1) / (q + 1) = r
r * (3*q^2 + 1) / (q + 1)^2 = c
```

under the single relation

```lean
c^2 - c * r * (r^2 + 3*r + 2) +
  r^2 * (3*r^2 + 3*r + 1) = 0.
```

Then

```lean
tateC12_c q
  = (q * (q - 1) / (q + 1)) * ((3*q^2 + 1) / (q + 1)^2)
  = c
```

and

```lean
b = c * (1 + r)
  = tateC12_c q * ((q^2 + 1)/(q + 1))
  = tateC12_b q.
```

## Lean insertion snippets

These snippets are intended to be pasted into `KubertBridgeN12.lean` after the definitions of `tateC12_K`, `tateC12_b`, and `tateC12_c`.

```lean
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN12

noncomputable section

private def tateC12_rInv (b c : ℚ) : ℚ :=
  (b - c) / c

private def tateC12_qInv (b c : ℚ) : ℚ :=
  -1 - 2 * (b - c)^2 / (c * (b - c - c^2))

private lemma tateC12_K_r_identity
    (b c : ℚ) (hc : c ≠ 0) :
    let r : ℚ := tateC12_rInv b c
    tateC12_K b c =
      c^4 *
        (c^2 - c * r * (r^2 + 3*r + 2) +
          r^2 * (3*r^2 + 3*r + 1)) := by
  dsimp [tateC12_rInv]
  field_simp [hc, tateC12_K]
  ring

private lemma tateC12_qInv_rform
    (b c : ℚ) (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0) :
    let r : ℚ := tateC12_rInv b c
    tateC12_qInv b c = (2*r^2 + r - c) / (c - r) := by
  dsimp [tateC12_qInv, tateC12_rInv]
  field_simp [hc, h6]
  ring

private lemma tateC12_c_sub_r_ne_zero
    (b c : ℚ) (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0) :
    c - tateC12_rInv b c ≠ 0 := by
  have hrewrite : c - tateC12_rInv b c = -(b - c - c^2) / c := by
    dsimp [tateC12_rInv]
    field_simp [hc]
    ring
  rw [hrewrite]
  exact div_ne_zero (neg_ne_zero.mpr h6) hc

private lemma tateC12_r_ne_zero_of_K
    {b c : ℚ} (hc : c ≠ 0) (hK : tateC12_K b c = 0) :
    tateC12_rInv b c ≠ 0 := by
  let r : ℚ := tateC12_rInv b c
  have hKid := tateC12_K_r_identity b c hc
  have hF : c^2 - c * r * (r^2 + 3*r + 2) +
      r^2 * (3*r^2 + 3*r + 1) = 0 := by
    have hc4 : c^4 ≠ 0 := pow_ne_zero 4 hc
    have hmul : c^4 *
        (c^2 - c * r * (r^2 + 3*r + 2) +
          r^2 * (3*r^2 + 3*r + 1)) = 0 := by
      simpa [r, hK] using hKid.symm
    exact (mul_eq_zero.mp hmul).resolve_left hc4
  intro hr0
  have hc2 : c^2 = 0 := by
    simpa [r, hr0] using hF
  exact hc (sq_eq_zero_iff.mp hc2)

/-- Ring certificate 1: the inverse parameter recovers `r=(b-c)/c`. -/
private lemma tateC12_qInv_recovers_r
    {r c : ℚ}
    (hF : c^2 - c * r * (r^2 + 3*r + 2) +
      r^2 * (3*r^2 + 3*r + 1) = 0)
    (hr : r ≠ 0) (hcr : c - r ≠ 0) :
    let q : ℚ := (2*r^2 + r - c) / (c - r)
    q * (q - 1) / (q + 1) = r := by
  dsimp
  field_simp [hr, hcr]
  ring_nf at hF ⊢
  exact hF

/-- Ring certificate 2: the inverse parameter recovers `c`. -/
private lemma tateC12_qInv_recovers_c
    {r c : ℚ}
    (hF : c^2 - c * r * (r^2 + 3*r + 2) +
      r^2 * (3*r^2 + 3*r + 1) = 0)
    (hr : r ≠ 0) (hcr : c - r ≠ 0) :
    let q : ℚ := (2*r^2 + r - c) / (c - r)
    r * (3*q^2 + 1) / (q + 1)^2 = c := by
  dsimp
  field_simp [hr, hcr]
  ring_nf at hF ⊢
  exact hF

private lemma tateC12_qInv_add_one_ne_zero
    {r c : ℚ} (hr : r ≠ 0) (hcr : c - r ≠ 0) :
    let q : ℚ := (2*r^2 + r - c) / (c - r)
    q + 1 ≠ 0 := by
  dsimp
  have hq1 : (2*r^2 + r - c) / (c - r) + 1 = 2*r^2 / (c - r) := by
    field_simp [hcr]
    ring
  rw [hq1]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) hcr

private lemma tateC12_c_factor_identity
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_c q =
      (q * (q - 1) / (q + 1)) *
        ((3*q^2 + 1) / (q + 1)^2) := by
  field_simp [tateC12_c, hq1]
  ring

private lemma tateC12_b_factor_identity
    (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_b q = tateC12_c q * ((q^2 + 1) / (q + 1)) := by
  field_simp [tateC12_b, tateC12_c, hq1]
  ring

private lemma tateC12_b_eq_c_mul_one_add_r
    (b c : ℚ) (hc : c ≠ 0) :
    b = c * (1 + tateC12_rInv b c) := by
  dsimp [tateC12_rInv]
  field_simp [hc]
  ring
```

## Core parametrization theorem

I recommend first proving the core theorem without the three rational/no-square `TateC12Good` decorations.  This is the clean algebraic residual.

```lean
theorem tateC12_K_parametrization_core
    {b c : ℚ}
    (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0)
    (hK : tateC12_K b c = 0) :
    ∃ q : ℚ,
      q ≠ 0 ∧ q - 1 ≠ 0 ∧ q + 1 ≠ 0 ∧
      b = tateC12_b q ∧ c = tateC12_c q := by
  let r : ℚ := tateC12_rInv b c
  let q : ℚ := tateC12_qInv b c
  have hq_rform : q = (2*r^2 + r - c) / (c - r) := by
    simpa [q, r] using tateC12_qInv_rform b c hc h6
  have hcr : c - r ≠ 0 := by
    simpa [r] using tateC12_c_sub_r_ne_zero b c hc h6
  have hr : r ≠ 0 := by
    simpa [r] using tateC12_r_ne_zero_of_K (b := b) (c := c) hc hK
  have hKid := tateC12_K_r_identity b c hc
  have hF : c^2 - c * r * (r^2 + 3*r + 2) +
      r^2 * (3*r^2 + 3*r + 1) = 0 := by
    have hc4 : c^4 ≠ 0 := pow_ne_zero 4 hc
    have hmul : c^4 *
        (c^2 - c * r * (r^2 + 3*r + 2) +
          r^2 * (3*r^2 + 3*r + 1)) = 0 := by
      simpa [r, hK] using hKid.symm
    exact (mul_eq_zero.mp hmul).resolve_left hc4
  have hqr : q * (q - 1) / (q + 1) = r := by
    rw [hq_rform]
    simpa using tateC12_qInv_recovers_r (r := r) (c := c) hF hr hcr
  have hqc : r * (3*q^2 + 1) / (q + 1)^2 = c := by
    rw [hq_rform]
    simpa using tateC12_qInv_recovers_c (r := r) (c := c) hF hr hcr
  have hq1 : q + 1 ≠ 0 := by
    rw [hq_rform]
    simpa using tateC12_qInv_add_one_ne_zero (r := r) (c := c) hr hcr
  have hc_param : c = tateC12_c q := by
    calc
      c = r * (3*q^2 + 1) / (q + 1)^2 := by rw [hqc]
      _ = (q * (q - 1) / (q + 1)) *
          ((3*q^2 + 1) / (q + 1)^2) := by rw [hqr]
      _ = tateC12_c q := by rw [tateC12_c_factor_identity q hq1]
  have hratio : (q^2 + 1) / (q + 1) = 1 + r := by
    calc
      (q^2 + 1) / (q + 1)
          = q * (q - 1) / (q + 1) + 1 := by
              field_simp [hq1]
              ring
      _ = r + 1 := by rw [hqr]
      _ = 1 + r := by ring
  have hb_param : b = tateC12_b q := by
    calc
      b = c * (1 + r) := tateC12_b_eq_c_mul_one_add_r b c hc
      _ = tateC12_c q * ((q^2 + 1) / (q + 1)) := by
            rw [← hc_param, hratio]
      _ = tateC12_b q := by rw [tateC12_b_factor_identity q hq1]
  have hq0 : q ≠ 0 := by
    intro hq0
    have hr0 : r = 0 := by
      simpa [hq0] using hqr.symm
    exact hr hr0
  have hq_sub_one : q - 1 ≠ 0 := by
    intro hq_sub
    have hqeq : q = 1 := sub_eq_zero.mp hq_sub
    have hr0 : r = 0 := by
      simpa [hqeq] using hqr.symm
    exact hr hr0
  exact ⟨q, hq0, hq_sub_one, hq1, hb_param, hc_param⟩
```

## Assembling `TateC12Good`

For the current theorem exactly as stated, use the core theorem and fill the remaining `TateC12Good` fields.  The positivity fields are easy over `ℚ`; the `3*q^2 - 1` field is a standalone no-rational-square lemma.

```lean
private lemma rat_three_mul_sq_sub_one_ne_zero (q : ℚ) :
    (3 : ℚ) * q^2 - 1 ≠ 0 := by
  intro h
  have hsq : q^2 = (1 : ℚ) / 3 := by
    nlinarith
  have hs : IsSquare ((1 : ℚ) / 3) := ⟨q, hsq.symm⟩
  -- `norm_num` knows that `1/3` is not a rational square in recent Mathlib.
  -- If this does not fire in the local Mathlib snapshot, replace this line by
  -- the existing squareclass/no-square lemma used elsewhere in the FLT descent files.
  norm_num at hs

theorem tateC12_K_parametrization
    {b c : ℚ}
    (hb : b ≠ 0) (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0)
    (hK : tateC12_K b c = 0) :
    ∃ q : ℚ, TateC12Good q ∧ b = tateC12_b q ∧ c = tateC12_c q := by
  rcases tateC12_K_parametrization_core (b := b) (c := c) hc h6 hK with
    ⟨q, hq0, hqsub, hqadd, hbq, hcq⟩
  have hq_sq_add_one : q^2 + 1 ≠ 0 := by
    have hpos : (0 : ℚ) < q^2 + 1 := by nlinarith [sq_nonneg q]
    exact ne_of_gt hpos
  have hone_add_three_q_sq : 1 + 3 * q^2 ≠ 0 := by
    have hpos : (0 : ℚ) < 1 + 3 * q^2 := by nlinarith [sq_nonneg q]
    exact ne_of_gt hpos
  refine ⟨q, ?_, hbq, hcq⟩
  exact
    { hq_ne_zero := hq0
      hq_sub_one := hqsub
      hq_add_one := hqadd
      hq_sq_add_one := hq_sq_add_one
      hone_add_three_q_sq := hone_add_three_q_sq
      hthree_q_sq_sub_one := rat_three_mul_sq_sub_one_ne_zero q }
```

## Why this is the right inverse

Starting from the known parametrization,

```lean
c = q*(q-1)*(3*q^2+1)/(q+1)^3
b = c * (q^2+1)/(q+1),
```

one gets

```lean
b - c = c * q*(q-1)/(q+1)
```

and a direct simplification gives

```lean
b - c - c^2 = -2 * q^3 * (q-1)^3 * (3*q^2+1) / (q+1)^6.
```

Therefore

```lean
q + 1 = -2 * (b - c)^2 / (c * (b - c - c^2)),
```

which is exactly the displayed inverse formula for `q`.

The pole `b - c - c^2 = 0` is therefore not an accidental artifact of the derivation; it is the natural missing denominator of the inverse map.  In the Tate-normal-form/order-12 pipeline it should be discharged upstream from the exact-order/non-lower-order hypotheses; in this pure algebra theorem it is correctly present as `h6`.
