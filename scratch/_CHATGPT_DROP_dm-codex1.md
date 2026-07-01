# Q3001 (dm-codex1): inverse algebra for C10 Tate row

The target is **true** under exactly the stated hypotheses

```lean
hc  : c ≠ 0
hbc : b - c ≠ 0
hK  : tateC10_K b c = 0
```

No extra exclusion is needed.  The denominator nonzero conclusion follows from the equation and these hypotheses.

The current sign/table row is internally consistent:

```lean
def tateC10_den (t : ℚ) : ℚ :=
  t ^ 2 - 3 * t + 1

def tateC10_b (t : ℚ) : ℚ :=
  t ^ 3 * (t - 1) * (2 * t - 1) / (tateC10_den t) ^ 2

def tateC10_c (t : ℚ) : ℚ :=
  -t * (t - 1) * (2 * t - 1) / tateC10_den t

def tateC10_tInv (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)
```

The key algebra is this.  Put

```lean
d = b - c
T = c^2 / d
```

Then `tateC10_K b c = 0` is equivalent, after multiplying by `T^3/c^5`, to

```lean
c * (T^2 - 3*T + 1) + T*(T-1)*(2*T-1) = 0.
```

So if `den(T)=0`, then `T*(T-1)*(2*T-1)=0`; but `T≠0`, and `T=1` or `T=1/2` contradicts `den(T)=0`.  Thus `den(T)≠0`, and the displayed equation solves immediately for

```lean
c = -T*(T-1)*(2*T-1)/den(T).
```

Finally `T = c^2/(b-c)` gives `b-c = c^2/T`, hence

```lean
b = c + c^2/T = T^3*(T-1)*(2*T-1)/den(T)^2.
```

## Pasteable Lean proof split into private lemmas

This is designed for your namespace `MazurProof.KubertBridgeN10` and the definitions in the prompt.

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN10
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN10

noncomputable section

private lemma tateC10_tInv_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0) :
    tateC10_tInv b c ≠ 0 := by
  dsimp [tateC10_tInv]
  exact div_ne_zero (pow_ne_zero 2 hc) hbc

/-- The linear-in-`c` equation obtained from `K=0` after setting `t=c^2/(b-c)`. -/
private lemma tateC10_linear_of_K
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    c * tateC10_den (tateC10_tInv b c) +
        tateC10_tInv b c * (tateC10_tInv b c - 1) *
          (2 * tateC10_tInv b c - 1) = 0 := by
  have hbc2 : (b - c) ^ 2 ≠ 0 := pow_ne_zero 2 hbc
  have hbc3 : (b - c) ^ 3 ≠ 0 := pow_ne_zero 3 hbc
  dsimp [tateC10_tInv, tateC10_den]
  dsimp [tateC10_K] at hK
  field_simp [hbc, hbc2, hbc3]
  ring_nf at hK ⊢
  nlinarith [hK]

private lemma tateC10_den_tInv_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    tateC10_den (tateC10_tInv b c) ≠ 0 := by
  let t : ℚ := tateC10_tInv b c
  have ht_ne : t ≠ 0 := by
    simpa [t] using tateC10_tInv_ne_zero (b := b) (c := c) hc hbc
  have hlin : c * tateC10_den t + t * (t - 1) * (2 * t - 1) = 0 := by
    simpa [t] using tateC10_linear_of_K (b := b) (c := c) hc hbc hK
  change tateC10_den t ≠ 0
  intro hden
  have hprod : t * (t - 1) * (2 * t - 1) = 0 := by
    nlinarith [hlin, hden]
  rcases mul_eq_zero.mp hprod with hleft | hright
  · rcases mul_eq_zero.mp hleft with ht0 | ht1m
    · exact ht_ne ht0
    · have ht1 : t = 1 := by linarith
      rw [ht1] at hden
      norm_num [tateC10_den] at hden
  · have ht_half : t = (1 : ℚ) / 2 := by linarith
    rw [ht_half] at hden
    norm_num [tateC10_den] at hden

private lemma tateC10_c_tInv_eq_of_K
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    c = tateC10_c (tateC10_tInv b c) := by
  let t : ℚ := tateC10_tInv b c
  have hden : tateC10_den t ≠ 0 := by
    simpa [t] using tateC10_den_tInv_ne_zero (b := b) (c := c) hc hbc hK
  have hlin : c * tateC10_den t + t * (t - 1) * (2 * t - 1) = 0 := by
    simpa [t] using tateC10_linear_of_K (b := b) (c := c) hc hbc hK
  change c = tateC10_c t
  dsimp [tateC10_c]
  field_simp [hden]
  ring_nf at hlin ⊢
  nlinarith [hlin]

private lemma tateC10_b_tInv_eq_of_K
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    b = tateC10_b (tateC10_tInv b c) := by
  let t : ℚ := tateC10_tInv b c
  have ht_ne : t ≠ 0 := by
    simpa [t] using tateC10_tInv_ne_zero (b := b) (c := c) hc hbc
  have hden : tateC10_den t ≠ 0 := by
    simpa [t] using tateC10_den_tInv_ne_zero (b := b) (c := c) hc hbc hK
  have hc_param : c = tateC10_c t := by
    simpa [t] using tateC10_c_tInv_eq_of_K (b := b) (c := c) hc hbc hK
  have hb_sub : b - c = c ^ 2 / t := by
    dsimp [t, tateC10_tInv]
    field_simp [hc, hbc]
  have hb_expr : b = c + c ^ 2 / t := by
    linarith
  calc
    b = c + c ^ 2 / t := hb_expr
    _ = tateC10_c t + (tateC10_c t) ^ 2 / t := by rw [hc_param]
    _ = tateC10_b t := by
      dsimp [tateC10_b, tateC10_c]
      field_simp [hden, ht_ne]
      ring

/-- Inverse algebra for the C10 Tate row. -/
theorem tateC10_param_of_K
    {b c : ℚ}
    (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    let t := tateC10_tInv b c
    tateC10_den t ≠ 0 ∧
      b = tateC10_b t ∧ c = tateC10_c t := by
  change
    tateC10_den (tateC10_tInv b c) ≠ 0 ∧
      b = tateC10_b (tateC10_tInv b c) ∧
      c = tateC10_c (tateC10_tInv b c)
  exact ⟨
    tateC10_den_tInv_ne_zero (b := b) (c := c) hc hbc hK,
    tateC10_b_tInv_eq_of_K (b := b) (c := c) hc hbc hK,
    tateC10_c_tInv_eq_of_K (b := b) (c := c) hc hbc hK⟩

end

end MazurProof.KubertBridgeN10
```

## If `field_simp` in `tateC10_linear_of_K` leaves inverse powers

Use this more explicit version of that lemma.  It sets `d=b-c` and proves the cleared identity by multiplying the target by `d^3`.

```lean
private lemma tateC10_linear_of_K_alt
    {b c : ℚ} (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    c * tateC10_den (tateC10_tInv b c) +
        tateC10_tInv b c * (tateC10_tInv b c - 1) *
          (2 * tateC10_tInv b c - 1) = 0 := by
  let d : ℚ := b - c
  have hd : d ≠ 0 := by simpa [d] using hbc
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hd3 : d ^ 3 ≠ 0 := pow_ne_zero 3 hd
  have hK' : -d ^ 3 + (3 * c ^ 2 - c) * d ^ 2 +
      (3 * c ^ 3 - c ^ 4) * d - 2 * c ^ 5 = 0 := by
    simpa [d, tateC10_K] using hK
  have hcleared :
      (c * tateC10_den (c ^ 2 / d) +
          (c ^ 2 / d) * (c ^ 2 / d - 1) * (2 * (c ^ 2 / d) - 1)) * d ^ 3 = 0 := by
    field_simp [hd, hd2, hd3]
    ring_nf at hK' ⊢
    nlinarith [hK']
  have hmul :
      c * tateC10_den (c ^ 2 / d) +
          (c ^ 2 / d) * (c ^ 2 / d - 1) * (2 * (c ^ 2 / d) - 1) = 0 := by
    exact mul_eq_zero.mp hcleared |>.resolve_right hd3
  simpa [d, tateC10_tInv] using hmul
```

Use either `tateC10_linear_of_K` or this `..._alt`; the rest of the proof is unchanged.

## No counterexample

There is no rational counterexample with `c≠0`, `b-c≠0`, and `K=0`.  The apparent possible exceptional denominator `t^2-3t+1=0` cannot occur in the inverse situation: it would force `t*(t-1)*(2t-1)=0`, while `t=c^2/(b-c)≠0`, and the remaining possibilities `t=1` and `t=1/2` make `t^2-3t+1` equal `-1` and `-1/4`, respectively.
