# Q846 (dm2): nonvanishing of the even cofactor on the `Ψ₃ = 0` stratum

## Bottom line

Do **not** try to prove this from the four-neighbor relation

```text
δ · α = γ · β.
```

For Mathlib’s auxiliary sequence `preΨ`, that relation is not valid without parity / `Ψ₂Sq` factors.  The clean way is to specialize the whole evaluated `preΨ` sequence at a root of `Ψ₃`.

Let

```text
B := Ψ₂Sq(x)^2.
```

At a root of `Ψ₃`, using

```text
preΨ₄(x) = -Ψ₂Sq(x)^2 = -B,
```

the evaluated auxiliary EDS has initial values

```text
u₀ = 0,
u₁ = 1,
u₂ = 1,
u₃ = 0,
u₄ = -B.
```

The resulting specialized sequence is six-periodic up to powers of `B`:

```text
u_{6t}     = 0
u_{6t+1}   =  B^(3t² + t)
u_{6t+2}   =  B^(3t² + 2t)
u_{6t+3}   = 0
u_{6t+4}   = -B^(3t² + 4t + 1)
u_{6t+5}   = -B^(3t² + 5t + 2).
```

Then, since `3 ∣ m + 3`, there are only two cases.

If

```text
m = 6t,
```

then

```text
α = preΨ(m+1)(x) =  B^(3t² + t)
β = preΨ(m+2)(x) =  B^(3t² + 2t)
γ = preΨ(m+4)(x) = -B^(3t² + 4t + 1)
δ = preΨ(m+5)(x) = -B^(3t² + 5t + 2),
```

so

```text
β²δ - αγ² = -2 · B^(9t² + 9t + 2).
```

If

```text
m = 6t + 3,
```

then

```text
α = preΨ(m+1)(x) = -B^(3t² + 4t + 1)
β = preΨ(m+2)(x) = -B^(3t² + 5t + 2)
γ = preΨ(m+4)(x) =  B^(3t² + 7t + 4)
δ = preΨ(m+5)(x) =  B^(3t² + 8t + 5),
```

so

```text
β²δ - αγ² = 2 · B^(9t² + 18t + 9).
```

Thus the cofactor is nonzero as soon as

```text
2 ≠ 0
B ≠ 0.
```

The hypothesis `(2 * (m + 3) : K) ≠ 0` gives `2 ≠ 0`.  The fact `B ≠ 0` follows from adjacent nonvanishing of `preΨ₃` and `preΨ₄`: if `B = 0`, then `preΨ₄(x) = -B = 0`, contradicting `preΨ₃(x) = Ψ₃(x) = 0` and adjacent coprimality.

That proves the desired nonvanishing.

---

## The important correction

The tempting relation

```text
preΨ(r+2)(x) · preΨ(r-2)(x)
  = preΨ(r+1)(x) · preΨ(r-1)(x)
```

at `preΨ(r)(x) = 0` is **not** a valid relation for Mathlib’s auxiliary `preΨ` sequence.

You can see the failure already at the specialized initial values.  Put `r = 3`.  Then

```text
u₁ = 1,
u₂ = 1,
u₄ = -B,
u₅ = -B².
```

The claimed relation would say

```text
u₅ · u₁ = u₄ · u₂,
```

that is

```text
-B² = -B,
```

which is false for general `B`.

The missing issue is that `preΨ` is not the actual normalized EDS; it is Mathlib’s auxiliary sequence with the even `ψ₂` factors stripped off.  The Ward/Somos relations for the actual normalized EDS acquire parity factors when translated to `preΨ`.  So this branch should not be attacked through the naive four-neighbor Somos relation.

---

## First useful polynomial identity

The identity behind the assumption

```text
preΨ₄(x) = -Ψ₂Sq(x)^2
```

is the polynomial identity

```text
preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄) · Ψ₃.
```

In Lean, prove it as a lemma by unfolding the `bᵢ` definitions:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

lemma preΨ₄_add_Ψ₂Sq_sq :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃]
  rw [b₂, b₄, b₆, b₈]
  ring_nf

lemma preΨ₄_eval_eq_neg_Ψ₂Sq_sq_of_Ψ₃_eval_eq_zero
    {x : K} (h3 : W.Ψ₃.eval x = 0) :
    W.preΨ₄.eval x = - (W.Ψ₂Sq.eval x) ^ 2 := by
  have h := congrArg (fun p : K[X] => p.eval x) (W.preΨ₄_add_Ψ₂Sq_sq)
  simp [eval_add, eval_mul, eval_pow, h3] at h
  -- h : W.preΨ₄.eval x + (W.Ψ₂Sq.eval x)^2 = 0
  linarith

end WeierstrassCurve
```

If `linarith` dislikes the final ring expression, use:

```lean
  linear_combination h
```

or simply

```lean
  rw [eq_neg_iff_add_eq_zero]
  exact h
```

depending on the exact shape after `simp`.

---

## The specialized EDS block lemma

Define, after evaluation at `x`,

```lean
u j := (W.preΨ' j).eval x
B   := (W.Ψ₂Sq.eval x) ^ 2
```

Under

```lean
h3 : W.Ψ₃.eval x = 0
h4 : W.preΨ₄.eval x = -B
```

Mathlib’s recurrence for `preΨ'` specializes to the sequence with initial values

```text
0, 1, 1, 0, -B.
```

The useful lemma is:

```lean
lemma preΨ'_eval_six_block_of_Ψ₃_eval_eq_zero
    {x : K} (h3 : W.Ψ₃.eval x = 0)
    (h4 : W.preΨ₄.eval x = - (W.Ψ₂Sq.eval x) ^ 2) (t : ℕ) :
    let B : K := (W.Ψ₂Sq.eval x) ^ 2
    (W.preΨ' (6 * t)).eval x = 0 ∧
    (W.preΨ' (6 * t + 1)).eval x = B ^ (3 * t ^ 2 + t) ∧
    (W.preΨ' (6 * t + 2)).eval x = B ^ (3 * t ^ 2 + 2 * t) ∧
    (W.preΨ' (6 * t + 3)).eval x = 0 ∧
    (W.preΨ' (6 * t + 4)).eval x = -B ^ (3 * t ^ 2 + 4 * t + 1) ∧
    (W.preΨ' (6 * t + 5)).eval x = -B ^ (3 * t ^ 2 + 5 * t + 2) := by
  -- Prove by strong induction using `preΨ'_even` and `preΨ'_odd`,
  -- or prove the corresponding scalar lemma for `preNormEDS' B 0 (-B)`.
  sorry
```

For maintainability, I recommend proving the scalar version first:

```lean
lemma preNormEDS'_zero_neg_six_block (B : K) (t : ℕ) :
    preNormEDS' B 0 (-B) (6 * t) = 0 ∧
    preNormEDS' B 0 (-B) (6 * t + 1) = B ^ (3 * t ^ 2 + t) ∧
    preNormEDS' B 0 (-B) (6 * t + 2) = B ^ (3 * t ^ 2 + 2 * t) ∧
    preNormEDS' B 0 (-B) (6 * t + 3) = 0 ∧
    preNormEDS' B 0 (-B) (6 * t + 4) = -B ^ (3 * t ^ 2 + 4 * t + 1) ∧
    preNormEDS' B 0 (-B) (6 * t + 5) = -B ^ (3 * t ^ 2 + 5 * t + 2) := by
  sorry
```

Then either prove an evaluation-commutation lemma for `preNormEDS'`, or just use the same proof pattern directly on the evaluated `preΨ'` recurrences.

The recurrences you need after evaluating are exactly:

```lean
have h_even (r : ℕ) :
    u (2 * (r + 3)) =
      u (r + 2) ^ 2 * u (r + 3) * u (r + 5)
        - u (r + 1) * u (r + 3) * u (r + 4) ^ 2 := by
  simpa [u, eval_mul, eval_sub, eval_pow]
    using congrArg (fun p : K[X] => p.eval x) (W.preΨ'_even r)

have h_odd (r : ℕ) :
    u (2 * (r + 2) + 1) =
      u (r + 4) * u (r + 2) ^ 3 * (if Even r then B else 1)
        - u (r + 1) * u (r + 3) ^ 3 * (if Even r then 1 else B) := by
  simpa [u, B, eval_mul, eval_sub, eval_pow]
    using congrArg (fun p : K[X] => p.eval x) (W.preΨ'_odd r)
```

The proof of the six-block lemma is just these recurrences plus `omega` for index arithmetic and `ring_nf` for the exponent arithmetic.

---

## Cofactor calculation

Let

```lean
C_m :=
  (W.preΨ' (m + 2)).eval x ^ 2 * (W.preΨ' (m + 5)).eval x
    - (W.preΨ' (m + 1)).eval x * (W.preΨ' (m + 4)).eval x ^ 2
```

Assume

```lean
hdiv : 3 ∣ m + 3.
```

Since `m + 3 ≥ 3`, write either

```text
m = 6t
```

or

```text
m = 6t + 3.
```

The six-block lemma gives the following two concrete calculations.

### Case 1: `m = 6t`

```lean
have hC : C_m = -2 * B ^ (9 * t ^ 2 + 9 * t + 2) := by
  subst m
  simp [C_m, preΨ'_eval_six_block_of_Ψ₃_eval_eq_zero, B]
  ring_nf
```

Mathematically, this is:

```text
β²δ - αγ²
  = (B^(3t²+2t))² · (-B^(3t²+5t+2))
      - B^(3t²+t) · (-B^(3t²+4t+1))²
  = -B^(9t²+9t+2) - B^(9t²+9t+2)
  = -2B^(9t²+9t+2).
```

### Case 2: `m = 6t + 3`

```lean
have hC : C_m = 2 * B ^ (9 * t ^ 2 + 18 * t + 9) := by
  subst m
  simp [C_m, preΨ'_eval_six_block_of_Ψ₃_eval_eq_zero, B]
  ring_nf
```

Mathematically:

```text
β²δ - αγ²
  = (-B^(3t²+5t+2))² · B^(3t²+8t+5)
      - (-B^(3t²+4t+1)) · (B^(3t²+7t+4))²
  = B^(9t²+18t+9) + B^(9t²+18t+9)
  = 2B^(9t²+18t+9).
```

The cancellation danger disappears because the two terms have **opposite signs**.  This is the piece that the naive `δα = γβ` manipulation misses.

---

## Nonzero inputs

You need two nonzero facts.

### 1. `2 ≠ 0`

From the final separability hypothesis

```lean
hn : ((2 * (m + 3) : ℕ) : K) ≠ 0
```

get:

```lean
have h2 : (2 : K) ≠ 0 := by
  intro h2zero
  apply hn
  simp [Nat.cast_mul, h2zero]
```

In a field, this also gives `(4 : K) ≠ 0` if you need adjacent coprimality:

```lean
have h4K : (4 : K) ≠ 0 := by
  norm_num [show (4 : K) = (2 : K) * (2 : K) by norm_num]
  exact mul_ne_zero h2 h2
```

If the displayed `norm_num` proof does not work verbatim, use:

```lean
have hfour : (4 : K) = (2 : K) * (2 : K) := by norm_num
rw [hfour]
exact mul_ne_zero h2 h2
```

### 2. `B ≠ 0`

Use adjacent nonvanishing between `preΨ₃` and `preΨ₄`.

```lean
have hpre4_ne : (W.preΨ₄.eval x) ≠ 0 := by
  have hadj := preΨ'_adjacent_ne_zero_of_preΨ'_zero
    (W := W) (x := x) h4K (n := 3) (by norm_num) (by simpa using h3)
  -- hadj.2 is nonvanishing of `preΨ' 4`.
  simpa [preΨ'_four] using hadj.2
```

Then:

```lean
let B : K := (W.Ψ₂Sq.eval x) ^ 2
have hB : B ≠ 0 := by
  intro hBzero
  apply hpre4_ne
  have hpre4 : W.preΨ₄.eval x = -B := by
    dsimp [B]
    exact W.preΨ₄_eval_eq_neg_Ψ₂Sq_sq_of_Ψ₃_eval_eq_zero h3
  rw [hpre4, hBzero, neg_zero]
```

Alternatively, if you already have a theorem that roots of `Ψ₃` are not roots of `Ψ₂Sq` under `[W.IsElliptic]` and `(6 : K) ≠ 0`, use that directly.

---

## Final theorem shape

A good local theorem is:

```lean
theorem evenCofactor_eval_ne_zero_of_middle_zero_of_Ψ₃_zero
    [W.IsElliptic] {m : ℕ} {x : K}
    (hn : ((2 * (m + 3) : ℕ) : K) ≠ 0)
    (hdiv : 3 ∣ m + 3)
    (h3 : W.Ψ₃.eval x = 0) :
    ( (W.preΨ' (m + 2)).eval x ^ 2 * (W.preΨ' (m + 5)).eval x
        - (W.preΨ' (m + 1)).eval x * (W.preΨ' (m + 4)).eval x ^ 2 ) ≠ 0 := by
  let B : K := (W.Ψ₂Sq.eval x) ^ 2

  have hpre4 : W.preΨ₄.eval x = -B := by
    dsimp [B]
    exact W.preΨ₄_eval_eq_neg_Ψ₂Sq_sq_of_Ψ₃_eval_eq_zero h3

  have h2 : (2 : K) ≠ 0 := by
    intro h2zero
    apply hn
    simp [Nat.cast_mul, h2zero]

  have h4K : (4 : K) ≠ 0 := by
    have hfour : (4 : K) = (2 : K) * (2 : K) := by norm_num
    rw [hfour]
    exact mul_ne_zero h2 h2

  have hpre4_ne : W.preΨ₄.eval x ≠ 0 := by
    have hadj := preΨ'_adjacent_ne_zero_of_preΨ'_zero
      (W := W) (x := x) h4K (n := 3) (by norm_num) (by simpa using h3)
    simpa [preΨ'_four] using hadj.2

  have hB : B ≠ 0 := by
    intro hBzero
    exact hpre4_ne (by simpa [hpre4, hBzero])

  rcases hdiv with ⟨s, hs⟩
  have hspos : 0 < s := by omega

  -- Split `s` by parity.  Since `m + 3 = 3s`, odd `s` gives `m = 6t`,
  -- and positive even `s` gives `m = 6t + 3`.
  rcases Nat.even_or_odd s with hs_even | hs_odd
  · rcases hs_even with ⟨r, rfl⟩
    cases r with
    | zero => omega
    | succ t =>
        have hm : m = 6 * t + 3 := by omega
        subst m
        have hC :
            (W.preΨ' (6 * t + 3 + 2)).eval x ^ 2
                * (W.preΨ' (6 * t + 3 + 5)).eval x
              - (W.preΨ' (6 * t + 3 + 1)).eval x
                * (W.preΨ' (6 * t + 3 + 4)).eval x ^ 2
              = 2 * B ^ (9 * t ^ 2 + 18 * t + 9) := by
          -- Use the six-block lemma and `ring_nf`.
          sorry
        rw [hC]
        exact mul_ne_zero h2 (pow_ne_zero _ hB)
  · rcases hs_odd with ⟨t, rfl⟩
    have hm : m = 6 * t := by omega
    subst m
    have hC :
        (W.preΨ' (6 * t + 2)).eval x ^ 2
            * (W.preΨ' (6 * t + 5)).eval x
          - (W.preΨ' (6 * t + 1)).eval x
            * (W.preΨ' (6 * t + 4)).eval x ^ 2
          = -2 * B ^ (9 * t ^ 2 + 9 * t + 2) := by
      -- Use the six-block lemma and `ring_nf`.
      sorry
    rw [hC]
    exact neg_ne_zero.mpr (mul_ne_zero h2 (pow_ne_zero _ hB))
```

The two remaining `sorry`s are not conceptual; they are the mechanical substitutions from the six-block lemma.

---

## If the local code uses integer-indexed `preΨ`

Do the proof Nat-indexed first.  Then transport by `simp`:

```lean
@[simp]
lemma WeierstrassCurve.preΨ_ofNat (n : ℕ) :
    W.preΨ n = W.preΨ' n
```

So a term like

```lean
(W.preΨ ((m + 2 : ℕ) : ℤ)).eval x
```

should reduce to

```lean
(W.preΨ' (m + 2)).eval x
```

by `simpa`.

Avoid doing the six-block arithmetic over arbitrary `ℤ` indices unless downstream code truly requires it.  The cofactor in this branch has Nat indices, and the Nat block lemma is much easier.

---

## Final recommendation

Replace the attempted Somos manipulation by the specialized six-block lemma.  The proof becomes:

1. prove `preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄)Ψ₃`,
2. set `B = Ψ₂Sq(x)^2`, so at `Ψ₃(x)=0` the evaluated sequence has data `0,1,1,0,-B`,
3. prove the six-block formulas for `preΨ'` values,
4. split `3 ∣ m + 3` into `m = 6t` or `m = 6t + 3`,
5. compute the cofactor as `-2B^N` or `2B^N`, and
6. use `(2 * (m + 3) : K) ≠ 0` plus adjacent nonvanishing to get `2 ≠ 0` and `B ≠ 0`.

This bypasses the false four-neighbor relation and gives exactly the nonvanishing needed for the even cofactor branch.
