# Q772 (dm2): using `no_adjacent_preΨ_zero` to get nonzero adjacent `preΨ` values

## Core point

The cleanest proof is to first prove an **integer-indexed** lemma.  This avoids the `ℕ` predecessor issue entirely:

```lean
preΨ (m - 1), preΨ m, preΨ (m + 1)       -- all indexed by ℤ
```

Then specialize to `m = (n : ℤ)`.  The bridge from `preΨ' n` to `preΨ (n : ℤ)` is Mathlib’s simp lemma from `DivisionPolynomial.Basic`:

```lean
@[simp]
lemma WeierstrassCurve.preΨ_ofNat (n : ℕ) :
    W.preΨ n = W.preΨ' n
```

So this usually works:

```lean
have hmid : (W.preΨ (n : ℤ)).eval x = 0 := by
  simpa using hroot
```

For `n + 1`, simp/coercions are easy.  For `n - 1`, if you want a **Nat-indexed** statement about `preΨ' (n - 1)`, you need `0 < n`, because Nat subtraction truncates at zero.  Without `0 < n`, `preΨ' (n - 1)` is not the same as `preΨ ((n : ℤ) - 1)`.

---

## Integer-indexed adjacent nonvanishing lemma

This is the lemma I recommend using internally.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import scratch.KeystoneCoprimality

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K) {x : K}

/--
If `preΨ m` vanishes at `x`, then neither adjacent value can vanish.
This is the direct reusable form of `no_adjacent_preΨ_zero`.
-/
public theorem preΨ_adjacent_ne_zero_of_preΨ_zero
    [W.IsElliptic] (h4 : (4 : K) ≠ 0) {m : ℤ}
    (hm : (W.preΨ m).eval x = 0) :
    (W.preΨ (m - 1)).eval x ≠ 0 ∧
    (W.preΨ (m + 1)).eval x ≠ 0 := by
  constructor
  · intro hprev
    have hno := no_adjacent_preΨ_zero (W := W) (x := x) h4 (m - 1)
    apply hno
    constructor
    · exact hprev
    · -- The second term in the adjacent pair at `m - 1` is `m`.
      simpa using hm
  · intro hnext
    have hno := no_adjacent_preΨ_zero (W := W) (x := x) h4 m
    exact hno ⟨hm, hnext⟩
```

If the named implicit argument `(x := x)` is not accepted because of how your section variables are named, just remove it:

```lean
have hno := no_adjacent_preΨ_zero (W := W) h4 (m - 1)
```

The proof idea is exactly:

```lean
no_adjacent_preΨ_zero h4 (m - 1) :
  ¬(preΨ (m - 1) x = 0 ∧ preΨ ((m - 1) + 1) x = 0)

no_adjacent_preΨ_zero h4 m :
  ¬(preΨ m x = 0 ∧ preΨ (m + 1) x = 0)
```

and `simpa` normalizes `((m - 1) + 1)` to `m`.

---

## Version for a root of `preΨ' n`, returning integer-indexed neighbors

This is the best version when the root hypothesis is Nat-indexed but the adjacent terms are intended as true adjacent division polynomials.

```lean
/--
If `preΨ' n` vanishes, then the integer-adjacent values
`preΨ ((n : ℤ) - 1)` and `preΨ ((n : ℤ) + 1)` do not vanish.
-/
public theorem preΨ_int_adjacent_ne_zero_of_preΨ'_zero
    [W.IsElliptic] (h4 : (4 : K) ≠ 0) {n : ℕ}
    (hroot : (W.preΨ' n).eval x = 0) :
    (W.preΨ ((n : ℤ) - 1)).eval x ≠ 0 ∧
    (W.preΨ ((n : ℤ) + 1)).eval x ≠ 0 := by
  have hmid : (W.preΨ (n : ℤ)).eval x = 0 := by
    simpa using hroot
  exact preΨ_adjacent_ne_zero_of_preΨ_zero
    (W := W) (x := x) h4 hmid
```

This statement is valid even for `n = 0`.  In that case the left neighbor is genuinely `preΨ (-1)`, not `preΨ' 0`.

---

## Nat-indexed version, requiring `0 < n`

If downstream code wants the adjacent values as `preΨ' (n - 1)` and `preΨ' (n + 1)`, use this wrapper.

```lean
/--
Nat-indexed adjacent nonvanishing.  The hypothesis `0 < n` is needed because
`preΨ' (n - 1)` corresponds to `preΨ ((n : ℤ) - 1)` only when Nat subtraction
has not truncated.
-/
public theorem preΨ'_adjacent_ne_zero_of_preΨ'_zero
    [W.IsElliptic] (h4 : (4 : K) ≠ 0) {n : ℕ}
    (hn : 0 < n) (hroot : (W.preΨ' n).eval x = 0) :
    (W.preΨ' (n - 1)).eval x ≠ 0 ∧
    (W.preΨ' (n + 1)).eval x ≠ 0 := by
  have hZ := preΨ_int_adjacent_ne_zero_of_preΨ'_zero
    (W := W) (x := x) h4 hroot
  constructor
  · intro hprev
    apply hZ.1
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      omega
    have hprevZ : (W.preΨ ((n - 1 : ℕ) : ℤ)).eval x = 0 := by
      simpa using hprev
    simpa [hcast] using hprevZ
  · intro hnext
    apply hZ.2
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
      omega
    have hnextZ : (W.preΨ ((n + 1 : ℕ) : ℤ)).eval x = 0 := by
      simpa using hnext
    simpa [hcast] using hnextZ

end WeierstrassCurve
```

If Lean has trouble with `omega` on the first cast, make the positivity explicit:

```lean
have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  omega
```

---

## Variant for `n ≥ 3`

In a separability proof you likely have `3 ≤ n`; then the Nat-indexed wrapper is immediate:

```lean
public theorem preΨ'_adjacent_ne_zero_of_preΨ'_zero_of_three_le
    [W.IsElliptic] (h4 : (4 : K) ≠ 0) {n : ℕ}
    (hn3 : 3 ≤ n) (hroot : (W.preΨ' n).eval x = 0) :
    (W.preΨ' (n - 1)).eval x ≠ 0 ∧
    (W.preΨ' (n + 1)).eval x ≠ 0 := by
  exact preΨ'_adjacent_ne_zero_of_preΨ'_zero
    (W := W) (x := x) h4 (by omega) hroot
```

---

## About the characteristic hypothesis

You are right to be suspicious:

```lean
(n : K) ≠ 0
```

does **not** imply

```lean
(4 : K) ≠ 0
```

even for `n ≥ 3`.  In characteristic `2`, any odd `n` has `(n : K) ≠ 0`, but `(4 : K) = 0`.  For example, `n = 3` in characteristic `2` is the basic counterexample.

So any proof that literally uses

```lean
no_adjacent_preΨ_zero h4
```

must carry an explicit hypothesis

```lean
h4 : (4 : K) ≠ 0
```

or must be inside a branch where `h4` has been proved.

The hypothesis

```lean
hY : W.toAffine.polynomialY.evalEval x y ≠ 0
```

or equivalently

```text
2y + a₁x + a₃ ≠ 0
```

also does **not** imply `(4 : K) ≠ 0`.  It is a condition on the point being non-2-torsion, not a condition on the characteristic of the field.  In characteristic `2`, it becomes

```text
a₁x + a₃ ≠ 0,
```

which can certainly hold.

What `hY` can give you is a **local non-2-torsion condition**, essentially

```lean
W.Ψ₂Sq.eval x ≠ 0
```

because on the curve one has

```text
ψ₂(x,y)^2 = Ψ₂Sq(x).
```

That is useful, but it is not the same as `(4 : K) ≠ 0`.

---

## What to do in the full separability theorem

If the final separability theorem assumes only

```lean
hn : (n : K) ≠ 0
```

then there are two cases.

### Case 1: `(4 : K) ≠ 0`

Use the lemmas above directly:

```lean
by_cases h4 : (4 : K) ≠ 0
· have hadj := preΨ'_adjacent_ne_zero_of_preΨ'_zero
    (W := W) (x := x) h4 hn_pos hroot
  -- hadj.1 : (W.preΨ' (n - 1)).eval x ≠ 0
  -- hadj.2 : (W.preΨ' (n + 1)).eval x ≠ 0
  ...
```

### Case 2: `(4 : K) = 0`

You cannot use the current `no_adjacent_preΨ_zero`.  The assumption `hn : (n : K) ≠ 0` only tells you that the characteristic does not divide `n`; it does not rule out characteristic `2`.

For this branch, the right fix is to strengthen the coprimality/no-adjacent theorem so that it uses the local non-2-torsion hypothesis instead of global `(4 : K) ≠ 0`:

```lean
public theorem no_adjacent_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
    [W.IsElliptic] (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) (m : ℤ) :
    ¬(W.preΨ m |>.eval x = 0 ∧ W.preΨ (m + 1) |>.eval x = 0) := by
  -- Same EDS argument as `no_adjacent_preΨ_zero`, but after evaluating at `x`.
  -- The recurrence parameter is `W.Ψ₂Sq.eval x`, and the proof only needs
  -- this evaluated parameter to be nonzero.
  sorry
```

Then the adjacent proof is literally the same:

```lean
public theorem preΨ_adjacent_ne_zero_of_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
    [W.IsElliptic] (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) {m : ℤ}
    (hm : (W.preΨ m).eval x = 0) :
    (W.preΨ (m - 1)).eval x ≠ 0 ∧
    (W.preΨ (m + 1)).eval x ≠ 0 := by
  constructor
  · intro hprev
    exact (no_adjacent_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
      (W := W) (x := x) hΨ₂ (m - 1)) ⟨hprev, by simpa using hm⟩
  · intro hnext
    exact (no_adjacent_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
      (W := W) (x := x) hΨ₂ m) ⟨hm, hnext⟩
```

And `hY` should feed this stronger theorem via:

```lean
have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := by
  -- Use `W.ψ₂_sq` / `W.C_Ψ₂Sq`, evaluate at `(x,y)`, and use the curve equation.
  -- Conceptually: `ψ₂(x,y)^2 = Ψ₂Sq(x)`, so nonzero `ψ₂(x,y)` implies
  -- nonzero `Ψ₂Sq(x)` in a field.
  sorry
```

This is the branch that will cover characteristic `2` with odd `n`.

---

## Bottom line

For the theorem you can prove **right now** from your existing lemma, use:

```lean
preΨ_int_adjacent_ne_zero_of_preΨ'_zero
```

or, if `0 < n`, the Nat-indexed wrapper:

```lean
preΨ'_adjacent_ne_zero_of_preΨ'_zero
```

But this proof necessarily assumes:

```lean
h4 : (4 : K) ≠ 0
```

It cannot be recovered from `(n : K) ≠ 0`, and it cannot be recovered from `hY`.  For the final separability theorem under only `(n : K) ≠ 0`, you need either a characteristic-2 branch or, better, a strengthened no-adjacent theorem using the evaluated non-2-torsion condition `W.Ψ₂Sq.eval x ≠ 0`.
