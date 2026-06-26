# Q796 (dm2): characteristic 2 separability without `Ωₙ`

## Bottom line

The literal proof strategy “EDS recurrence + adjacent coprimality only” is not enough by itself.  Adjacent coprimality is a zero-set statement: it tells you that a root of `ψₙ` is not also a root of the neighboring division polynomials.  Separability is a first-order statement: it says that a root of `ψₙ` is not a double root, equivalently that `ψₙ'` does not vanish there.  Some first-order input is unavoidable.

However, there is a good characteristic-2-friendly replacement for the `Ωₙ` argument.  Do **not** try to define `Ωₙ` in characteristic `2`.  Instead, prove and use the Ω-free squared differential congruence

```text
Ψ₂Sq · (preΨₙ')² ≡ n² · Φₙ        mod preΨₙ          (n odd).
```

In Mathlib-style notation, for odd `n : ℕ`, the target should be something like

```lean
(W.preΨ' n) ∣
  W.Ψ₂Sq * (Polynomial.derivative (W.preΨ' n)) ^ 2
    - C ((n : K) ^ 2) * W.Φ (n : ℤ)
```

or equivalently as a `Polynomial.ModEq` statement.  This identity uses only objects that Mathlib already has: `preΨ'`, `Ψ₂Sq`, `Φ`, and `derivative`.  It contains no division by `2` and no `Ωₙ`.

This congruence is essentially the square of the local-parameter identity

```text
v · Φₙ · ψₙ' + n · Ωₙ ≡ 0        mod ψₙ,
```

together with the curve-equation consequence

```text
Ωₙ² ≡ Φₙ³                         mod ψₙ.
```

But the important point for formalization is that the squared congruence can be stated without ever defining `Ωₙ`.

---

## Why this avoids the characteristic-2 problem

The x-coordinate Wronskian loses information in characteristic `2` because the denominator is `ψₙ²`; differentiating `ψₙ²` produces a factor `2`, which vanishes.  The local parameter `t = -x/y` does not have this problem: the formal-group identity is

```text
[n]^* t = n · t + higher order terms.
```

So when `(n : K) ≠ 0`, the pullback of the local parameter still has order one.  Squaring the resulting first-order identity gives the univariate congruence above.  The factor `2` never appears.

Geometrically, at an affine `n`-torsion point `P`, with `n` prime to the characteristic, `[n]^*t` is a uniformizer at `P`.  Since `x` has a double pole at `O`, `x ∘ [n]` has pole order `2` at `P`.  But

```text
x([n]Q) = Φₙ(Q) / ψₙ(Q)².
```

If `Φₙ(P)` is a unit, then `ψₙ` has order exactly `1` at `P`.  This proves separability and uses only the x-coordinate numerator `Φₙ`, not the y-coordinate numerator `Ωₙ`.

The squared congruence is the polynomial version of that order calculation.

---

## Characteristic `2` branch

Assume

```lean
h2 : (2 : K) = 0
hn : (n : K) ≠ 0
```

with `K` a field.  Then `n` is odd.  In Lean this should be a small lemma:

```lean
have hnodd : Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro hneven
  rcases hneven with ⟨m, rfl⟩
  -- now `(2 * m : K) = 0`, contradicting `hn`
  simpa [Nat.cast_mul, h2] using hn
```

For odd `n`, the actual bivariate division polynomial is just the univariate polynomial:

```text
Ψₙ = preΨₙ.
```

So the relevant separability statement is about `W.preΨ' n`.

Let `x` be a root:

```lean
hroot : (W.preΨ' n).eval x = 0
```

To prove separability, it is enough to show

```lean
(Polynomial.derivative (W.preΨ' n)).eval x ≠ 0
```

Suppose, for contradiction, that the derivative vanishes.  Evaluating the squared congruence at `x` gives

```text
Ψ₂Sq(x) · ψₙ'(x)² = n² · Φₙ(x).
```

If `ψₙ'(x) = 0`, then

```text
n² · Φₙ(x) = 0.
```

Since `(n : K) ≠ 0`, also `(n : K)² ≠ 0`, hence

```text
Φₙ(x) = 0.
```

But for odd `n`, Mathlib’s definition of `Φ` gives

```text
Φₙ = X · preΨₙ² - preΨₙ₊₁ · preΨₙ₋₁ · Ψ₂Sq.
```

At a root of `preΨₙ`, this reduces to

```text
Φₙ(x) = - preΨₙ₊₁(x) · preΨₙ₋₁(x) · Ψ₂Sq(x).
```

Thus `Φₙ(x) ≠ 0` follows from three nonvanishing facts:

```text
preΨₙ₊₁(x) ≠ 0,
preΨₙ₋₁(x) ≠ 0,
Ψ₂Sq(x) ≠ 0.
```

This contradicts `Φₙ(x) = 0`, so `ψₙ'(x) ≠ 0`.

That is the complete characteristic-2 separability argument.

---

## What coprimality input is actually needed

You need slightly more than the old adjacent `preΨ` statement.

For a root of odd `preΨₙ`, the formula for `Φₙ(x)` contains the extra factor `Ψ₂Sq(x)`.  Therefore the characteristic-2 proof needs either:

1. point-level adjacent nonvanishing for the **actual** division polynomials `Ψₙ`, or
2. a univariate package consisting of adjacent nonvanishing for `preΨ` plus a separate proof that `Ψ₂Sq(x) ≠ 0`.

The second option is usually easier to integrate into the existing `preΨ` work.

A useful local replacement for the old characteristic restriction is:

```lean
public theorem no_adjacent_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
    [W.IsElliptic] {x : K} (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) (m : ℤ) :
    ¬ ((W.preΨ m).eval x = 0 ∧ (W.preΨ (m + 1)).eval x = 0) := by
  -- Same EDS proof as `no_adjacent_preΨ_zero`, but after evaluating at `x`.
  -- The recurrence parameter is `W.Ψ₂Sq.eval x`, and the proof needs this
  -- evaluated parameter to be nonzero, not the global hypothesis `(4 : K) ≠ 0`.
  sorry
```

Then the adjacent-root lemma is unchanged:

```lean
public theorem preΨ_adjacent_ne_zero_of_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
    [W.IsElliptic] {x : K} (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) {m : ℤ}
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

So the remaining non-adjacent input is:

```lean
public theorem Ψ₂Sq_eval_ne_zero_of_preΨ'_odd_root_char_two
    [W.IsElliptic] (h2 : (2 : K) = 0) {n : ℕ}
    (hnodd : Odd n) (hn : (n : K) ≠ 0) {x : K}
    (hroot : (W.preΨ' n).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  sorry
```

There are two ways to prove this theorem.

### Option A: point-level proof

Over an algebraic closure, choose `y` with `(x, y)` on the curve.  Since `n` is odd and `preΨₙ(x) = 0`, the point is `n`-torsion.  If `Ψ₂Sq(x) = 0`, then `ψ₂(x,y) = 0`, so the point is also `2`-torsion.  Because `gcd n 2 = 1`, the point would be `O`, impossible for an affine point.  Hence `Ψ₂Sq(x) ≠ 0`.

This is conceptually clean, but it needs whatever point/multiplication API the project has available.

### Option B: univariate EDS proof in characteristic `2`

Work modulo `Ψ₂Sq`.  In characteristic `2`, the EDS parameter for `preΨ` is `Ψ₂Sq²`, so modulo `Ψ₂Sq` the odd recurrence collapses.  One gets the congruence

```text
preΨ'_(2r+1) ≡ Ψ₃^(r(r+1)/2)        mod Ψ₂Sq.
```

Equivalently, for odd `n`,

```text
preΨ'_n ≡ Ψ₃^((n² - 1) / 8)          mod Ψ₂Sq.
```

So it is enough to prove

```lean
IsCoprime W.Ψ₃ W.Ψ₂Sq
```

in characteristic `2`, under `[W.IsElliptic]`.  This is the statement that a smooth curve has no point that is simultaneously `2`-torsion and `3`-torsion.  Algebraically, it is a finite calculation from the discriminant/nonsingularity hypothesis.

Then `preΨ'_n` is coprime to `Ψ₂Sq`, so a root of `preΨ'_n` cannot be a root of `Ψ₂Sq`.

This option is probably the most compatible with an EDS-only development.

---

## The recommended theorem stack

I would structure the implementation like this.

### 1. Characteristic-2 parity lemma

```lean
theorem odd_of_char_two_natCast_ne_zero
    [Field K] (h2 : (2 : K) = 0) {n : ℕ} (hn : (n : K) ≠ 0) :
    Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro hneven
  rcases hneven with ⟨m, rfl⟩
  exact hn (by simp [Nat.cast_mul, h2])
```

The exact `simp` line may need minor adjustment, but the proof is just `n = 2*m` implies `(n : K) = 0`.

### 2. Ω-free squared differential congruence

```lean
theorem preΨ'_odd_derivative_sq_mod
    [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hnodd : Odd n) :
    (W.preΨ' n) ∣
      W.Ψ₂Sq * (Polynomial.derivative (W.preΨ' n)) ^ 2
        - C ((n : K) ^ 2) * W.Φ (n : ℤ) := by
  -- Best proof: local parameter / invariant differential.
  -- Alternative proof: EDS induction, but it will be a differentiated EDS identity,
  -- not a consequence of adjacent coprimality alone.
  sorry
```

This is the key replacement for `Ωₙ`.

### 3. Non-2-torsion at roots of odd `preΨₙ`

```lean
theorem Ψ₂Sq_eval_ne_zero_of_preΨ'_odd_root_char_two
    [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) = 0) {n : ℕ}
    (hnodd : Odd n) (hn : (n : K) ≠ 0) {x : K}
    (hroot : (W.preΨ' n).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  -- Either point-level torsion proof, or the modulo-Ψ₂Sq EDS proof.
  sorry
```

### 4. Adjacent nonvanishing with local `Ψ₂Sq` hypothesis

```lean
theorem preΨ_int_adjacent_ne_zero_of_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
    [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {x : K} (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) {m : ℤ}
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

Use integer indices internally to avoid `Nat` subtraction issues.

### 5. Characteristic-2 derivative nonvanishing

```lean
theorem preΨ'_derivative_eval_ne_zero_of_root_char_two
    [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) = 0) {n : ℕ} (hn : (n : K) ≠ 0)
    {x : K} (hroot : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  have hnodd : Odd n := odd_of_char_two_natCast_ne_zero (K := K) h2 hn

  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 :=
    Ψ₂Sq_eval_ne_zero_of_preΨ'_odd_root_char_two
      (W := W) h2 hnodd hn hroot

  have hrootZ : (W.preΨ (n : ℤ)).eval x = 0 := by
    simpa using hroot

  have hadj :=
    preΨ_int_adjacent_ne_zero_of_preΨ_zero_of_Ψ₂Sq_eval_ne_zero
      (W := W) (x := x) hΨ₂ hrootZ

  have hΦ_ne : (W.Φ (n : ℤ)).eval x ≠ 0 := by
    -- Expand `Φ` for odd `n`:
    --   Φₙ(x) = - preΨₙ₊₁(x) * preΨₙ₋₁(x) * Ψ₂Sq(x)
    -- because `preΨₙ(x) = 0`.
    -- Then use `hadj.1`, `hadj.2`, and `hΨ₂`.
    sorry

  intro hderiv

  have hmod := preΨ'_odd_derivative_sq_mod (W := W) hnodd

  have hΦ_zero : (W.Φ (n : ℤ)).eval x = 0 := by
    -- Evaluate `hmod` at `x`.
    -- The modulus term vanishes by `hroot`.
    -- The left side vanishes by `hderiv`.
    -- Since `(n : K)^2 ≠ 0`, conclude `Φₙ(x) = 0`.
    sorry

  exact hΦ_ne hΦ_zero
```

This is the separability core for characteristic `2`.

---

## Ordinary versus supersingular

You do not need to split the characteristic-2 proof into ordinary and supersingular cases.

In characteristic `2`,

```text
v = 2y + a₁x + a₃ = a₁x + a₃.
```

If the curve is supersingular, then `a₁ = 0`, and nonsingularity forces `a₃ ≠ 0`; hence `v = a₃` is automatically nonzero.  If the curve is ordinary, then `v = 0` is exactly the affine `2`-torsion condition.  Since `n` is odd, an `n`-torsion point cannot also be nontrivial `2`-torsion.  Thus `v ≠ 0`, equivalently `Ψ₂Sq(x) ≠ 0`, in both cases.

So the uniform proof should be phrased as “odd `n`-division roots are not roots of `Ψ₂Sq`,” not as a case split on `a₁`.

---

## Answer to the proposed alternative

There is no proof from adjacent coprimality alone.  Adjacent coprimality gives

```text
preΨₙ(x) = 0  ⇒  preΨₙ₋₁(x) ≠ 0 and preΨₙ₊₁(x) ≠ 0,
```

but it says nothing about whether `preΨₙ` has a double zero at `x`.  To rule out a double zero you need first-order information.  In characteristic `2`, the right first-order information is not the x-coordinate Wronskian and not `Ωₙ`; it is the local-parameter/invariant-differential identity, packaged as the squared univariate congruence

```text
Ψ₂Sq · (preΨₙ')² ≡ n² · Φₙ        mod preΨₙ.
```

Once that congruence is available, the rest of the proof is exactly EDS-style: use the oddness of `n`, nonvanishing of `Ψ₂Sq` at odd `n`-division roots, and adjacent coprimality to show `Φₙ(x) ≠ 0`.  Then the congruence forces `preΨₙ'(x) ≠ 0`.

That is the cleanest Ω-free characteristic-2 path.
