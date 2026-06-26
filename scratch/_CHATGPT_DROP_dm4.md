# Q848 (dm4): reducing odd separability to the even case when `char K ≠ 2`

## Answer

Yes.  The odd-via-even reduction is correct whenever `(2 : K) ≠ 0`.

In fact, the algebraic reduction does not use oddness directly.  It only uses:

```text
preΨ'(2n) = preΨ'(n) · cofactor
```

and

```text
(2n : K) ≠ 0.
```

For the intended odd case, `(n : K) ≠ 0` plus `(2 : K) ≠ 0` gives `(2n : K) ≠ 0`.  In characteristic `2`, the reduction fails exactly as you noted, because `(2n : K) = 0` for every `n`.

The key point is that you do **not** need to prove `cofactor(x) ≠ 0` separately.  If `preΨ'(n)` had a double root at `x`, then both `preΨ'(2n)` and its derivative vanish at `x`.  This contradicts the even separability theorem for `2n`.  The nonvanishing of the cofactor is then an automatic consequence of the even theorem, not an input.

## Mathlib factorization to use

At the pinned Mathlib revision, the natural-index recurrence is:

```lean
lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2
```

So the useful centered factorization is:

```text
preΨ'(2*(m+3)) = preΨ'(m+3) ·
  (preΨ'(m+2)^2 * preΨ'(m+5) - preΨ'(m+1) * preΨ'(m+4)^2).
```

For `n ≥ 3`, take `m = n - 3`.

## Lean code

The following code is written so that the already-proved even case is an argument.  Replace `hEvenSep` with the actual theorem in your file, for example something like `preΨ'_deriv_ne_zero_at_root_even`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/--
The cofactor in the centered even recurrence
`preΨ'(2*(m+3)) = preΨ'(m+3) * preΨEvenCofactor m`.
-/
noncomputable def preΨEvenCofactor (m : ℕ) : K[X] :=
  W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
    W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2

/-- The EDS even recurrence, factored by the middle factor. -/
lemma preΨ'_even_factor_center (m : ℕ) :
    W.preΨ' (2 * (m + 3)) = W.preΨ' (m + 3) * W.preΨEvenCofactor m := by
  rw [W.preΨ'_even m]
  unfold preΨEvenCofactor
  ring

/-- If the center factor vanishes, then the doubled-index polynomial vanishes. -/
lemma preΨ'_root_two_mul_of_root_center {m : ℕ} {x : K}
    (hx : (W.preΨ' (m + 3)).IsRoot x) :
    (W.preΨ' (2 * (m + 3))).IsRoot x := by
  rw [W.preΨ'_even_factor_center m]
  change (W.preΨ' (m + 3) * W.preΨEvenCofactor m).eval x = 0
  have hfx : (W.preΨ' (m + 3)).eval x = 0 := by
    simpa [Polynomial.IsRoot] using hx
  simp [hfx]

/-- If the center factor has a double root, then the doubled-index polynomial has a double root. -/
lemma preΨ'_derivative_root_two_mul_of_double_root_center {m : ℕ} {x : K}
    (hx : (W.preΨ' (m + 3)).IsRoot x)
    (hder : (derivative (W.preΨ' (m + 3))).IsRoot x) :
    (derivative (W.preΨ' (2 * (m + 3)))).IsRoot x := by
  rw [W.preΨ'_even_factor_center m]
  change (derivative (W.preΨ' (m + 3) * W.preΨEvenCofactor m)).eval x = 0
  have hfx : (W.preΨ' (m + 3)).eval x = 0 := by
    simpa [Polynomial.IsRoot] using hx
  have hdfx : (derivative (W.preΨ' (m + 3))).eval x = 0 := by
    simpa [Polynomial.IsRoot] using hder
  rw [derivative_mul]
  simp [hfx, hdfx]

/--
Reduction from `n` to the even index `2n`, valid when `(2 : K) ≠ 0`.

The hypothesis `hEvenSep` is the already-proved even-index theorem.  I included
`4 ≤ N` in its signature because most local even theorems are stated only for the
non-small even case.  If your theorem is stated for all even `N`, just delete the
`4 ≤ N` argument below.
-/
theorem preΨ'_deriv_ne_zero_at_root_via_even_double
    {n : ℕ} (hn3 : 3 ≤ n) (h2 : (2 : K) ≠ 0) (hn : (n : K) ≠ 0)
    (hEvenSep :
      ∀ {N : ℕ}, Even N → 4 ≤ N → (N : K) ≠ 0 → ∀ {x : K},
        (W.preΨ' N).IsRoot x → ¬ (derivative (W.preΨ' N)).IsRoot x)
    {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  intro hder

  -- Center the Mathlib recurrence at `m + 3 = n`.
  let m : ℕ := n - 3
  have hn_center : n = m + 3 := by
    omega

  have hx_center : (W.preΨ' (m + 3)).IsRoot x := by
    simpa [hn_center] using hx
  have hder_center : (derivative (W.preΨ' (m + 3))).IsRoot x := by
    simpa [hn_center] using hder

  -- The doubled index is even and still nonzero in `K` because `2` and `n` are nonzero.
  have hN_even : Even (2 * (m + 3)) := by
    use m + 3
    omega
  have hN_ge4 : 4 ≤ 2 * (m + 3) := by
    omega
  have hm_nz : ((m + 3 : ℕ) : K) ≠ 0 := by
    simpa [hn_center] using hn
  have hN_nz : ((2 * (m + 3) : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero h2 hm_nz

  -- A double root of the center factor would be a double root of the doubled even polynomial.
  have hroot2 : (W.preΨ' (2 * (m + 3))).IsRoot x :=
    W.preΨ'_root_two_mul_of_root_center hx_center
  have hder2 : (derivative (W.preΨ' (2 * (m + 3)))).IsRoot x :=
    W.preΨ'_derivative_root_two_mul_of_double_root_center hx_center hder_center

  exact (hEvenSep hN_even hN_ge4 hN_nz hroot2) hder2

/-- The odd `n ≥ 5` wrapper.  Oddness is only used conceptually to identify the remaining
case after the even theorem; the algebraic reduction itself only needs `(2 : K) ≠ 0`. -/
theorem preΨ'_odd_ge5_deriv_ne_zero_at_root_via_even
    {n : ℕ} (_hn_odd : Odd n) (hn5 : 5 ≤ n)
    (h2 : (2 : K) ≠ 0) (hn : (n : K) ≠ 0)
    (hEvenSep :
      ∀ {N : ℕ}, Even N → 4 ≤ N → (N : K) ≠ 0 → ∀ {x : K},
        (W.preΨ' N).IsRoot x → ¬ (derivative (W.preΨ' N)).IsRoot x)
    {x : K} (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  exact W.preΨ'_deriv_ne_zero_at_root_via_even_double
    (hn3 := by omega) h2 hn hEvenSep hx

end WeierstrassCurve
```

## How to plug this into the final theorem

In the odd branch of your strong induction or case split, do this:

```lean
by_cases h2 : (2 : K) = 0
· -- characteristic 2 branch; odd-via-even is unavailable here.
  -- Need the separate char-2 odd proof.
  sorry
· -- characteristic not 2.
  exact W.preΨ'_odd_ge5_deriv_ne_zero_at_root_via_even
    hn_odd hn5 h2 hn
    (fun {N} hN_even hN_ge4 hN_nz {x} hxN =>
      W.preΨ'_deriv_ne_zero_at_root_even hN_even hN_ge4 hN_nz hxN)
    hx
```

Adjust the final lambda to match the exact argument order of your even theorem.  If your even theorem does not require `4 ≤ N`, remove `hN_ge4` from both the helper theorem and the lambda.

## Why the proof is sound

Assume, toward contradiction,

```text
preΨ'(n)(x) = 0
(preΨ'(n))'(x) = 0.
```

By the factorization

```text
preΨ'(2n) = preΨ'(n) · C_n,
```

we get

```text
preΨ'(2n)(x) = 0.
```

Differentiating the product gives

```text
(preΨ'(2n))'(x)
  = (preΨ'(n))'(x) · C_n(x) + preΨ'(n)(x) · C_n'(x)
  = 0.
```

But `2n` is even, `2n ≥ 4`, and `(2n : K) ≠ 0`, so the even separability theorem says that a root of `preΨ'(2n)` cannot also be a root of its derivative.  Contradiction.

This is exactly the desired reduction.

## Characteristic `2`

The reduction cannot prove the remaining characteristic-`2` odd case, because then

```text
(2n : K) = 0
```

for every `n`, so the even separability theorem for `2n` is not applicable.  In the global proof, the branch split should therefore be:

```text
char K ≠ 2:
  all odd n ≥ 5 reduce to the even theorem at 2n;

char K = 2:
  only odd n can satisfy (n : K) ≠ 0, and these need a separate odd/char-2 proof.
```

So the odd-via-even reduction is a clean way to remove the odd case in characteristic not `2`, but it is not a substitute for the characteristic-`2` argument.
