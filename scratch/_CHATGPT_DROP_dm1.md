# Q1024 (dm1): `dm3` — strengthened induction for division-polynomial separability

The prompt body I received was only:

```text
Q1024 (dm1): dm3
```

I searched the repository for `Q1024` and `dm3` and found no matching task body.  I therefore interpret `dm3` as the earlier division-polynomial/separability question about whether the even/odd circularity can be broken by strengthening the induction hypothesis to include both separability of `preΨ' n` and separability of the even cofactor in

```text
preΨ'(2k) = preΨ'(k) * C_k.
```

## Short answer

The naive strengthened induction

```text
P(k) := Sep(k) ∧ CofactorSep(k)
```

is **not enough by itself**, unless `CofactorSep(k)` has an independent proof whose dependencies are strictly smaller than `k`.

The better polynomial-only version is to index the cofactor obligation by its **ambient target size** `2k`, not by `k`.  In other words, treat `CofactorSep(k)` as an obligation of size `2k`, because it is used to prove separability of `preΨ'(2k)`.

Then the right strengthened invariant is closer to:

```text
Ledger(N) :=
  (∀ n ≤ N, Sep(n))
  ∧
  (∀ k, 2*k ≤ N → CofactorSep(k)).
```

This can break the **even-case** circularity if you can prove:

```text
CofactorSep(k) from Sep(j) for j < 2*k.
```

However, it still does **not** justify proving odd `Sep(n)` by calling the even theorem for `Sep(2n)`, because `2n` is outside the current induction range and the even proof of `Sep(2n)` still needs `Sep(n)` in the factor-root branch.

So the strengthened induction is useful only if paired with either:

1. a direct odd-step proof from the odd recurrence, or
2. the formal-group/tangent bridge proving rootwise separability for all `n` at once.

## Why `P(k) := Sep(k) ∧ CofactorSep(k)` is the wrong indexing

The even factorization has the form:

```text
preΨ'(2k) = preΨ'(k) * C_k.
```

For the rootwise derivative proof of `Sep(2k)`, at a root `x` of the product, there are two branches.

### Branch A: `preΨ'(k)(x) = 0`

The derivative of the product reduces to

```text
(preΨ'(k))'(x) * C_k(x).
```

So this branch needs:

```text
Sep(k)
C_k(x) ≠ 0
```

The first is genuinely a smaller separability result, since `k < 2k`.

### Branch B: `C_k(x) = 0`

The derivative of the product reduces to

```text
preΨ'(k)(x) * C_k'(x).
```

So this branch needs:

```text
preΨ'(k)(x) ≠ 0
C_k'(x) ≠ 0
```

This is the cofactor-separability/disjointness obligation.

The important point is that `C_k` belongs naturally to the proof of `Sep(2k)`, not to the proof of `Sep(k)`.  Its definition usually involves division-polynomial terms around `k`, such as neighboring indices in the doubling recurrence.  Those indices are generally `< 2k`, but not necessarily `< k`.

So if you try to prove `CofactorSep(k)` already at stage `k`, the available IH is too small.  This is why the naive strengthened statement tends to feel circular.

## Better invariant: a target-bound ledger

Use an invariant parameterized by the maximum target index `N`.

Schematic Lean interface:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Rootwise separability of a polynomial. -/
def RootwiseSep (P : K[X]) : Prop :=
  ∀ x : K, P.eval x = 0 → P.derivative.eval x ≠ 0

/-- Rootwise separability of the `n`th x-division polynomial. -/
def Sep (n : ℕ) : Prop :=
  RootwiseSep (W.preΨ n)

/--
The even doubling cofactor `C_k` in
`preΨ (2*k) = preΨ k * C_k`.

Replace this placeholder by the actual cofactor definition already used in the file.
-/
def DoubleCofactor (k : ℕ) : K[X] :=
  0

/-- The package needed in the cofactor-root branch of the even proof. -/
def DoubleCofactorGood (k : ℕ) : Prop :=
  ∀ x : K,
    (DoubleCofactor (W := W) k).eval x = 0 →
      (W.preΨ k).eval x ≠ 0 ∧
      ((DoubleCofactor (W := W) k).derivative).eval x ≠ 0

/-- Separability known up to target size `N`. -/
def SepUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → Sep (W := W) n

/-- Cofactor obligations whose ambient double target is at most `N`. -/
def CofactorGoodUpTo (N : ℕ) : Prop :=
  ∀ k : ℕ, 2 * k ≤ N → DoubleCofactorGood (W := W) k

/-- The strengthened induction ledger. -/
def SepLedger (N : ℕ) : Prop :=
  SepUpTo (W := W) N ∧ CofactorGoodUpTo (W := W) N

end WeierstrassCurve
```

The key theorem you want is not

```lean
Sep k → CofactorSep k
```

but rather:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

-- Use the actual definitions from the previous code block / repository.

/--
Cofactor goodness for `C_k` should be proved from separability facts whose
indices are all strictly below the ambient target `2*k`.
-/
theorem doubleCofactorGood_of_sep_lt_double
    (k : ℕ)
    (hSepLower : ∀ j : ℕ, j < 2 * k → RootwiseSep (W.preΨ j)) :
    DoubleCofactorGood (W := W) k := by
  -- Prove by expanding the actual doubling cofactor formula.
  -- The important admissibility condition is: every division-polynomial
  -- separability fact used here must have index `< 2*k`, not merely `< k`.
  sorry

end WeierstrassCurve
```

Once this theorem exists, the even step is clean.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/--
Even separability from the smaller factor and the doubling cofactor package.
This is the correct local replacement for the problematic even branch split.
-/
theorem sep_even_of_sep_and_doubleCofactorGood
    (k : ℕ)
    (hSepK : RootwiseSep (W.preΨ k))
    (hCof : DoubleCofactorGood (W := W) k)
    (hFactor : W.preΨ (2 * k) = W.preΨ k * DoubleCofactor (W := W) k) :
    RootwiseSep (W.preΨ (2 * k)) := by
  intro x hx
  rw [hFactor] at hx ⊢
  -- Product-root split:
  --   eval (Ψ_k * C_k) x = 0
  -- gives either `Ψ_k.eval x = 0` or `C_k.eval x = 0` over a field.
  -- In the first branch use `hSepK` plus cofactor nonvanishing/disjointness.
  -- In the second branch use `hCof`.
  -- The exact proof is routine with:
  --   Polynomial.eval_mul
  --   Polynomial.derivative_mul
  --   IsDomain.mul_eq_zero
  --   mul_ne_zero
  -- but the concrete names may differ in the current file.
  sorry

end WeierstrassCurve
```

## How the induction should be organized

The safe polynomial-only proof has this shape:

```text
Strong induction on target bound N.
Assume SepLedger(M) for all M < N.
Prove SepLedger(N).

To prove new cofactor obligations with 2*k = N:
  use doubleCofactorGood_of_sep_lt_double k,
  because all required Sep(j) have j < 2*k = N,
  hence they are available from SepLedger(N-1).

To prove Sep(N):
  if N = 2*k, use
      sep_even_of_sep_and_doubleCofactorGood k.
  if N is odd, do NOT call Sep(2*N).
      use a direct odd recurrence proof, or use the formal tangent bridge.
```

This avoids using `CofactorSep(k)` before it is justified.  The cofactor obligation is introduced exactly when the ambient target `2k` enters the induction frontier.

## The remaining odd obstruction

This strengthened ledger solves only the even cofactor branch.  It does not make the following proof valid:

```text
OddSep(n)
  by applying EvenSep(2n)
```

because `EvenSep(2n)` still has the factor-root branch:

```text
preΨ'(n)(x) = 0
```

and that branch needs `Sep(n)`, which is the current odd goal.

So the old circular dependency remains:

```text
OddSep(n)
  → EvenSep(2n)
  → Sep(n)
```

The only ways out are:

1. **direct odd recurrence:** prove `Sep(2m+1)` directly from the odd division-polynomial recurrence, with all separability dependencies `< 2m+1`; or
2. **formal tangent bridge:** prove that `[n]` has nonzero tangent multiplier `(n : K)`, hence the `n`-torsion kernel is reduced, hence roots of the division polynomial are simple.

## Practical recommendation

For Lean, I would not use the naive statement

```text
∀ k < n, Sep(k) ∧ CofactorSep(k)
```

unless `CofactorSep(k)` already has a genuinely independent proof from indices `< k`.

Instead, use this three-part plan:

1. Prove the cofactor lemma with the correct size bound:

   ```lean
   doubleCofactorGood_of_sep_lt_double
     : (∀ j < 2*k, Sep(j)) → DoubleCofactorGood(k)
   ```

2. Use it in the even step:

   ```lean
   Sep(k) → DoubleCofactorGood(k) → Sep(2*k)
   ```

3. Do not prove odd `Sep(n)` through even `Sep(2n)`.  Either write the direct odd recurrence step, or use the formal-group/tangent bridge as the final theorem.

## Final answer

The strengthened induction idea is salvageable, but only if the cofactor obligation is indexed by the **double target size** `2k`, not by the smaller parameter `k`.

So the answer to the `dm3` question is:

```text
Naive D:      Sep(k) ∧ CofactorSep(k)          -- not enough / wrong size
Better D:     Sep up to N ∧ CofactorSep(k) for 2k ≤ N
Still needed: direct odd step or formal tangent bridge
```

This makes the even case non-circular, but it does not by itself solve the odd case if the odd proof still goes through `even(2n)`.
