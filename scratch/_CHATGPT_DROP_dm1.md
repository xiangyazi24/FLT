# Q867 (dm1): breaking the even/odd circularity

## Bottom line

The circularity is real.  It is not just a Lean termination/checker artifact.

The bad dependency is:

```text
OddSep n
  └─ tries to use EvenSep (2*n)
        └─ in the factor-root branch of Ψ(2*n) = Ψ(n) * C_n,
           EvenSep (2*n) needs Sep n again
```

So no well-founded induction on `n` can accept the current proof graph.  One of these two edges must be removed:

1. remove `OddSep n → EvenSep (2*n)`, or
2. remove `EvenSep (2*n) → Sep n` in the factor-root branch.

As stated, **A** and **D** only remove the cofactor-root branch, not the factor-root branch.  Therefore they are useful, but they do **not** by themselves break the odd/even cycle.

My recommendation is:

* **Near-term / polynomial-only work:** finish **A** and package it as **D**, because it is the right way to close the even case cleanly.
* **For the complete non-circular separability proof:** use **C** as the main theorem interface.  The formal-group tangent bridge is the real cycle breaker.  Once it exists, both odd and even separability become corollaries, and the parity induction can be deleted or demoted to auxiliary recurrence facts.
* **B** is conceptually good, but in Lean it is not cheaper than C unless you already have the point/order/root bridge.  Exact-order induction still needs the same local tangent fact for primitive roots.

So the feasible Lean answer is: **do A/D for the even infrastructure, but do not expect A/D alone to prove odd via `2n`; the robust final route is C.**

## Why A alone is not enough

Write the even factorization schematically as

```text
Ψ(2*k) = Ψ(k) * C_k
```

At a root `x` of `Ψ(2*k)`, the product-rule proof splits into two meaningful branches.

### Branch 1: `Ψ(k)(x) = 0`

Then

```text
(Ψ(2*k))'(x) = Ψ(k)'(x) * C_k(x)
```

To prove this is nonzero, you need both:

```text
Ψ(k)'(x) ≠ 0
C_k(x) ≠ 0
```

The first is exactly `Sep k`.  The second is a disjointness/cofactor-nonvanishing fact.

### Branch 2: `C_k(x) = 0`

Then, provided `Ψ(k)(x) ≠ 0`,

```text
(Ψ(2*k))'(x) = Ψ(k)(x) * C_k'(x)
```

To prove this is nonzero, you need cofactor separability:

```text
C_k'(x) ≠ 0
```

This is your “Even Case B”.

Therefore proving Even Case B independently is necessary for the even case, but it only solves Branch 2.  Branch 1 still depends on `Sep k`.

Now put `k = n`, where `n` is the current odd goal.  The attempted proof of `OddSep n` by `EvenSep (2*n)` lands exactly in Branch 1, so the even proof wants `Sep n`, which is the current theorem.

That is the circularity.

## Why D, in the naive form, also does not break the cycle

If the strengthened induction statement is merely

```lean
Sep n ∧ CofactorSep n
```

then the even case gets cleaner, but the dependency graph is still:

```text
OddSep n
  → EvenSep (2*n)
  → Sep n
```

So this strengthened IH is valuable but insufficient.

A strengthened statement would break the cycle only if it included a genuinely new primitive/local assertion, for example:

```text
Primitive roots of Ψ(n) are simple directly,
```

or

```text
[n] has nonzero tangent multiplier n at every n-torsion point.
```

But that is essentially option C, or option B plus the core tangent lemma.

## Why B is mathematically clean but Lean-heavy

The order-of-torsion induction is the right conceptual picture:

```text
root of Ψ(n)
  ↔ x-coordinate of a nonzero n-torsion point P
let d = exact order of P
then d ∣ n
```

If `d < n`, one wants to reduce to `Ψ(d)`.  If `d = n`, one proves the primitive root is simple directly.

The problem is that, in Lean, this route requires a lot of infrastructure:

1. a point-level elliptic curve group law over the relevant field or algebraic closure;
2. a theorem connecting roots of `preΨ n` with nonzero `n`-torsion points;
3. exact order, divisibility, and transport between point order and polynomial roots;
4. a proof that primitive torsion roots are simple.

Item 4 is exactly the formal tangent bridge in another form.  So B is not really cheaper than C.  It is a good organizational layer after C exists, but I would not use it as the first Lean route.

## Why C is the real cycle breaker

The formal-group/tangent statement says, morally:

```text
The differential of [n] on the elliptic curve is multiplication by n.
```

So under the usual separability hypothesis

```lean
(n : K) ≠ 0
```

multiplication by `n` is étale.  Hence the `n`-torsion kernel is reduced.  The division polynomial cuts out the nonzero `n`-torsion in the `x`-coordinate, so its roots are simple.

The final user-facing theorem can be stated at the polynomial level, hiding all the geometry behind one bridge lemma:

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Polynomial-level separability theorem for the x-division polynomial. -/
theorem preΨ_derivative_ne_zero_of_eval_eq_zero
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ n).eval x = 0) :
    (Polynomial.derivative (W.preΨ n)).eval x ≠ 0 := by
  -- bridge to a point above `x`, use the tangent of `[n]`, then descend
  -- reducedness/simple-root statement back to the x-division polynomial
  sorry

end WeierstrassCurve
```

Once this theorem exists, the parity split becomes unnecessary:

```lean
theorem preΨ_separable
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Squarefree (W.preΨ n) := by
  -- use `preΨ_derivative_ne_zero_of_eval_eq_zero`
  sorry
```

Or, if your current goal is phrased as a rootwise derivative statement, the rootwise theorem above is already the desired endpoint.

## How to use A/D without getting stuck

I would still finish the cofactor work because it is valuable and much more local than the formal group bridge.

Use it to make the even theorem modular:

```lean
/-- Roots of the doubling cofactor are simple and disjoint from roots of `Ψ k`. -/
def DoubleCofactorGood (W : WeierstrassCurve K) (k : ℕ) : Prop :=
  ∀ x,
    -- schematic:
    C_k.eval x = 0 →
      (W.preΨ k).eval x ≠ 0 ∧
      (Polynomial.derivative C_k).eval x ≠ 0

/-- The even step, with all cofactor obligations explicit. -/
theorem even_sep_of_sep_and_cofactor_good
    {k : ℕ}
    (hSep : Sep W k)
    (hCof : DoubleCofactorGood W k) :
    Sep W (2*k) := by
  -- product rule on `Ψ(2*k) = Ψ(k) * C_k`
  sorry
```

This is the right form of D: not because it solves odd separability, but because it prevents the even proof from hiding cofactor obligations in nested case splits.

Then use C to close `Sep W k` uniformly.  After that, `even_sep_of_sep_and_cofactor_good` becomes either redundant or useful as a consistency check / recurrence lemma.

## Practical Lean plan

1. **Do not continue trying to make `OddSep n` call `EvenSep (2*n)` inside the same strong induction.**  That proof graph is cyclic.

2. **Finish Even Case B independently.**  This is still useful.  It gives a clean theorem of the form:

   ```lean
   DoubleCofactorGood W k
   ```

   or whatever exact cofactor notation your file uses.

3. **Refactor the even step so its dependencies are explicit:**

   ```lean
   Sep W k → DoubleCofactorGood W k → Sep W (2*k)
   ```

   This keeps the polynomial recurrence layer sane.

4. **Introduce one central tangent-bridge theorem with a narrow interface.**

   Start with the polynomial-level statement you actually need, even if the first version is a `sorry`:

   ```lean
   theorem preΨ_derivative_ne_zero_of_eval_eq_zero
       {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
       (hx : (W.preΨ n).eval x = 0) :
       (Polynomial.derivative (W.preΨ n)).eval x ≠ 0 := by
     sorry
   ```

   Then route both odd and even separability through this theorem.

5. **Only after that, decide whether to prove the bridge via formal groups or via a point/order formulation.**

   The order-of-torsion induction can be a nice internal proof of the bridge, but it should not be the public dependency of the parity induction unless the point/order API is already mature.

## Ranking of the options

### Best complete cycle breaker: C

C removes the parity induction entirely.  It is the cleanest final theorem and gives the strongest Lean API.

### Best near-term local work: A packaged as D

A/D is the best way to finish the even recurrence proof and eliminate the current Even Case B sorry.  But it is not, by itself, a proof of odd separability.

### B is conceptually right but probably not the fastest Lean implementation

B still needs the point/root/order/tangent infrastructure.  If that infrastructure already exists, B is fine.  If it does not, C is a better target because it packages the required geometry into one theorem instead of spreading it through an exact-order induction.

### D alone does not solve the cycle

`Sep n ∧ CofactorSep n` is not enough.  It helps the even step but leaves the same `OddSep n → EvenSep (2*n) → Sep n` loop.

## Final recommendation

For Lean 4, I would proceed as follows:

```text
1. Finish Even Case B independently.
2. Package the even proof as:
      Sep k → DoubleCofactorGood k → Sep (2*k).
3. Stop using even(2n) to prove odd(n) inside the same induction.
4. Add the formal-group/tangent bridge as the central theorem:
      (n : K) ≠ 0 → every root of preΨ n is simple.
5. Use that theorem to close odd and even separability uniformly.
```

So: **A/D is the right local cleanup, but C is the actual non-circular endpoint.**
