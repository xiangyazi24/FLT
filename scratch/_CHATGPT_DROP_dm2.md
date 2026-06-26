# Q868 (dm2): exact-order induction and quotient coprimality for `preΨ'`

## Bottom line

The implication

```text
(preΨ'(d))'(x) ≠ 0  ⇒  (preΨ'(n))'(x) ≠ 0
```

is **not** a consequence of divisibility alone.

If `d ∣ n`, write

```text
F_d := preΨ'(d),
F_n := preΨ'(n),
F_n = F_d · Q.
```

At a root `x` of `F_d`, the product rule gives

```text
F_n'(x) = F_d'(x) · Q(x) + F_d(x) · Q'(x)
        = F_d'(x) · Q(x).
```

So the induction hypothesis `F_d'(x) ≠ 0` proves `F_n'(x) ≠ 0` **only if** one also proves

```text
Q(x) ≠ 0.
```

Equivalently, one needs

```text
gcd(F_d, F_n / F_d) = 1
```

at least locally at `x`.  Without this, the argument fails: a simple root of a factor can become a double root of the product.  The toy counterexample is

```text
F_d = X - a,
F_n = (X - a)^2.
```

Then `F_d'(a) = 1`, but `F_n'(a) = 0`.

Thus the exact-order induction does **not** by itself break the circularity.  It replaces the original separability problem by a quotient-nonvanishing / primitive-factor-coprimality problem.

---

## Is the quotient nonzero for division polynomials?

Mathematically, under the standard good hypothesis

```text
char K ∤ n
```

and after using the correct normalized `preΨ'` factors, the quotient is nonzero at a point of exact order `d < n`.

The reason is the usual torsion-structure statement:

```text
E[n] = disjoint union of exact-order strata,
```

and, when `char K ∤ n`, the group scheme `E[n]` is reduced / finite étale.  Therefore the divisor of `n`-torsion is reduced, and the factors corresponding to different exact orders are pairwise coprime.

Equivalently, the primitive division factors are pairwise coprime:

```text
F_n = ∏_{e ∣ n} F_e^prim,
```

and a point of exact order `d` is a zero only of the primitive `d`-factor, not of the primitive factors for `e ≠ d`.

For the `x`-coordinate polynomial this remains true because `x(P) = x(Q)` implies `Q = ±P` on a nonsingular Weierstrass curve, and `P` and `-P` have the same exact order.  The only nuisance is the usual even / `ψ₂` normalization: Mathlib's `preΨ'` strips off the `ψ₂` factor, so order-2 points have to be treated according to the exact definition of `preΨ'`.  They are not automatically roots of every `preΨ'` one would expect from the full `ψ_n`.

So:

```text
Q(x) ≠ 0
```

is true in the separable-torsion setting, but proving it is essentially the same level of input as proving that the `n`-torsion divisor is reduced.

In bad characteristic it is false in exactly the expected way.  If the characteristic divides `n`, multiplication by `n` can be inseparable, the torsion scheme can be nonreduced, and multiplicities can appear.  Then an old torsion root can reappear with higher multiplicity in `F_n`.

---

## What the exact-order argument really needs

For the descent case `d < n`, with `n = d · m`, the useful local statement is not merely divisibility.  It is:

```text
If P has exact order d,
if F_d has a simple zero at x(P),
and if m ≠ 0 in K,
then F_n has a simple zero at x(P).
```

This can be seen from the local composition

```text
[n] = [m] ∘ [d].
```

Near `P`, choose a local parameter `u` at `P`, and use the formal parameter `t` at `O`.  Since `[d]P = O`, the map `[d]` has a local expansion

```text
t([d](P + u)) = a · u + higher terms,
```

where `a ≠ 0` is the local meaning of `F_d` having a simple zero at `x(P)`.

Then apply `[m]` at the origin.  The formal group expansion is

```text
[m]_F(T) = m · T + O(T^2).
```

If `m ≠ 0` in `K`, then

```text
t([n](P + u))
  = [m]_F(t([d](P + u)))
  = m · a · u + higher terms,
```

and `m · a ≠ 0`.  Therefore `[n]` also has a simple zero at `P`.

Translated back to the quotient factor, this says exactly:

```text
(F_n / F_d)(x(P)) ≠ 0.
```

This is probably the cleanest way to prove the descent case if you want to use the formal tangent lemma you already have:

```text
formalNsmulF_coeff_one : coeff_one([m]_F) = m.
```

But notice that this is already a local separability argument for multiplication maps.  It is not a purely EDS-divisibility argument.

---

## Primitive case `d = n`

The primitive case is precisely where exact-order induction gives no descent.

If `P` has exact order `n`, then `[n]P = O`, but there is no smaller `F_d` whose simple-root statement can be invoked.  One must prove directly that `[n]` is locally separable at `P`.

Again, the formal group gives the right statement.  Since the differential of `[n]` is translation-invariant, the tangent coefficient at every point is the same scalar `n`.  Locally,

```text
t([n](P + u)) = n · a_P · u + higher terms,
```

with `a_P ≠ 0` coming from the chosen local parameters.  If `n ≠ 0` in `K`, this is a simple zero.

So the primitive case is handled by the global isogeny fact:

```text
[n] is separable iff n ≠ 0 in K.
```

This is exactly the Silverman Exercise 3.7 route, and it handles old and primitive torsion points simultaneously.

---

## Lean consequence

The exact-order induction is viable only if you add a strong lemma of the following shape:

```lean
-- schematic only
lemma preΨ'_quotient_nonzero_at_exact_order
    {K : Type*} [Field K]
    (W : WeierstrassCurve K)
    {d m n : ℕ} {x : K}
    (hn : n = d * m)
    (hm : (m : K) ≠ 0)
    -- x comes from a point P of exact order d
    (hexact : ExactOrderPoint W x d)
    -- normalization side conditions for preΨ'
    (hroot_d : (W.preΨ' d).eval x = 0)
    (hsimple_d : (derivative (W.preΨ' d)).eval x ≠ 0) :
    ((W.preΨ' n) / (W.preΨ' d)).eval x ≠ 0 := by
  -- proof cannot come from `F_d ∣ F_n` alone;
  -- it needs local separability of [m] at O, or primitive-factor coprimality.
  sorry
```

Then the derivative step is easy:

```lean
lemma derivative_mul_at_simple_root
    {K : Type*} [Field K]
    {F Q : K[X]} {x : K}
    (hFx : F.eval x = 0)
    (hF' : (derivative F).eval x ≠ 0)
    (hQx : Q.eval x ≠ 0) :
    (derivative (F * Q)).eval x ≠ 0 := by
  rw [derivative_mul]
  simp [eval_add, eval_mul, hFx]
  exact mul_ne_zero hF' hQx
```

So the descent proof would look like:

```lean
have hfactor : W.preΨ' n = W.preΨ' d * Q := by
  -- divisibility / multiplication formula
  sorry

have hQx : Q.eval x ≠ 0 := by
  -- this is the real theorem: primitive-factor coprimality
  -- or local separability of [m] at O
  sorry

rw [hfactor]
exact derivative_mul_at_simple_root hroot_d hsimple_d hQx
```

The second `sorry`, `hQx`, is exactly the hard part.

---

## Recommendation

I would **not** use exact-order induction as the main route unless the repo already has primitive division factors and pairwise-coprimality infrastructure.

The exact-order strategy decomposes the problem into two cases:

1. `d < n`: old torsion roots.  Needs quotient nonvanishing.
2. `d = n`: primitive torsion roots.  Needs a direct primitive separability argument.

But the clean global argument proves both at once:

```text
formalNsmulF_coeff_one
  ⇒ differential of [n] is multiplication by n
  ⇒ [n] is separable when (n : K) ≠ 0
  ⇒ every n-torsion point is reduced
  ⇒ preΨ'(n) has no repeated roots, modulo the ψ₂/preΨ' normalization cases.
```

For Lean, the most useful target lemma is probably not an induction lemma, but a bridge lemma:

```lean
-- schematic
lemma preΨ'_simple_root_of_nsmul_separable
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).eval x = 0) :
    (derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- use [n] separability / local formal parameter bridge
  sorry
```

Then all old-root and primitive-root cases disappear.  The exact-order quotient statement becomes a corollary rather than a prerequisite.

So the answer to your concrete question is:

```text
Does (preΨ'(d))'(x) ≠ 0 imply (preΨ'(n))'(x) ≠ 0?
```

Only with the extra theorem

```text
(preΨ'(n) / preΨ'(d))(x) ≠ 0.
```

And that extra theorem is not free from divisibility.  It is essentially the reducedness / finite-étaleness of prime-to-characteristic torsion, or equivalently the local separability of `[m]` in the factorization `[n] = [m] ∘ [d]`.
