# Q2078 (dm4): Does the Hasse-bound shortcut eliminate the Weil-pairing step, and what about `m = 4`?

Date: 2026-06-28.

Question: suppose `E/ℚ` has full rational `m`-torsion, i.e.

```text
E[m](ℚ) ≃ (ZMod m)^2.
```

Can we avoid the Weil pairing by reducing modulo a small prime and using Hasse?

The tempting argument is:

```text
E[m](ℚ) injects into E(𝔽_p) if p ∤ m and E has good reduction at p,
so m^2 ≤ #E(𝔽_p) ≤ p + 1 + 2√p.
```

For odd `m`, using `p = 2` would give

```text
m^2 ≤ #E(𝔽_2) ≤ 5,
```

contradicting `m ≥ 3`.  But for `m = 4`, `p = 2` is unavailable, and the first odd primes give:

```text
p = 3:  #E(𝔽_3) ≤ floor(3 + 1 + 2√3) = 7
p = 5:  #E(𝔽_5) ≤ floor(5 + 1 + 2√5) = 10
p = 7:  #E(𝔽_7) ≤ floor(7 + 1 + 2√7) = 13
p = 11: #E(𝔽_11) ≤ floor(11 + 1 + 2√11) = 18
```

So full rational `4`-torsion would contradict Hasse at a **good** prime `p = 3, 5, or 7`, but not at `p = 11`.

## Executive answer

The Hasse-bound shortcut does **not** uniformly replace the Weil-pairing argument.

For `m = 4`, the shortcut proves a contradiction only if `E` has good reduction at one of

```text
3, 5, 7.
```

There is no general reason, from the bare hypothesis “full rational `4`-torsion,” that one of these primes must be a good-reduction prime unless we add more arithmetic input.  An elliptic curve can have bad reduction at any prescribed finite set of primes by having discriminant divisible by those primes, and the naive Hasse-count argument only applies at good primes.

So yes: **in the current Mazur-proof scaffold, `m = 4` still needs a non-Hasse input**.  The Weil pairing is the cleanest such input:

```text
E[4](ℚ) full ⇒ μ_4 ⊂ ℚ,
```

which is impossible because `ℚ` has no primitive fourth root of unity.

There are possible alternatives to the Weil pairing, but they are not the bare Hasse shortcut.

## The hidden hypothesis: good reduction

The reduction injection is not simply:

```text
p ∤ m ⇒ E[m](ℚ) ↪ E(𝔽_p).
```

The usual statement is:

```text
if E has good reduction at p and p ∤ m,
then reduction is injective on m-torsion.
```

Thus, even for odd `m`, the `p = 2` shortcut only works when `E` has good reduction at `2`.  For an arbitrary elliptic curve over `ℚ`, `2` may be a bad prime.

This matters because the Mazur torsion-bound argument is about arbitrary elliptic curves over `ℚ`, not just curves with good reduction at `2`.

## What the Hasse shortcut actually gives

For any good prime `p ∤ m`, full rational `m`-torsion gives:

```text
m^2 ≤ #E(𝔽_p) ≤ p + 1 + 2√p = (√p + 1)^2.
```

So a contradiction occurs when:

```text
m > √p + 1,
```

or equivalently:

```text
p < (m - 1)^2.
```

For `m = 4`, this means:

```text
p < 9,
```

and since `p ∤ 4`, the useful primes are exactly:

```text
3, 5, 7.
```

Therefore:

```text
If E has full rational 4-torsion and good reduction at 3, 5, or 7,
then Hasse gives a contradiction.
```

But this is only conditional.

## Why `p = 11` no longer contradicts `m = 4`

At `p = 11`, Hasse gives:

```text
#E(𝔽_11) ≤ 11 + 1 + 2√11 < 19,
```

so, since the cardinality is an integer,

```text
#E(𝔽_11) ≤ 18.
```

Full rational `4`-torsion would only force:

```text
16 ≤ #E(𝔽_11),
```

and `16 ≤ 18` is possible.  So every good prime `p ≥ 11` is too large for this single-prime Hasse contradiction.

## Could we prove one of `3,5,7` is good from full rational `4`-torsion?

Not by the bare reduction/Hasse argument.  Proving such a statement would require additional arithmetic information about the discriminant or reduction type of a curve with full rational `4`-torsion.

Possible non-Weil alternatives include:

1. **A halving criterion for full `2`-torsion.**
   If
   ```text
   E : y^2 = (x-a)(x-b)(x-c)
   ```
   with `a,b,c ∈ ℚ`, then a rational `2`-torsion point is divisible by `2` over `ℚ` only under explicit square conditions on root differences.  Over the ordered field `ℚ`, the middle root gives opposite signs, obstructing full rational `4`-torsion.  This can prove no full rational `4`-torsion without the Weil pairing, but it is a different elliptic-curve theorem.

2. **A modular-curve/full-level-4 argument.**
   Full rational `4`-torsion is a rational full level-4 structure.  One can rule this out by analyzing the corresponding level modular curve, but this is far heavier than the Weil-pairing consequence.

3. **A stronger reduction theorem with local reduction-type analysis.**
   One could try to handle the case where `3,5,7` are all bad by studying component groups or local torsion.  This is not the simple Hasse shortcut and likely becomes more work than the Weil-pairing seam.

## Does `m = 4` need the Weil pairing?

For the current formalization strategy: **yes, or something morally replacing it.**

More precisely:

```text
m = 4 does not necessarily need the full general Weil-pairing library,
but it does need an additional theorem beyond Hasse + good-reduction injection.
```

The cleanest additional theorem remains the Weil-pairing consequence:

```lean
axiom/theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then `m = 4` is immediately impossible because a primitive fourth root of unity cannot lie in `ℚ`.

## Practical recommendation

Do not replace the Weil-pairing seam by the Hasse shortcut globally.

Instead, record the Hasse shortcut as a useful **conditional lemma**:

```text
If E has full rational m-torsion, and E has good reduction at some p ∤ m
with p < (m - 1)^2, then contradiction.
```

This lemma is valuable and can discharge many cases when a suitable good small prime is known.  But it does not prove the general `m ≤ 2` result for arbitrary `E/ℚ`, and it especially does not handle `m = 4` without extra input.

For the Mazur proof, keep the high-level Weil-pairing consequence as the stable axiom/interface.  If later we want a no-Weil proof of the `m = 4` case, the most plausible separate target is an explicit halving criterion for full rational `2`-torsion, not the single-prime Hasse bound.
