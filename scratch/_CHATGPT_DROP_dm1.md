# Q2075 (dm1): Can the finite Mazur obstruction use only Hasse?

Date: 2026-06-28.

Question: for the Mazur proof over `ℚ`, can we prove

```text
E[m] fully rational over ℚ  →  m ≤ 2
```

for

```text
m ∈ {3,4,5,6,7,8,9,10,12}
```

without the Weil pairing, using only reduction modulo a prime and the Hasse bound?

Proposed argument:

```text
If E[m](ℚ) contains (ℤ/mℤ)^2, then m^2 divides #E(𝔽_p) for all good primes p.
Hasse: #E(𝔽_p) = p + 1 - a_p with |a_p| ≤ 2√p.
At p = 2, #E(𝔽_2) ≤ 2 + 1 + 2√2 < 6, so m^2 ≤ 5 and m ≤ 2.
```

## Verdict

**No, not as stated.**  The `p = 2` proof is not a valid uniform replacement for the Weil-pairing obstruction.

It becomes valid only under extra hypotheses such as:

```text
E has good reduction at 2, and 2 ∤ m.
```

That covers an odd `m` curve with good reduction at `2`, but it does not cover all elliptic curves over `ℚ`, and it does not cover even `m` at `p = 2`.

The correct reduction statement is:

```text
If E has good reduction at p and p ∤ m,
then the reduction map injects E[m](ℚ) into E(𝔽_p).
```

So, under full rational `m`-torsion, for every good prime `p ∤ m`, one gets

```text
m^2 ∣ #E(𝔽_p).
```

The condition `p ∤ m` is essential.  At primes dividing `m`, the reduction map on `m`-torsion need not be injective.

The condition that `p` is a good prime is also essential.  A fixed small prime, such as `2`, can be a bad prime for `E`.

## The correct Hasse-only lemma

The Hasse-bound argument proves the following conditional lemma.

```text
Lemma.
Assume E/ℚ has full rational m-torsion.
Let p be a good prime for E with p ∤ m.
If p < (m - 1)^2, then contradiction.
```

Proof:

```text
full rational m-torsion + good p ∤ m
  ⇒ (ℤ/mℤ)^2 injects into E(𝔽_p)
  ⇒ m^2 ∣ #E(𝔽_p)
  ⇒ m^2 ≤ #E(𝔽_p)

Hasse gives
  #E(𝔽_p) ≤ p + 1 + 2√p = (√p + 1)^2.

If p < (m - 1)^2, then √p + 1 < m, hence
  #E(𝔽_p) < m^2,
contradiction.
```

This is useful for a **specific** elliptic curve once we can exhibit one good prime `p ∤ m` with `p < (m - 1)^2`.  It is not a uniform theorem over all elliptic curves over `ℚ`, because an elliptic curve can have bad reduction at the small primes one wants to use.

## What goes wrong with `p = 2`

For `p = 2`, Hasse gives

```text
#E(𝔽_2) ≤ 2 + 1 + 2√2 < 6,
```

so, since the group order is an integer,

```text
#E(𝔽_2) ≤ 5.
```

If `E` has good reduction at `2` and `m` is odd, then full rational `m`-torsion would imply

```text
m^2 ∣ #E(𝔽_2),
```

hence `m^2 ≤ 5`, so `m ≤ 2`.  This rules out odd `m ≥ 3` **only for curves with good reduction at 2**.

But this does not prove the Mazur obstruction uniformly:

1. `E` may have bad reduction at `2`.
2. If `m` is even, then `2 ∣ m`, so prime-to-`p` injectivity of the `m`-torsion reduction map does not apply at `p = 2`.

Thus the proposed one-line proof is invalid for even values

```text
m = 4, 6, 8, 10, 12,
```

and also invalid for odd values if the curve has bad reduction at `2`.

## Table for the requested finite set

For each `m`, Hasse gives a contradiction at any good prime

```text
p ∤ m  and  p < (m - 1)^2.
```

Here are the first possible small primes:

```text
m = 3:   p = 2 only works, and only if E has good reduction at 2.

m = 4:   p = 3,5,7 would work if one is good.

m = 5:   p = 2,3,7,11,13 would work if one is good.

m = 6:   p = 5,7,11,13,17,19,23 would work if one is good.

m = 7:   any good p ∈ {2,3,5,11,13,17,19,23,29,31} works.

m = 8:   any good odd p < 49 works.

m = 9:   any good p < 64 with p ≠ 3 works.

m = 10:  any good p < 81 with p ≠ 2,5 works.

m = 12:  any good p < 121 with p ≠ 2,3 works.
```

This table is conditional.  It does **not** prove the desired statement for every elliptic curve over `ℚ`, because one cannot guarantee from Hasse alone that at least one of the listed small primes is a good prime for `E`.

## Why this cannot replace the Weil pairing

The Weil-pairing obstruction is global and field-theoretic:

```text
full rational E[m]  ⇒  μ_m ⊂ ℚ.
```

But `ℚ` contains only the roots of unity `±1`, so this forces

```text
m ≤ 2.
```

That proof does not need a good reduction prime.

The Hasse argument is instead local-at-a-prime:

```text
full rational E[m] + good reduction at p + p ∤ m
  ⇒ m^2 ∣ #E(𝔽_p)
  ⇒ Hasse may contradict this if p is small enough.
```

It is excellent for checking a specific curve, or for ruling out full `m`-torsion for curves known to have good reduction at a suitable small prime.  It is not enough for the uniform Mazur proof over `ℚ`.

## Lean-oriented lemma shape

The clean abstraction to formalize is not the false `p = 2` theorem, but the conditional lemma:

```lean
/-- Hasse obstruction to full rational m-torsion at one good prime. -/
theorem full_mtorsion_absurd_of_good_prime_hasse
    {m p : ℕ}
    -- E has good reduction at p
    (hgood : GoodReduction E p)
    -- p does not divide m
    (hpm : ¬ p ∣ m)
    -- full rational m-torsion injects into the reduction
    (hinj : InjectsFullMTorsionIntoReduction E m p)
    -- Hasse bound for the reduction
    (hhasse : Nat.card Efp ≤ p + 1 + floor_sqrt_bound p)
    -- small-prime condition, mathematically p < (m - 1)^2
    (hsmall : p < (m - 1)^2) :
    False := by
  -- From `hinj`: m^2 ∣ #E(F_p), hence m^2 ≤ #E(F_p).
  -- From Hasse + hsmall: #E(F_p) < m^2.
  -- Contradiction.
  sorry
```

For actual Mathlib, the exact statement will depend on the available finite-field elliptic-curve and good-reduction API.  The mathematical lemma should have these hypotheses explicitly:

```text
good reduction at p,
p ∤ m,
full rational m-torsion injects after reduction,
p < (m - 1)^2.
```

## Bottom line

The proposed proof is correct only in the special case where the chosen small prime is good and prime to `m`.  It does **not** work for all the needed values in `{3,4,5,6,7,8,9,10,12}` uniformly over all elliptic curves over `ℚ`.

So for the Mazur proof, the Weil-pairing primitive-root obstruction is still the right clean route for

```text
E[m] fully rational over ℚ  ⇒  m ≤ 2.
```
