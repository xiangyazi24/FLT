# Q1459 (dm1/dm3): even-`B` branch in `quartic_plus` descent

Do **not** try to prove `both_odd` by local mod arithmetic; the `4 ∣ B` branch is genuinely not killed that way.  But you also do **not** need `both_odd` if you split the descent into two parity-normalized factor pairs.

The key correction to the proposed even-`B` calculation is:

```text
when B is even, U and V are not merely even; they are divisible by 4.
```

Indeed, with

```text
A = 2*r^2 + B^2,
U = A - 2*s,
V = A + 2*s,
```

primitive even-`B` gives `r` odd, and the equation gives `s` odd.  Since `B^2 ≡ 0 (mod 4)` and `r^2 ≡ 1 (mod 2)`, we have

```text
A = 2*r^2 + B^2 ≡ 2 (mod 4),
2*s ≡ 2 (mod 4),
```

so

```text
4 ∣ U,    4 ∣ V.
```

Thus if `B = 2*B₁`, define

```text
U₁ = U / 4,
V₁ = V / 4.
```

Then the product is not `20*B₁^4`; after dividing both factors by `4`, it is exactly

```text
U₁ * V₁ = (U*V)/16 = 5 * B^4 / 16 = 5 * B₁^4.
```

This is the clean replacement for `both_odd`.

## Recommended restructure

Use two branches.

### Odd `B` branch

This is the old branch:

```text
U = 2*r^2 + B^2 - 2*s,
V = 2*r^2 + B^2 + 2*s,
U*V = 5*B^4,
gcd(U,V)=1,
U,V > 0,
U,V odd.
```

Then apply the coprime factorization lemma directly to `U,V,B`.

### Even `B` branch

Write `B = 2*B₁`.  Replace the factor pair by

```text
U₁ = (2*r^2 + B^2 - 2*s) / 4,
V₁ = (2*r^2 + B^2 + 2*s) / 4.
```

Then prove the normalized package:

```text
0 < U₁,
0 < V₁,
U₁ * V₁ = 5 * B₁^4,
gcd(U₁,V₁)=1.
```

The gcd proof is not the old `U,V` gcd proof.  Use:

```text
U₁ + V₁ = r^2 + 2*B₁^2,
V₁ - U₁ = s.
```

So any common prime `p` of `U₁,V₁` divides both

```text
s
r^2 + 2*B₁^2.
```

Also `p ∣ U₁*V₁ = 5*B₁^4`.

Now split:

* if `p ∣ B₁`, then `p ∣ r^2`, hence `p ∣ r`, contradicting `gcd(r,B)=1`;
* if `p ∤ B₁`, then `p = 5`; but `5 ∣ r^2 + 2*B₁^2` gives

```text
(r/B₁)^2 ≡ -2 ≡ 3  (mod 5),
```

impossible because the nonzero square classes mod `5` are `1,4`.

This proves `gcd(U₁,V₁)=1`.

Then apply the **same** coprime factorization theorem to `U₁,V₁,B₁`:

```text
∃ a b,
  0<a ∧ 0<b ∧ gcd(a,b)=1 ∧ a*b=B₁ ∧
    ((U₁=a^4 ∧ V₁=5*b^4) ∨ (U₁=5*a^4 ∧ V₁=b^4)).
```

## What identity comes out?

This is why the even branch is actually pleasant.  From

```text
U₁ + V₁ = r^2 + 2*B₁^2,
B₁ = a*b,
```

if

```text
U₁ = a^4,
V₁ = 5*b^4,
```

then

```text
r^2 = a^4 + 5*b^4 - 2*a^2*b^2
    = (a^2 - b^2)^2 + (2*b^2)^2.
```

If the `5` is on the other side,

```text
U₁ = 5*a^4,
V₁ = b^4,
```

then

```text
r^2 = 5*a^4 + b^4 - 2*a^2*b^2
    = (b^2 - a^2)^2 + (2*a^2)^2.
```

So the even-`B` branch feeds directly into a primitive Pythagorean triple with hypotenuse `r`, not `2*r`.

Compare with the odd-`B` branch: there the same calculation gives a Pythagorean triple with hypotenuse `2*r`.  That is exactly why trying to force one unified `both_odd` lemma is awkward.

## Lean-level plan

I would add a separate normalized lemma rather than patching `both_odd`:

```lean
/-- Even-`B` normalized factor pair.  Here `B = 2*B₁`. -/
lemma even_B_factor_package
    {r B B₁ s : ℤ}
    (hB : B = 2 * B₁)
    (hquartic : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hcop : Int.gcd r B = 1)
    (hrpos : 0 < r) (hBpos : 0 < B) :
    let U : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
    let V : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s
    ∃ U₁ V₁ : ℤ,
      U = 4 * U₁ ∧
      V = 4 * V₁ ∧
      0 < U₁ ∧
      0 < V₁ ∧
      U₁ * V₁ = 5 * B₁ ^ 4 ∧
      Int.gcd U₁ V₁ = 1 ∧
      U₁ + V₁ = r ^ 2 + 2 * B₁ ^ 2 ∧
      V₁ - U₁ = s := by
  -- parity: r odd from gcd and B even; s odd from mod 2
  -- divisibility: `4 ∣ U`, `4 ∣ V`
  -- product: from `(A-2s)(A+2s)=5B^4`, substitute `B=2B₁`, cancel `16`
  -- gcd: prime-divisor argument above, with the mod-5 nonresidue lemma for `-2`
  sorry
```

Then the descent theorem should branch as:

```lean
by_cases hBodd : B % 2 = 1
· -- old odd-B factorization using U,V,B
· -- even-B factorization using U/4,V/4,B/2
```

## Answer to the two strategic questions

There is **not** a clean reduction of the even-`B` branch to the literal odd-`B` equation.  After dividing by `4`, the sum identity changes from

```text
(U+V)/2 = 2*r^2 + B^2
```

to

```text
U₁ + V₁ = r^2 + 2*B₁^2.
```

So it is not the same quartic chart with `B₁`.

But there **is** a clean reduction to the same coprime factorization lemma for `5 * B₁^4`, and that is what the descent should use.

Also, I would not try to prove “`gcd(r,B)=1` and `B` even implies no solutions” as a standalone congruence lemma.  It is true only as part of the global descent.  Locally, the `4 ∣ B` subcase survives all the small congruence tests; the correct proof is to normalize the factors by `4` and continue the descent.