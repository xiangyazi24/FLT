# ChatGPT Drop File (dm2)

## Task

Prove the denominator quartics:

```lean
theorem no_denominator_quartic (s q t : ℤ) (hq : 2 ≤ q) (hcop : Int.gcd s q = 1) :
    t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4 → False
```

and

```lean
theorem no_denominator_quartic_neg (s q t : ℤ) (hq : 2 ≤ q) (hcop : Int.gcd s q = 1) :
    t ^ 2 = -s ^ 4 + s ^ 2 * q ^ 2 + q ^ 4 → False
```

This is hard.  I do not think the `t² + q⁴ = s²(s²+q²)` line is the right formal proof route: it does not give a coprime product of squares directly, because the left side is a sum of two fourth/square terms.  The better route is the Pellian factorization

```text
(2*s² + q²)² - (2*t)² = 5*q⁴.
```

That factorization gives the infinite descent.

## First reduction: the negative theorem follows from the positive theorem

The negative equation is the positive equation with `s` and `q` swapped:

```text
t² = -s⁴ + s²*q² + q⁴
   = q⁴ + q²*s² - s⁴.
```

So if `|s| ≥ 2`, then `no_denominator_quartic q |s| t` kills it.

The only remaining cases are `s = 0, ±1`:

* `s = 0` contradicts `Int.gcd s q = 1` and `2 ≤ q`, because `gcd(0,q)=q`.
* `s = ±1` gives

```text
t² = q⁴ + q² - 1.
```

For `q ≥ 2`, this lies strictly between consecutive squares:

```text
(q²)² < q⁴ + q² - 1 < (q² + 1)².
```

Thus the negative theorem should be proved only after the positive theorem, by a short wrapper.  The real hard theorem is the positive one.

## Correct hard core: positive quartic by infinite descent

Assume a primitive positive solution:

```text
t² = s⁴ + s²*q² - q⁴,
q ≥ 2,
gcd(s,q)=1.
```

First prove the elementary gcd lemma:

```text
gcd(t,q)=1.
```

Indeed, if a prime `p` divides both `t` and `q`, then reducing the equation modulo `p` gives

```text
0 = s⁴ mod p,
```

so `p ∣ s`, contradicting `gcd(s,q)=1`.

Now define

```text
U = 2*s² + q²,
A = U - 2*t,
B = U + 2*t.
```

Then

```text
A*B = 5*q⁴,
A+B = 4*s² + 2*q².
```

Both `A` and `B` are positive: the product is positive and the sum is positive.

This is the key place where the proof should branch by parity of `q`.

## Odd denominator branch

If `q` is odd, then the mod-4 obstruction first forces `s` odd.  If `s` were even, then

```text
t² = 0 + 0 - 1 = 3 mod 4,
```

impossible.

So `s,q,t` are all odd.  Hence `A` and `B` are odd.  Also `gcd(A,B)=1`: any odd prime dividing both `A` and `B` divides both their sum and difference, hence divides `q` and `t`, contradicting `gcd(t,q)=1`; the prime `2` does not divide either factor.

Since

```text
A*B = 5*q⁴
```

and the factors are coprime, after possibly replacing `t` by `-t` so that `A ≤ B`, there are two cases:

```text
A = m⁴,     B = 5*n⁴,    q = m*n,
```

or

```text
A = 5*m⁴,   B = n⁴,      q = m*n.
```

Consider the first case.  From `A+B = 4*s² + 2*q²`, we get

```text
m⁴ + 5*n⁴ = 4*s² + 2*m²*n²,
```

hence

```text
4*s² = (m² - n²)² + 4*n⁴.
```

Since `m,n` are odd, this becomes

```text
s² = ((m² - n²)/2)² + n⁴.
```

So we have a primitive Pythagorean triple

```text
((m² - n²)/2)² + (n²)² = s².
```

Parameterizing this primitive triple gives coprime positive integers `a,b` with

```text
n = a*b,
```

and

```text
m² = b⁴ + a²*b² - a⁴.
```

Therefore `(b, a, m)` is a new solution of the same positive denominator quartic:

```text
m² = b⁴ + b²*a² - a⁴.
```

The new denominator is `a`, and `a < q = m*n`, except for the base case `a = 1`.  If `a = 1`, then

```text
m² = b⁴ + b² - 1,
```

which is the already-proved `d = 1` squeeze from `scratch/Descent20a4.lean` after setting `u = b²`.  That forces `b² = 1`, hence `q = 1`, contradiction.

The second case `A = 5*m⁴`, `B = n⁴` is symmetric and gives the same descent.

This is the main infinite descent proof for odd `q`.

## Even denominator branch

If `q` is even, then `s` is odd.  Modulo `16`, if `q ≡ 2 mod 4`, then

```text
s⁴ + s²*q² - q⁴ ≡ 1 + 4 - 0 = 5 mod 16,
```

which is not a square.  Therefore any even-denominator solution must have

```text
4 ∣ q.
```

Now `t` is odd and both `A` and `B` are divisible by `4`.  Write

```text
A = 4*A₁,
B = 4*B₁,
q = 2*r.
```

Then

```text
A₁*B₁ = 5*r⁴,
A₁+B₁ = s² + 2*r².
```

The same gcd argument shows

```text
gcd(A₁,B₁)=1.
```

Thus, again after ordering the factors, either

```text
A₁ = m⁴,     B₁ = 5*n⁴,    r = m*n,
```

or

```text
A₁ = 5*m⁴,   B₁ = n⁴,      r = m*n.
```

In the first case,

```text
m⁴ + 5*n⁴ = s² + 2*m²*n²,
```

so

```text
s² = (m² - n²)² + (2*n²)².
```

This is again a primitive Pythagorean triple.  Parameterization gives coprime positive integers `a,b` with

```text
n = a*b,
```

and

```text
m² = b⁴ + a²*b² - a⁴.
```

So we again get a smaller positive-quartic solution `(b,a,m)`.  The new denominator `a` is smaller than the old denominator `q = 2*m*n`.  The base case `a = 1` is killed by the `d = 1` squeeze.

Thus the even branch also descends.

## Minimal Lean architecture

I would not try to prove the whole theorem in one block.  The manageable decomposition is:

```lean
-- 1. gcd transport from the original quartic
lemma denom_quartic_gcd_t_q
    (s q t : ℤ) (hcop : Int.gcd s q = 1)
    (h : t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4) :
    Int.gcd t q = 1 := ...

-- 2. Pellian factorization
lemma denom_quartic_factorization
    (s q t : ℤ)
    (h : t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4) :
    (2 * s ^ 2 + q ^ 2 - 2 * t) *
      (2 * s ^ 2 + q ^ 2 + 2 * t) = 5 * q ^ 4 := by
  nlinarith

-- 3. Positivity of the two factors
lemma denom_quartic_factors_pos ... :
    0 < 2*s^2 + q^2 - 2*t ∧ 0 < 2*s^2 + q^2 + 2*t := ...

-- 4. Odd-q coprime-factor classification
lemma denom_quartic_odd_factor_fourth_powers ... :
    ∃ m n : ℤ,
      q = m*n ∧
      ((A = m^4 ∧ B = 5*n^4) ∨ (A = 5*m^4 ∧ B = n^4)) := ...

-- 5. Even-q normalized factor classification
lemma denom_quartic_even_factor_fourth_powers ... :
    ∃ m n : ℤ,
      q = 2*m*n ∧
      ((A/4 = m^4 ∧ B/4 = 5*n^4) ∨ (A/4 = 5*m^4 ∧ B/4 = n^4)) := ...

-- 6. Pythagorean square-leg descent
lemma pythagorean_square_leg_descent_odd_case ... :
    ∃ a b : ℤ,
      1 ≤ a ∧
      a < q.natAbs ∧
      m ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 := ...

-- 7. Strong induction on q.natAbs
```

The Pythagorean-square-leg lemma is probably the largest local formalization step.  It is standard Fermat descent material: a primitive Pythagorean triple with a square leg forces a smaller solution of the same quartic.

## Useful theorem split

The final proof should be structured as:

```lean
theorem no_denominator_quartic_pos_by_descent :
    ∀ n : ℕ, ∀ s q t : ℤ,
      q.natAbs ≤ n →
      2 ≤ q →
      Int.gcd s q = 1 →
      t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4 →
      False := by
  intro n
  induction n with
  | zero => ...
  | succ n ih =>
      -- factorization, parity branch, produce smaller (s',q',t')
      -- with q'.natAbs ≤ n, then exact ih s' q' t' ...
```

Then expose the requested theorem as:

```lean
theorem no_denominator_quartic (s q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd s q = 1) :
    t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4 → False := by
  intro h
  exact no_denominator_quartic_pos_by_descent q.natAbs s q t le_rfl hq hcop h
```

For the negative theorem:

```lean
theorem no_denominator_quartic_neg (s q t : ℤ) (hq : 2 ≤ q)
    (hcop : Int.gcd s q = 1) :
    t ^ 2 = -s ^ 4 + s ^ 2 * q ^ 2 + q ^ 4 → False := by
  -- If |s| ≥ 2, swap s and q and use no_denominator_quartic.
  -- If s = 0, contradict gcd.
  -- If s = ±1, squeeze q⁴ < t² < (q²+1)².
```

## Why this is better than the `t²+q⁴` product idea

The identity

```text
t² + q⁴ = s²(s²+q²)
```

is true, and `gcd(s², s²+q²)=1`, but it does not make the left side a square product.  It is a sum of a square and a fourth power.  So `Int.sq_of_isCoprime` does not apply directly.

The factorization

```text
(2*s² + q² - 2*t)(2*s² + q² + 2*t)=5*q⁴
```

is the right one because its right side is a constant times a fourth power.  After proving the two factors are coprime, each factor must be a fourth power up to the single factor `5`, and that is exactly what opens the Pythagorean descent.

## Bottom line

I do not recommend trying to prove the two denominator quartics independently.

Prove only the positive quartic by strong infinite descent using

```text
(2*s²+q²-2t)(2*s²+q²+2t)=5*q⁴.
```

Then derive the negative theorem by swapping `s` and `q` plus the small cases `s=0, ±1`.

The decisive missing formal lemma is the primitive Pythagorean square-leg descent.  Once that lemma exists, the rest of the positive-quartic proof is a finite sequence of gcd, factorization, parity, and strong-induction steps.
