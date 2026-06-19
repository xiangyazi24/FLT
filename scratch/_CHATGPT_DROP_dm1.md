# `rat_den_one_of_curve`

Target:

```lean
theorem rat_den_one_of_curve
    (u w : ℚ) (hE : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  ...
```

## Main conclusion from the proposed denominator-clearing argument

Let

```lean
p : ℤ := u.num
q : ℕ := u.den
```

with `q > 0` and `Nat.Coprime p.natAbs q`.  From `hE`, after rewriting
`u = (p : ℚ) / (q : ℚ)` and multiplying by `(q : ℚ) ^ 3`, the useful cleared
identity is

```lean
w ^ 2 * (q : ℚ) ^ 3 =
  (p : ℚ) * ((p : ℚ) ^ 2 + (p : ℚ) * (q : ℚ) - (q : ℚ) ^ 2)
```

Equivalently, if `w = a / b` in lowest terms, this becomes the integer identity

```text
a^2 * q^3 = b^2 * p * (p^2 + p*q - q^2).        (1)
```

For any prime `ℓ ∣ q`, the right-hand integer factor

```text
P := p * (p^2 + p*q - q^2)
```

is not divisible by `ℓ`:

* `ℓ ∤ p`, because `gcd(|p|, q) = 1`;
* `p^2 + p*q - q^2 ≡ p^2 [MOD ℓ]`, so `ℓ ∤ p^2 + p*q - q^2`.

Taking `ℓ`-adic exponents in (1) gives

```text
2 * vℓ(a) + 3 * vℓ(q) = 2 * vℓ(b).
```

Since `gcd(|a|, b) = 1` and `vℓ(q) > 0`, this forces `vℓ(a) = 0` and

```text
3 * vℓ(q) = 2 * vℓ(b).
```

Therefore `vℓ(q)` is even.  So the formal local lemma obtained from this
argument is:

```lean
/-- First local denominator conclusion: every prime exponent in `u.den` is even. -/
lemma den_is_square_of_curve
    (u w : ℚ) (hE : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    ∃ s : ℕ, u.den = s ^ 2 := by
  -- Use `Rat.num`, `Rat.den`, `Rat.reduced`, and `Nat.factorization`.
  -- For every prime ℓ with ℓ ∣ u.den, apply `Nat.factorization` to (1):
  --   2 * vp(a.natAbs) + 3 * vp(q) = 2 * vp(b)
  -- `omega` then gives `Even (vp q)`.
  -- Finish using the characterization of natural squares by even
  -- factorization exponents.
  sorry
```

This is the point where the tempting direct proof breaks: this does **not**
give `q = 1`.  It only gives `q = s^2` and, similarly, `w.den = s^3` after
checking that `w.den` has no prime factors outside `q`.

## Reduced integer equation after the local step

Writing

```text
u = p / s^2,     w = a / s^3,
```

with `gcd(|p|, s) = 1`, the curve equation reduces to

```text
a^2 = p * (p^2 + p*s^2 - s^4).                  (2)
```

The two factors on the right are coprime:

```text
gcd(p, p^2 + p*s^2 - s^4) = 1,
```

because the gcd divides `s^4`, and `gcd(p, s) = 1`.  Hence each factor has the
same squareclass.  Thus `p = d*r^2`, where `d = ±1`, and the equation becomes
one of the two quartic covers

```text
v^2 =  r^4 + r^2 - 1        -- d = 1
v^2 = -r^4 + r^2 + 1        -- d = -1.
```

So the clean Lean split should be:

```lean
lemma den_is_square_of_curve
    (u w : ℚ) (hE : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    ∃ s : ℕ, u.den = s ^ 2 := by
  sorry

lemma cover_one_den_one
    (r v : ℚ) (h : v ^ 2 = r ^ 4 + r ^ 2 - 1) :
    r.den = 1 := by
  sorry

lemma cover_neg_one_den_one
    (r v : ℚ) (h : v ^ 2 = -r ^ 4 + r ^ 2 + 1) :
    r.den = 1 := by
  sorry

theorem rat_den_one_of_curve
    (u w : ℚ) (hE : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  -- 1. Use `den_is_square_of_curve` to write `u.den = s^2`.
  -- 2. Clear denominators completely to get (2).
  -- 3. Use coprimality of the two factors in (2) to get squareclass `d = ±1`.
  -- 4. Convert to one of the two cover equations.
  -- 5. Apply `cover_one_den_one` or `cover_neg_one_den_one`.
  sorry
```

## Why `cover_no_solution_of_prime_dvd` does not directly apply

The lemma for

```text
d * v^2 = d^2 * r^4 + d * r^2 - 1
```

rules out a prime divisor of the squarefree parameter `d`, because modulo such a
prime the right-hand side is `-1`.  In the original denominator equation,
setting `d = q` does not produce that shape: primes dividing `q` can be absorbed
by the denominator of `w`.  The exact exponent equation is

```text
2 * vℓ(w) + 3 * vℓ(q) = 0,
```

which is consistent whenever `vℓ(q)` is even.  Therefore the requested
`False` from just the first cleared equation and `gcd(|p|, q) = 1` is not the
right Lean goal.  The right local goal is square denominator, followed by the
quartic-cover descent above.
