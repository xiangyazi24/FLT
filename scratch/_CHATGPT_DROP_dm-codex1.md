# Q2736 (dm-codex1): corrected Eisenstein half-factor split

We work with primitive positive Eisenstein triples

```text
Z^2 = X^2 - X*Y + Y^2,    0<X, 0<Y, 0<Z,    IsCoprime X Y.
```

Define

```text
U = 2*Z - (2*X - Y),
V = 2*Z + (2*X - Y).
```

Then

```text
U*V = 3*Y^2,
U+V = 4*Z,
V-U = 2*(2*X-Y),
4*Z^2 = (2*X-Y)^2 + 3*Y^2.
```

The final split

```text
raw:      U = 3*r^2, V = s^2,
divided:  U = r^2,   V = 3*s^2
```

is correct for the original `U,V`. The error to avoid is applying a coprime product-square lemma directly to `U,V`. They are not always coprime: `(X,Y,Z)=(5,8,7)` gives `U=12`, `V=16`, `gcd(U,V)=4`, but still `U=3*2^2`, `V=4^2`.

## 1. Exact gcd statement

For primitive positive triples:

```text
gcd(|U|,|V|) = 1  if Y is odd,
gcd(|U|,|V|) = 4  if Y is even.
```

Equivalently:

```text
gcd(|U|,|V|) = if (2 : ℤ) ∣ Y then 4 else 1.
```

So `v_2(gcd(U,V))` is `0` or `2`, and no odd prime divides both half factors. In particular, a common factor `3` is impossible.

Proof. Let an odd prime `p` divide both `U` and `V`. Then `p ∣ U+V = 4Z` and `p ∣ V-U = 2*(2X-Y)`, hence `p ∣ Z` and `p ∣ 2X-Y`. Also `p^2 ∣ U*V = 3Y^2`. If `p≠3`, this gives `p∣Y`, hence `p∣X`, contradiction. If `p=3`, then `9∣3Y^2`, so `3∣Y`; together with `3∣2X-Y`, this gives `3∣X`, contradiction. Thus no odd common prime exists.

For the 2-part, `U≡Y` and `V≡Y` mod `2`. If `Y` is odd, both are odd, so the gcd is `1`. If `Y` is even, coprimality gives `X` odd, the Eisenstein equation gives `Z` odd, and reducing mod `4` rules out `Y≡2`; hence `4∣Y`. Then `4∣U,V`. They cannot both be divisible by `8`, since that would make `8∣U+V=4Z`, forcing `Z` even. Therefore the gcd is exactly `4`.

## 2. Correct square split

Use this normalized coprime lemma, not a lemma applied directly to `U,V`:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-- Coprime product equal to `3` times a square. -/
theorem Nat.coprime_mul_eq_three_sq_split
    {u v y : ℕ}
    (huv : Nat.Coprime u v)
    (h : u * v = 3 * y ^ 2) :
    (∃ r s : ℕ, u = 3 * r ^ 2 ∧ v = s ^ 2 ∧ y = r * s) ∨
    (∃ r s : ℕ, u = r ^ 2 ∧ v = 3 * s ^ 2 ∧ y = r * s) := by
  -- Prove by `Nat.factorization`: all primes except `3` occur to even
  -- exponent; the odd exponent of `3` lies wholly in one coprime factor.
  sorry
```

Then the half-factor theorem should be:

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

def eisensteinHalfU (X Y Z : ℤ) : ℤ :=
  2 * Z - (2 * X - Y)

def eisensteinHalfV (X Y Z : ℤ) : ℤ :=
  2 * Z + (2 * X - Y)

/-- Correct split for the original integer half factors. In the gcd-4 case the
witnesses `r,s` are even. -/
theorem eisenstein_halfFactors_square_split
    {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : IsCoprime X Y)
    (htri : Z ^ 2 = X ^ 2 - X * Y + Y ^ 2) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧
      Y = r * s ∧
      (2 : ℤ) ∣ r + s ∧
      ((eisensteinHalfU X Y Z = 3 * r ^ 2 ∧
        eisensteinHalfV X Y Z = s ^ 2) ∨
       (eisensteinHalfU X Y Z = r ^ 2 ∧
        eisensteinHalfV X Y Z = 3 * s ^ 2)) := by
  -- 1. Prove positivity and product `U*V=3*Y^2`.
  -- 2. Use `gcd(|U|,|V|)=1∨4`.
  -- 3. If gcd=1, apply `Nat.coprime_mul_eq_three_sq_split` to `U,V,Y`.
  -- 4. If gcd=4, write `U=4u`, `V=4v`, `Y=4y`; then `u*v=3*y^2`
  --    and `Nat.Coprime u v`. Apply the coprime lemma and double witnesses:
  --    `r=2*r0`, `s=2*s0`.
  -- 5. Parity follows because `U` and `V` have the same parity.
  sorry
```

Thus the split itself is not false. The counterexample `(5,8,7)` only refutes the coprime shortcut.

## 3. Parity for `m`

The theorem should return `(2 : ℤ) ∣ r+s`. Since

```text
U-V = -2*(2X-Y),
```

`U` and `V` have the same parity. In the raw case `U=3*r^2`, `V=s^2`; in the divided case `U=r^2`, `V=3*s^2`. Modulo `2`, `3≡1` and squaring preserves parity, so `r` and `s` have the same parity. Hence `2∣r+s`. Also

```text
r + 3*s = (r+s) + 2*s,
```

so `2∣r+3*s`, which is the numerator needed in the divided case.

Useful Lean lemma:

```lean
theorem even_r_add_three_mul_s_of_even_r_add_s {r s : ℤ}
    (h : (2 : ℤ) ∣ r + s) :
    (2 : ℤ) ∣ r + 3 * s := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + s, ?_⟩
  calc
    r + 3 * s = (r + s) + 2 * s := by ring
    _ = 2 * k + 2 * s := by rw [hk]
    _ = 2 * (k + s) := by ring
```

## 4. Constructing parameters and proving coprimality

### Raw case

Assume

```text
U=3*r^2, V=s^2, Y=r*s, 0<r, 0<s, 2∣r+s.
```

Choose `m` with `2*m=r+s`, and set `n=r`. Then

```text
2*m-n = s,
m-n = (s-r)/2,
m+n = (s+3*r)/2.
```

The identities are:

```text
4*X = s^2 - 3*r^2 + 2*r*s = (s-r)*(s+3*r),
X = (m-n)*(m+n),
Y = n*(2*m-n),
4*Z = 3*r^2+s^2,
Z = m^2 - m*n + n^2.
```

The inequality `n<m` follows from `0<X` and

```text
4*X = (s-r)*(s+3*r),  with s+3*r>0,
```

so `s-r>0`.

### Divided case

Assume

```text
U=r^2, V=3*s^2, Y=r*s, 0<r, 0<s, 2∣r+s.
```

Choose `m` with `2*m=r+3*s`, and set `n=r`. Then

```text
2*m-n = 3*s,
m-n = (3*s-r)/2,
m+n = 3*(r+s)/2,
```

so `3∣m+n`. The identities are:

```text
4*X = 3*s^2 - r^2 + 2*r*s = (3*s-r)*(r+s),
3*X = (m-n)*(m+n),
3*Y = n*(2*m-n),
4*Z = r^2+3*s^2,
3*Z = m^2 - m*n + n^2.
```

The inequality `n<m` follows from `0<X` and

```text
4*X = (3*s-r)*(r+s),  with r+s>0,
```

so `r<3*s`.

### Coprimality of `m,n`

Prove `IsCoprime m n` from primitive `IsCoprime X Y` after the parameter identities are known.

Raw helper:

```lean
theorem raw_param_coprime_mn_of_coprime_XY
    {X Y m n : ℤ}
    (hcopXY : IsCoprime X Y)
    (hX : X = (m - n) * (m + n))
    (hY : Y = n * (2 * m - n)) :
    IsCoprime m n := by
  -- If a prime divides both `m` and `n`, it divides `m-n`, `m+n`, `n`,
  -- and `2*m-n`; hence it divides both `X` and `Y`, contradiction.
  sorry
```

Divided helper:

```lean
theorem divided_param_coprime_mn_of_coprime_XY
    {X Y m n : ℤ}
    (hcopXY : IsCoprime X Y)
    (hX : 3 * X = (m - n) * (m + n))
    (hY : 3 * Y = n * (2 * m - n)) :
    IsCoprime m n := by
  -- If a prime `p` divides both `m` and `n`, it divides both RHSs.
  -- For `p≠3`, Euclid gives `p∣X` and `p∣Y`, contradiction.
  -- For `p=3`, every factor on both RHSs is divisible by `3`, so both RHSs
  -- are divisible by `9`; hence `3∣X` and `3∣Y`, contradiction.
  sorry
```

This is where the divided-by-3 issue belongs. Do not use `p∣3*X → p∣X` without first splitting off the case `p=3`.

## 5. Final implementation DAG

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

-- Algebra/positivity
#check eisensteinHalfU
#check eisensteinHalfV
#check eisenstein_halfFactors_square_split

-- Gcd theorem to prove before the split
-- target shape:
-- Nat.gcd (Int.natAbs (eisensteinHalfU X Y Z))
--         (Int.natAbs (eisensteinHalfV X Y Z)) =
--   if (2 : ℤ) ∣ Y then 4 else 1

-- Coprime normalized square split
#check Nat.coprime_mul_eq_three_sq_split

-- Parameter construction helpers
#check raw_param_coprime_mn_of_coprime_XY
#check divided_param_coprime_mn_of_coprime_XY
```

Final audit answer:

* `gcd(U,V)` is exactly `1` or `4`.
* A common factor `3` is impossible.
* The original raw/divided split is correct, but the proof must normalize the `gcd=4` case.
* Parity follows because `r,s` have the same parity; this gives both `2∣r+s` and `2∣r+3*s`.
* `IsCoprime m n` should be proved from the final raw/divided parameter identities and `IsCoprime X Y`, with a separate `p=3` argument in the divided case.
