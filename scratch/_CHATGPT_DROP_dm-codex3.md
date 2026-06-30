# Q2575: constructing `PrimitiveCenteredFourSqAP` from `EulerSquarePair`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Target namespace: `MazurProof.RationalPointsN12.EulerSquarePair`.

This note assumes the local file already has the names mentioned in the prompt:

```lean
centerX E = E.B * E.C
stepN E = E.A * E.D
fm6 E = centerX E - 6 * stepN E
fm2 E = centerX E - 2 * stepN E
fp2 E = centerX E + 2 * stepN E
fp6 E = centerX E + 6 * stepN E
```

The key point is that the `PrimitiveCenteredFourSqAP` structure wants the six root gcd fields, so the factor level must be pairwise coprime among all four factors, not just the two product-pairs.

## 0. Warning about positivity/sign choices

The construction is safe only after proving the four factors are positive:

```text
0 < fm6 E, 0 < fm2 E, 0 < fp2 E, 0 < fp6 E.
```

The product identities alone do not give square roots of individual factors unless the factors are nonnegative/positive. Once roots exist, their signs do not matter: `Int.gcd` is sign-insensitive and every odd integer, positive or negative, satisfies `p % 2 = 1` for `Int.emod`.

The outer identity

```text
fm6 E * fp6 E = (E.D^2 - 8*E.A^2)^2
```

is still usable even if `E.D^2 - 8*E.A^2` is negative; the right side is a square. Only factor positivity matters for extraction.

## 1. Minimal pairwise factor-coprimality requirements

Let `X = centerX E` and `N = stepN E`. The four factors are

```text
F_{-6}=X-6N, F_{-2}=X-2N, F_2=X+2N, F_6=X+6N.
```

To get the six root gcd fields, the minimal factor-level targets are exactly these six pairwise coprimalities:

```lean
-- Suggested theorem headers; bodies should use the proof described below.
--
-- theorem fm6_coprime_fm2 (E : EulerSquarePair) :
--     IsCoprime (fm6 E) (fm2 E)
--
-- theorem fm6_coprime_fp2 (E : EulerSquarePair) :
--     IsCoprime (fm6 E) (fp2 E)
--
-- theorem fm6_coprime_fp6 (E : EulerSquarePair) :
--     IsCoprime (fm6 E) (fp6 E)
--
-- theorem fm2_coprime_fp2 (E : EulerSquarePair) :
--     IsCoprime (fm2 E) (fp2 E)
--
-- theorem fm2_coprime_fp6 (E : EulerSquarePair) :
--     IsCoprime (fm2 E) (fp6 E)
--
-- theorem fp2_coprime_fp6 (E : EulerSquarePair) :
--     IsCoprime (fp2 E) (fp6 E)
```

If `fm2_coprime_fp2` and `fm6_coprime_fp6` are already checked locally, the new factor-coprimality work is only the four remaining cross/adjacent pairs:

```text
fm6/fm2, fm6/fp2, fm2/fp6, fp2/fp6.
```

For a robust local API, I recommend adding generic integer lemmas for the five easy pairs and one separate outer pair lemma.

```lean
-- Difference 4N pairs.
-- theorem linear_factor_coprime_diff_four_left
--     {X N : Int} (hXN : IsCoprime X N)
--     (hodd : Odd (X - 6 * N)) :
--     IsCoprime (X - 6 * N) (X - 2 * N)
--
-- theorem linear_factor_coprime_diff_four_middle
--     {X N : Int} (hXN : IsCoprime X N)
--     (hodd : Odd (X - 2 * N)) :
--     IsCoprime (X - 2 * N) (X + 2 * N)
--
-- theorem linear_factor_coprime_diff_four_right
--     {X N : Int} (hXN : IsCoprime X N)
--     (hodd : Odd (X + 2 * N)) :
--     IsCoprime (X + 2 * N) (X + 6 * N)
--
-- Difference 8N pairs.
-- theorem linear_factor_coprime_diff_eight_left
--     {X N : Int} (hXN : IsCoprime X N)
--     (hodd : Odd (X - 6 * N)) :
--     IsCoprime (X - 6 * N) (X + 2 * N)
--
-- theorem linear_factor_coprime_diff_eight_right
--     {X N : Int} (hXN : IsCoprime X N)
--     (hodd : Odd (X - 2 * N)) :
--     IsCoprime (X - 2 * N) (X + 6 * N)
--
-- Difference 12N outer pair. This is the only pair needing the mod-3 input.
-- theorem linear_factor_coprime_diff_twelve_outer
--     {X N : Int} (hXN : IsCoprime X N)
--     (h3X : IsCoprime (3 : Int) X)
--     (hodd : Odd (X - 6 * N)) :
--     IsCoprime (X - 6 * N) (X + 6 * N)
```

### Proof of the generic factor lemmas

For `F_i = X + i*N` and `F_j = X + j*N`, a common prime divisor `l` divides

```text
F_j - F_i = (j-i) * N.
```

Also `l` cannot divide `N`: if `l ∣ N` and `l ∣ F_i`, then `l ∣ X`, contradicting `IsCoprime X N`. Hence Euclid's lemma gives `l ∣ (j-i)`.

For the pairs with differences `4` or `8`, this forces `l = 2`; factor oddness excludes this.

For the outer pair with difference `12`, this forces `l = 2` or `l = 3`; oddness excludes `2`, and `h3X : IsCoprime 3 X` excludes `3`, since `X - 6N ≡ X mod 3`.

Lean implementation advice: if the `IsCoprime` prime-divisor API is inconvenient over `Int`, prove these via `Int.gcd`. Show `Int.gcd F_i F_j` divides `(j-i)*N`, show it is coprime to `N`, then show its only possible prime divisors are `2` and maybe `3`; remove `2` by oddness and remove `3` by `h3X` in the outer case.

A useful local utility statement is:

```lean
-- theorem isCoprime_linear_factor_step
--     {X N k : Int} (hXN : IsCoprime X N) :
--     IsCoprime (X + k * N) N
```

This follows immediately from a Bezout witness for `IsCoprime X N`:

```text
u*X + v*N = 1
=> u*(X+kN) + (v-u*k)*N = 1.
```

## 2. Extracting square roots of the four factors

Use the banked two-factor square extraction twice.

Recommended wrapper:

```lean
-- theorem extract_two_int_square_roots_of_coprime_product_square
--     {f g z : Int}
--     (hf_nonneg : 0 <= f) (hg_nonneg : 0 <= g)
--     (hfg : IsCoprime f g)
--     (hprod : f * g = z ^ 2) :
--     exists u v : Int, f = u ^ 2 /\ g = v ^ 2
```

This is just the local/banked `Int_coprime_mul_eq_sq_of_nonneg` or equivalent wrapper. Apply it as follows:

```text
middle: f = fm2 E, g = fp2 E, z = E.D^2 + 8*E.A^2
outer:  f = fm6 E, g = fp6 E, z = E.D^2 - 8*E.A^2
```

Then rename the roots as

```text
fm6 E = p^2, fm2 E = q^2, fp2 E = r^2, fp6 E = s^2.
```

For the `PrimitiveCenteredFourSqAP` fields, use the symmetric orientation:

```text
hp : p^2 = centerX E - 6*stepN E
hq : q^2 = centerX E - 2*stepN E
hr : r^2 = centerX E + 2*stepN E
hs : s^2 = centerX E + 6*stepN E
```

If extraction returns `factor = root^2`, fill the structure fields with `.symm` after unfolding `fm6`, `fm2`, `fp2`, `fp6`.

## 3. Reusable lemma: factor coprime implies root gcd one

This is the central bridge from factor pairwise coprimality to the six root gcd fields.

```lean
-- theorem Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors
--     {p q f g : Int}
--     (hp : p ^ 2 = f) (hq : q ^ 2 = g)
--     (hfg : IsCoprime f g) :
--     Int.gcd p q = 1
```

Proof plan:

1. Rewrite `hfg` along `hp` and `hq` to get `IsCoprime (p^2) (q^2)`.
2. Prove or use the standard power-removal lemma:

```lean
-- theorem isCoprime_of_sq_sq_isCoprime
--     {p q : Int} (h : IsCoprime (p ^ 2) (q ^ 2)) :
--     IsCoprime p q
```

3. Convert `IsCoprime p q` to `Int.gcd p q = 1` using the local convention already used in the file. If no wrapper exists, add one:

```lean
-- theorem Int.gcd_eq_one_of_isCoprime
--     {p q : Int} (h : IsCoprime p q) :
--     Int.gcd p q = 1
```

Mathlib/API hints: look for existing lemmas around `IsCoprime.pow_left`, `IsCoprime.pow_right`, `isCoprime_iff_gcd_eq_one`, `Int.gcd`, and `Int.natAbs`. If those names drift, the prime-divisor proof is short: a common prime divisor of `p` and `q` divides `p^2` and `q^2`, contradicting `IsCoprime (p^2) (q^2)`.

Then the six structure fields are obtained by applying the bridge to the six factor-coprimality lemmas:

```text
Int.gcd p q = 1  from  IsCoprime (fm6 E) (fm2 E)
Int.gcd p r = 1  from  IsCoprime (fm6 E) (fp2 E)
Int.gcd p s = 1  from  IsCoprime (fm6 E) (fp6 E)
Int.gcd q r = 1  from  IsCoprime (fm2 E) (fp2 E)
Int.gcd q s = 1  from  IsCoprime (fm2 E) (fp6 E)
Int.gcd r s = 1  from  IsCoprime (fp2 E) (fp6 E)
```

## 4. Root oddness and `% 2 = 1`

Use factor oddness plus the square equation.

```lean
-- theorem Int.emod_two_eq_one_of_sq_eq_odd
--     {p f : Int} (hp : p ^ 2 = f) (hfodd : Odd f) :
--     p % 2 = 1
```

Proof plan:

1. Rewrite `hfodd` by `hp` to get `Odd (p^2)`.
2. If `Even p`, then `Even (p^2)`, contradiction.
3. Hence `Odd p`.
4. Convert `Odd p` to `p % 2 = 1`.

Mathlib/API hints: search locally for existing conversions between `Odd`, `Even`, and integer mod. Likely names include variants of `Int.odd_iff`, `Int.even_iff`, or lemmas around `Int.emod_two_eq_zero_or_one`. If API is annoying, prove by cases on `p % 2 = 0` or `p % 2 = 1` using `Int.emod_two_eq_zero_or_one`.

Apply this four times:

```text
p % 2 = 1 from p^2 = fm6 E and Odd (fm6 E)
q % 2 = 1 from q^2 = fm2 E and Odd (fm2 E)
r % 2 = 1 from r^2 = fp2 E and Odd (fp2 E)
s % 2 = 1 from s^2 = fp6 E and Odd (fp6 E)
```

## 5. Constructor skeleton

The final local theorem should be a wrapper around extraction plus the six factor-coprimality lemmas.

```lean
-- theorem EulerSquarePairToPrimitiveCentered_of_factor_square_data :
--     EulerSquarePairToPrimitiveCentered
```

Implementation shape:

```lean
-- intro E
-- let X : Int := centerX E
-- let N : Int := stepN E
--
-- have hNpos : 0 < N := stepN_pos E
--
-- have hmid_prod : fm2 E * fp2 E = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 :=
--   middle_factor_product_square E
-- have hout_prod : fm6 E * fp6 E = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
--   outer_factor_product_square E
--
-- obtain <q, r, hq_factor, hr_factor> :=
--   extract_two_int_square_roots_of_coprime_product_square
--     (le_of_lt (fm2_pos E)) (le_of_lt (fp2_pos E))
--     (fm2_coprime_fp2 E) hmid_prod
--
-- obtain <p, s, hp_factor, hs_factor> :=
--   extract_two_int_square_roots_of_coprime_product_square
--     (le_of_lt (fm6_pos E)) (le_of_lt (fp6_pos E))
--     (fm6_coprime_fp6 E) hout_prod
--
-- have hp : p ^ 2 = X - 6 * N := by
--   -- from hp_factor.symm and definitions of X,N,fm6
-- have hq : q ^ 2 = X - 2 * N := by
--   -- from hq_factor.symm and definitions of X,N,fm2
-- have hr : r ^ 2 = X + 2 * N := by
--   -- from hr_factor.symm and definitions of X,N,fp2
-- have hs : s ^ 2 = X + 6 * N := by
--   -- from hs_factor.symm and definitions of X,N,fp6
--
-- refine <{
--   X := X,
--   N := N,
--   hNpos := hNpos,
--   p := p, q := q, r := r, s := s,
--   hp := hp,
--   hq := hq,
--   hr := hr,
--   hs := hs,
--   hpq := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hp hq (fm6_coprime_fm2 E),
--   hpr := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hp hr (fm6_coprime_fp2 E),
--   hps := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hp hs (fm6_coprime_fp6 E),
--   hqr := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hq hr (fm2_coprime_fp2 E),
--   hqs := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hq hs (fm2_coprime_fp6 E),
--   hrs := Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors hr hs (fp2_coprime_fp6 E),
--   hp_mod := Int.emod_two_eq_one_of_sq_eq_odd hp (fm6_odd E),
--   hq_mod := Int.emod_two_eq_one_of_sq_eq_odd hq (fm2_odd E),
--   hr_mod := Int.emod_two_eq_one_of_sq_eq_odd hr (fp2_odd E),
--   hs_mod := Int.emod_two_eq_one_of_sq_eq_odd hs (fp6_odd E)
-- }, ?_>
--
-- -- final equality T.N = E.A * E.D:
-- -- simp [N, stepN]
```

The field names in the literal structure may differ (`hpq`, `hpr`, etc.); wire the six gcd values in the order required by `PrimitiveCenteredFourSqAP`.

## 6. Dependency DAG

1. Existing/banked Euler data:
   - `stepN_pos`
   - four factor positivity lemmas
   - four factor oddness lemmas
   - `middle_factor_product_square`
   - `outer_factor_product_square`
   - `centerX_coprime_stepN`
   - `three_coprime_centerX`

2. Add generic factor-coprimality utilities:
   - `isCoprime_linear_factor_step`
   - five diff-4/diff-8 factor lemmas using `centerX_coprime_stepN` and oddness
   - one diff-12 outer factor lemma using `centerX_coprime_stepN`, oddness, and `three_coprime_centerX`

3. E-specialized factor-pair lemmas:
   - `fm6_coprime_fm2`
   - `fm6_coprime_fp2`
   - `fm6_coprime_fp6`
   - `fm2_coprime_fp2`
   - `fm2_coprime_fp6`
   - `fp2_coprime_fp6`

4. Square extraction:
   - `extract_two_int_square_roots_of_coprime_product_square`, wrapping the banked coprime-product-square helper.

5. Root utilities:
   - `Int.gcd_eq_one_of_sq_eq_sq_of_isCoprime_factors`
   - `Int.emod_two_eq_one_of_sq_eq_odd`

6. Final wrapper:
   - `EulerSquarePairToPrimitiveCentered_of_factor_square_data : EulerSquarePairToPrimitiveCentered`.

## Bottom line

The construction is:

```text
X := E.B * E.C
N := E.A * E.D
fm6,fm2,fp2,fp6 := X-6N, X-2N, X+2N, X+6N

middle product + coprime => fm2=q^2, fp2=r^2
outer product  + coprime => fm6=p^2, fp6=s^2

all six factor coprimalities => all six Int.gcd root_i root_j = 1
factor oddness + root square equations => p%2=q%2=r%2=s%2=1

T := { X, N, p,q,r,s, ... }
T.N = E.A * E.D by definition of N.
```

The only nontrivial missing piece for the six gcd fields is not root-level algebra; it is proving the four additional factor-pair coprimalities. They are all elementary consequences of `IsCoprime centerX stepN`, oddness, and, for the outer `fm6/fp6` pair only, `three_coprime_centerX`.
