# Q2605: common refinement for `EulerSquarePairDescent`

Target: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`, theorem family `EulerSquarePairDescent`.

## Bottom line

This common-refinement step should **not** be treated as a paper-scale residual. It can be proved cleanly as a local Mathlib-style lemma over `Nat` using `Nat.gcd`. The key current Mathlib API is:

```lean
-- in Mathlib.Data.Nat.GCD.Basic
-- theorem Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
--     {x n m : Nat} (hcop : Nat.Coprime n m) :
--     Nat.gcd x n * Nat.gcd x m = x <-> x ∣ n * m
```

This theorem makes the four-corner decomposition almost direct. A `Nat.factorization` proof is also possible, but it is longer and less ergonomic for this particular target.

Recommended local import if not already available through existing imports:

```lean
import Mathlib.Data.Nat.GCD.Basic
```

If later using the factorization proof route instead, add:

```lean
import Mathlib.Data.Nat.Factorization.Basic
```

## 1. Minimal Nat theorem statement

Use the product equality directly; the common integer `A` is not needed in the core theorem. Positivity avoids all zero corner pathologies.

```lean
-- Suggested local theorem statement.
-- theorem two_coprime_factorizations_refine_nat
--     {U V Up Vp : Nat}
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hEq : U * V = Up * Vp)
--     (hUV : Nat.Coprime U V)
--     (hUpVp : Nat.Coprime Up Vp) :
--     exists a b c d : Nat,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = a * b /\ V = c * d /\
--       Up = a * c /\ Vp = b * d /\
--       Nat.Coprime a b /\ Nat.Coprime a c /\ Nat.Coprime a d /\
--       Nat.Coprime b c /\ Nat.Coprime b d /\ Nat.Coprime c d
```

If the surrounding proof has `A = U*V` and `A = Up*Vp`, make a thin wrapper:

```lean
-- Suggested wrapper.
-- theorem two_coprime_factorizations_refine_nat_of_common_value
--     {A U V Up Vp : Nat}
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hUVeq : A = U * V) (hUpVpeq : A = Up * Vp)
--     (hUV : Nat.Coprime U V)
--     (hUpVp : Nat.Coprime Up Vp) :
--     exists a b c d : Nat,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = a * b /\ V = c * d /\
--       Up = a * c /\ Vp = b * d /\
--       Nat.Coprime a b /\ Nat.Coprime a c /\ Nat.Coprime a d /\
--       Nat.Coprime b c /\ Nat.Coprime b d /\ Nat.Coprime c d
```

The wrapper just sets `hEq : U*V = Up*Vp` by rewriting with `hUVeq` and `hUpVpeq`.

## 2. GCD proof strategy

Define the four corners by gcds:

```text
a := Nat.gcd U Up
b := Nat.gcd U Vp
c := Nat.gcd V Up
d := Nat.gcd V Vp
```

Then prove the four product equations with `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`.

### `U = a*b`

Use `hUpVp : Nat.Coprime Up Vp` and the fact that `U ∣ Up*Vp`, which follows from `hEq`:

```text
U ∣ Up*Vp, since Up*Vp = U*V.
Nat.gcd U Up * Nat.gcd U Vp = U.
```

This is exactly:

```lean
-- have hU_dvd : U ∣ Up * Vp := by
--   exact ⟨V, hEq.symm⟩
-- have hU_corner : Nat.gcd U Up * Nat.gcd U Vp = U :=
--   (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUpVp).2 hU_dvd
```

Then rewrite by the definitions of `a,b` and take `.symm` if the target is `U = a*b`.

### `V = c*d`

Similarly, `V ∣ Up*Vp` because `Up*Vp = U*V`, and the same coprimality `hUpVp` gives:

```text
Nat.gcd V Up * Nat.gcd V Vp = V.
```

### `Up = a*c`

Use `hUV : Nat.Coprime U V` and `Up ∣ U*V`, from `hEq`:

```text
Nat.gcd Up U * Nat.gcd Up V = Up.
```

Then commute gcds:

```text
Nat.gcd Up U = Nat.gcd U Up = a,
Nat.gcd Up V = Nat.gcd V Up = c.
```

Expected simp/rw helpers: `Nat.gcd_comm`, `mul_comm`, `mul_left_comm`, `mul_assoc`.

### `Vp = b*d`

Use `hUV : Nat.Coprime U V` and `Vp ∣ U*V`, from `hEq`:

```text
Nat.gcd Vp U * Nat.gcd Vp V = Vp.
```

Commute gcds to obtain `b*d`.

### Positivity of the corners

Use `Nat.gcd_pos_of_pos_left` or `Nat.gcd_pos_of_pos_right`. For example:

```lean
-- have ha_pos : 0 < Nat.gcd U Up := Nat.gcd_pos_of_pos_left Up hUpos
-- have hb_pos : 0 < Nat.gcd U Vp := Nat.gcd_pos_of_pos_left Vp hUpos
-- have hc_pos : 0 < Nat.gcd V Up := Nat.gcd_pos_of_pos_left Up hVpos
-- have hd_pos : 0 < Nat.gcd V Vp := Nat.gcd_pos_of_pos_left Vp hVpos
```

## 3. Pairwise coprimalities among the corners

The Nat theorem can return all six pairwise coprimalities essentially for free.

Use divisibility of the gcd corners and `Nat.Coprime.of_dvd` / `.of_dvd_left` / `.of_dvd_right`.

The divisibilities are:

```text
a | U and a | Up
b | U and b | Vp
c | V and c | Up
d | V and d | Vp
```

Then derive:

```text
Coprime a b  from hUpVp, since a | Up and b | Vp.
Coprime a c  from hUV,   since a | U  and c | V.
Coprime a d  from hUV,   since a | U  and d | V.
Coprime b c  from hUV,   since b | U  and c | V.
Coprime b d  from hUV,   since b | U  and d | V.
Coprime c d  from hUpVp, since c | Up and d | Vp.
```

For the later Euler descent, the two most important outputs are:

```text
Coprime b c   -- needed for square-factor balance from b^2*M = c^2*N.
Coprime a d   -- needed for coprimality of cofactors 4*a^2+d^2 and 16*a^2+d^2,
                  and for the smaller Euler pair field hADcop.
```

The other four pairwise coprimalities are cheap and useful for cleanup/parity wrappers, so include them in the theorem output.

## 4. Factorization proof route, if preferred

A `Nat.factorization` proof is standard but longer. The shape is:

```text
For every prime p,
  v_p(U) + v_p(V) = v_p(Up) + v_p(Vp).
Since gcd(U,V)=1, at most one of v_p(U),v_p(V) is nonzero.
Since gcd(Up,Vp)=1, at most one of v_p(Up),v_p(Vp) is nonzero.
Therefore the exponent mass for p lies in exactly one of the four intersections:
  U∩Up, U∩Vp, V∩Up, V∩Vp.
```

Relevant APIs if you go this way:

```lean
-- Nat.factorization_mul
-- Nat.factorization_le_iff_dvd
-- Nat.factorization_prime_le_iff_dvd
-- Nat.factorization_eq_zero_iff
-- Nat.Coprime
-- Finsupp.ext
```

I recommend the gcd route instead. It is shorter and avoids a pointwise `Finsupp` proof.

## 5. Positive `Int` wrapper

The Euler parameters live in `Int`. Do not prove the refinement primarily over `Int`; lift positive variables to `Nat`, apply the Nat theorem, then cast back.

Recommended positive-Int wrapper:

```lean
-- Suggested local wrapper.
-- theorem two_coprime_factorizations_refine_int_pos
--     {U V Up Vp : Int}
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hEq : U * V = Up * Vp)
--     (hUV : IsCoprime U V)
--     (hUpVp : IsCoprime Up Vp) :
--     exists a b c d : Int,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = a * b /\ V = c * d /\
--       Up = a * c /\ Vp = b * d /\
--       IsCoprime a b /\ IsCoprime a c /\ IsCoprime a d /\
--       IsCoprime b c /\ IsCoprime b d /\ IsCoprime c d
```

Implementation notes:

1. Set

```text
u := U.toNat, v := V.toNat, up := Up.toNat, vp := Vp.toNat.
```

2. Use positivity to rewrite casts:

```text
(u : Int) = U, etc.
```

Expected API: `Int.toNat_of_nonneg` with `le_of_lt hUpos`.

3. Convert `hEq` to a Nat equality. If `exact_mod_cast` sees the `toNat` rewrites, it usually closes; otherwise prove by casting both sides to `Int` and using the positivity rewrites.

4. Convert `IsCoprime U V` and `IsCoprime Up Vp` to `Nat.Coprime u v` and `Nat.Coprime up vp`. If the current file does not already have this, isolate tiny wrappers:

```lean
-- theorem nat_coprime_of_int_isCoprime_pos
--     {x y : Int} (hx : 0 < x) (hy : 0 < y) (hxy : IsCoprime x y) :
--     Nat.Coprime x.toNat y.toNat
--
-- theorem int_isCoprime_of_nat_coprime_pos
--     {x y : Int} (hx : 0 < x) (hy : 0 < y)
--     (hxy : Nat.Coprime x.toNat y.toNat) :
--     IsCoprime x y
```

5. Apply the Nat theorem and cast witnesses back with `a := (an : Int)`, etc.

This wrapper is routine but may be more annoying than the Nat core because of `Int.toNat`/`IsCoprime` conversion. Keep it separate.

## 6. Parity-specialized wrapper for the Euler route

After Pythagorean parametrization, the Euler route has:

```text
U, Up even;
V, Vp odd;
A = U*V = Up*Vp.
```

The desired refinement is:

```text
U  = 2*a*b,
V  = c*d,
Up = 2*a*c,
Vp = b*d.
```

Prove it by applying the positive-Int wrapper first, giving temporary corners

```text
U  = alpha*beta,
V  = gamma*delta,
Up = alpha*gamma,
Vp = beta*delta.
```

Then:

1. `V = gamma*delta` and `Odd V` imply `Odd gamma` and `Odd delta`.
2. `Vp = beta*delta` and `Odd Vp` imply `Odd beta`.
3. `U = alpha*beta`, `Even U`, and `Odd beta` imply `Even alpha`.
4. Write `alpha = 2*a`. Since `alpha > 0` and even, get `0 < a`.
5. Set `b := beta`, `c := gamma`, `d := delta`.

Suggested statement:

```lean
-- Suggested Euler-facing theorem.
-- theorem two_coprime_factorizations_refine_even_even_odd_odd_int_pos
--     {U V Up Vp : Int}
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hEq : U * V = Up * Vp)
--     (hUV : IsCoprime U V)
--     (hUpVp : IsCoprime Up Vp)
--     (hUeven : Even U) (hUpeven : Even Up)
--     (hVodd : Odd V) (hVpodd : Odd Vp) :
--     exists a b c d : Int,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = 2 * a * b /\ V = c * d /\
--       Up = 2 * a * c /\ Vp = b * d /\
--       IsCoprime a b /\ IsCoprime a c /\ IsCoprime a d /\
--       IsCoprime b c /\ IsCoprime b d /\ IsCoprime c d /\
--       Odd b /\ Odd c /\ Odd d
```

For the final Euler descent, you can project just:

```text
0<a,b,c,d,
U=2ab, V=cd, Up=2ac, Vp=bd,
IsCoprime a d,
IsCoprime b c,
Odd b, Odd c, Odd d.
```

But returning all six coprimalities avoids re-proving divisibility projections later.

## 7. Residual recommendation

I would not mark the Nat core as a hard residual; it should be a manageable local lemma using `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`.

If you need to unblock the descent while another worker fills in the local arithmetic, use this exact residual boundary:

```lean
-- RESIDUAL, finite standard gcd lemma.
-- theorem two_coprime_factorizations_refine_even_even_odd_odd_int_pos
--     {U V Up Vp : Int}
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hEq : U * V = Up * Vp)
--     (hUV : IsCoprime U V)
--     (hUpVp : IsCoprime Up Vp)
--     (hUeven : Even U) (hUpeven : Even Up)
--     (hVodd : Odd V) (hVpodd : Odd Vp) :
--     exists a b c d : Int,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = 2 * a * b /\ V = c * d /\
--       Up = 2 * a * c /\ Vp = b * d /\
--       IsCoprime a b /\ IsCoprime a c /\ IsCoprime a d /\
--       IsCoprime b c /\ IsCoprime b d /\ IsCoprime c d /\
--       Odd b /\ Odd c /\ Odd d
```

This is mathematically finite/standard because it is only unique prime-factor distribution across two coprime bipartitions of the same positive integer. The gcd proof avoids explicit prime factorization and should be the first implementation attempt.

## 8. Exact later use in `EulerSquarePairDescent`

After signed Pythagorean parameters give

```text
E.A = U*V = Up*Vp,
U,Up even,
V,Vp odd,
IsCoprime U V,
IsCoprime Up Vp,
```

apply the parity-specialized wrapper to get:

```text
U  = 2*a*b,
V  = c*d,
Up = 2*a*c,
Vp = b*d.
```

Then the signed-D formulas become:

```text
D = epsC * ((2*a*b)^2 - (c*d)^2),
D = epsB * (4*(2*a*c)^2 - (b*d)^2).
```

The important refinement outputs downstream are:

```text
IsCoprime b c
IsCoprime a d
Odd b, Odd c, Odd d
0 < a,b,c,d
```

They feed the same-orientation mod-4 argument, the balance equation

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2),
```

and the final square-factor extraction for the smaller Euler pair.
