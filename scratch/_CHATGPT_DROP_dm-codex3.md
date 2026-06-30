# Q2609: theorem DAG for `PrimitiveCenteredToEulerSquarePair`

Target file family: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Namespace: `MazurProof.RationalPointsN12`.

Goal:

```lean
def PrimitiveCenteredToEulerSquarePair : Prop :=
  forall S : PrimitiveCenteredFourSqAP, exists E : EulerSquarePair, S.N = E.A * E.D
```

The construction should use **one** primitive Pythagorean triple, coming from the checked identity

```lean
theorem primitiveCentered_big_pyth_identity (S) :
  (S.X^2 - 20*S.N^2)^2 = (S.p*S.q*S.r*S.s)^2 + (16*S.N^2)^2
```

and then split the coprime product in the parametrization.

## 0. Import/API boundary

Use Mathlib's Pythagorean triple API:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
```

The useful Mathlib theorem is:

```lean
-- PythagoreanTriple.coprime_classification'
--   {x y z : Int} (h : PythagoreanTriple x y z)
--   (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1)
--   (h_pos : 0 < z) :
--   exists m n,
--     x = m ^ 2 - n ^ 2 /\
--     y = 2 * m * n /\
--     z = m ^ 2 + n ^ 2 /\
--     Int.gcd m n = 1 /\
--     ((m % 2 = 0 /\ n % 2 = 1) \/ (m % 2 = 1 /\ n % 2 = 0)) /\
--     0 <= m
```

## 1. The Pythagorean triple to parametrize

For `S : PrimitiveCenteredFourSqAP`, set

```text
O := S.p * S.q * S.r * S.s
Y := 16 * S.N^2
Z := S.X^2 - 20 * S.N^2
```

Then parametrize the primitive triple

```text
O^2 + Y^2 = Z^2.
```

Use odd leg first, even leg second:

```lean
-- theorem primitiveCentered_big_pyth_triple (S : PrimitiveCenteredFourSqAP) :
--     PythagoreanTriple
--       (S.p * S.q * S.r * S.s)
--       (16 * S.N ^ 2)
--       (S.X ^ 2 - 20 * S.N ^ 2)
```

Proof: unfold `PythagoreanTriple`; use `primitiveCentered_big_pyth_identity S` and `ring_nf` to flip the equality into Mathlib's `x*x + y*y = z*z` convention.

### Positivity of the hypotenuse

Do **not** use `abs (S.X^2 - 20*S.N^2)`. It is already positive. From

```text
S.p^2 = S.X - 6*S.N
```

and `S.p^2 >= 0`, get `S.X >= 6*S.N`; since `S.N > 0`,

```text
S.X^2 - 20*S.N^2 >= 36*S.N^2 - 20*S.N^2 = 16*S.N^2 > 0.
```

Suggested helper:

```lean
-- theorem primitiveCentered_big_hyp_pos (S : PrimitiveCenteredFourSqAP) :
--     0 < S.X ^ 2 - 20 * S.N ^ 2
```

This avoids the main absolute-value/sign trap.

### Odd leg parity

Use the four mod fields directly:

```lean
-- theorem primitiveCentered_root_product_mod_two (S : PrimitiveCenteredFourSqAP) :
--     (S.p * S.q * S.r * S.s) % 2 = 1
```

Proof: repeated `Int.mul_emod`, `S.hp_odd`, `S.hq_odd`, `S.hr_odd`, `S.hs_odd`, then `norm_num`/`decide`.

## 2. Primitive gcd obligation for the big triple

Need:

```lean
-- theorem primitiveCentered_big_triple_coprime (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd (S.p * S.q * S.r * S.s) (16 * S.N ^ 2) = 1
```

Break this into local lemmas.

First, adjacent square gaps:

```lean
-- theorem primitiveCentered_gap_pq (S : PrimitiveCenteredFourSqAP) :
--     S.q ^ 2 - S.p ^ 2 = 4 * S.N
--
-- theorem primitiveCentered_gap_qr (S : PrimitiveCenteredFourSqAP) :
--     S.r ^ 2 - S.q ^ 2 = 4 * S.N
--
-- theorem primitiveCentered_gap_rs (S : PrimitiveCenteredFourSqAP) :
--     S.s ^ 2 - S.r ^ 2 = 4 * S.N
```

Each is a direct subtraction of `hp,hq,hr,hs` followed by `ring`/`nlinarith`.

Then prove a reusable adjacent-root-to-step coprimality lemma:

```lean
-- theorem gcd_left_step_of_adjacent_square_gap
--     {u v N : Int}
--     (huv : Int.gcd u v = 1)
--     (hgap : v ^ 2 - u ^ 2 = 4 * N) :
--     Int.gcd u N = 1
--
-- theorem gcd_right_step_of_adjacent_square_gap
--     {u v N : Int}
--     (huv : Int.gcd u v = 1)
--     (hgap : v ^ 2 - u ^ 2 = 4 * N) :
--     Int.gcd v N = 1
```

Mathematical proof: a prime divisor of `u` and `N` divides `v^2 = u^2 + 4N`, hence divides `v`, contradicting `Int.gcd u v = 1`. The right version is symmetric using `u^2 = v^2 - 4N`.

Apply these to get:

```lean
-- theorem primitiveCentered_p_coprime_N (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd S.p S.N = 1
-- theorem primitiveCentered_q_coprime_N (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd S.q S.N = 1
-- theorem primitiveCentered_r_coprime_N (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd S.r S.N = 1
-- theorem primitiveCentered_s_coprime_N (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd S.s S.N = 1
```

Only adjacent gcd fields are needed here: `hpq`, `hqr`, `hrs`. The non-adjacent gcd fields are not essential for this direction.

Then combine:

```lean
-- theorem primitiveCentered_root_product_coprime_N (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd (S.p * S.q * S.r * S.s) S.N = 1
--
-- theorem primitiveCentered_root_product_coprime_sixteen (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd (S.p * S.q * S.r * S.s) 16 = 1
--
-- theorem primitiveCentered_big_triple_coprime (S : PrimitiveCenteredFourSqAP) :
--     Int.gcd (S.p * S.q * S.r * S.s) (16 * S.N ^ 2) = 1
```

For the last step, use product/power coprimality: coprime to `N` gives coprime to `N^2`, and oddness gives coprime to `16`.

## 3. Evenness of `S.N`

This is required later to make the Euler `A` even. It is easy but must not be skipped.

```lean
-- theorem primitiveCentered_N_even (S : PrimitiveCenteredFourSqAP) :
--     Even S.N
```

Proof: from `primitiveCentered_gap_pq S`,

```text
S.q^2 - S.p^2 = 4*S.N.
```

Since `S.p` and `S.q` are odd, odd squares are `1 mod 8`, hence `8 | S.q^2 - S.p^2`; therefore `2 | S.N`. In Lean, isolate the mod-8 arithmetic:

```lean
-- theorem even_step_of_odd_adjacent_square_gap
--     {p q N : Int}
--     (hp : p % 2 = 1) (hq : q % 2 = 1)
--     (hgap : q ^ 2 - p ^ 2 = 4 * N) :
--     Even N
```

## 4. Parametrization output and square split

Apply `PythagoreanTriple.coprime_classification'` to

```text
x = O, y = 16*S.N^2, z = Z.
```

Obtain `m n : Int` with

```text
O = m^2 - n^2,
16*S.N^2 = 2*m*n,
Z = m^2 + n^2,
Int.gcd m n = 1,
opposite parity,
0 <= m.
```

From `16*S.N^2 = 2*m*n`, derive

```text
m*n = 8*S.N^2.
```

Also prove `0 < m` and `0 < n`: `16*S.N^2 > 0`, `2*m*n > 0`, and Mathlib gives `0 <= m`; if `m=0` the even leg is zero, contradiction, and then `n>0` follows from positive product.

The key arithmetic residual is the coprime product split.

```lean
-- RESIDUAL, finite standard prime-factorization/valuation lemma.
-- theorem coprime_product_eq_eight_square_split_int
--     {N m n : Int}
--     (hNpos : 0 < N)
--     (hNeven : Even N)
--     (hmpos : 0 < m) (hnpos : 0 < n)
--     (hmn : m * n = 8 * N ^ 2)
--     (hmn_coprime : Int.gcd m n = 1)
--     (hparity :
--       (m % 2 = 0 /\ n % 2 = 1) \/
--       (m % 2 = 1 /\ n % 2 = 0)) :
--     exists A D : Int,
--       0 < A /\ 0 < D /\
--       Even A /\ Odd D /\ IsCoprime A D /\
--       N = A * D /\
--       ((m = 8 * A ^ 2 /\ n = D ^ 2) \/
--        (m = D ^ 2 /\ n = 8 * A ^ 2))
```

This lemma is mathematically standard: because `m,n` are coprime and `m*n = 8*N^2`, each prime's valuation goes wholly into exactly one of `m,n`; the odd parameter is a square `D^2`, and the even parameter is `8*A^2`. The hypothesis `Even N` is necessary for `Even A`; without it the statement is false, e.g. `N=1` gives the split `1 * 8` and `A=1`.

This gives the desired candidate Euler parameters `A,D`, with

```text
S.N = A*D,
A > 0,
D > 0,
A even,
D odd,
IsCoprime A D.
```

## 5. Recovering the Euler square factors `B,C`

From parametrization and the split, we know

```text
Z = m^2+n^2 = D^4 + 64*A^4
```

in either split case. Since `Z = S.X^2 - 20*S.N^2` and `S.N = A*D`, get

```text
S.X^2 = D^4 + 20*A^2*D^2 + 64*A^4
      = (D^2 + 16*A^2) * (D^2 + 4*A^2).
```

Use this algebra helper:

```lean
-- theorem center_square_eq_euler_cofactor_product_of_big_split
--     {X N m n A D : Int}
--     (hZ : X ^ 2 - 20 * N ^ 2 = m ^ 2 + n ^ 2)
--     (hN : N = A * D)
--     (hsplit :
--       (m = 8 * A ^ 2 /\ n = D ^ 2) \/
--       (m = D ^ 2 /\ n = 8 * A ^ 2)) :
--     X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)
```

Proof: cases on `hsplit`; `nlinarith` or `ring_nf` after substitutions.

Then prove the two cofactors are coprime:

```lean
-- theorem euler_cofactor_coprime
--     {A D : Int}
--     (hAD : IsCoprime A D)
--     (hDodd : Odd D) :
--     IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2)
```

Mathematical proof: a common prime divisor divides the difference `12*A^2`. It cannot divide `A`, because then it divides `D`. Thus it can only be `2` or `3`. `2` is excluded since `D` is odd, so both cofactors are odd. `3` is excluded because modulo `3` the two cofactors are both `A^2 + D^2`; with `gcd(A,D)=1`, this is never `0 mod 3`.

Now extract the square roots:

```lean
-- theorem euler_cofactors_are_squares_of_center_square
--     {A D X : Int}
--     (hApos : 0 < A) (hDpos : 0 < D)
--     (hDodd : Odd D)
--     (hAD : IsCoprime A D)
--     (hXsq : X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
--     exists B C : Int,
--       0 < B /\ 0 < C /\
--       B ^ 2 = 16 * A ^ 2 + D ^ 2 /\
--       C ^ 2 = 4 * A ^ 2 + D ^ 2
```

Proof route: use `euler_cofactor_coprime` and the standard coprime-product-square extraction lemma. Positivity of the factors is immediate from `A,D > 0`. Choose positive roots by taking absolute values if the extraction lemma returns arbitrary signed roots.

## 6. Final constructor theorem

A good final wrapper is:

```lean
-- theorem primitiveCentered_to_eulerSquarePair (S : PrimitiveCenteredFourSqAP) :
--     exists E : EulerSquarePair, S.N = E.A * E.D
```

Implementation skeleton:

```text
1. Let O := S.p*S.q*S.r*S.s, Y := 16*S.N^2, Z := S.X^2 - 20*S.N^2.
2. Prove `PythagoreanTriple O Y Z` from `primitiveCentered_big_pyth_identity`.
3. Prove `Int.gcd O Y = 1` from root-step coprimality and root oddness.
4. Prove `O % 2 = 1` and `0 < Z`.
5. Apply `PythagoreanTriple.coprime_classification'`.
6. Derive `m*n = 8*S.N^2`, `m>0`, `n>0`.
7. Prove `Even S.N`.
8. Apply `coprime_product_eq_eight_square_split_int` to obtain `A,D`.
9. Use `Z = m^2+n^2`, `S.N=A*D`, and the split to prove
   `S.X^2 = (16*A^2+D^2)*(4*A^2+D^2)`.
10. Apply `euler_cofactors_are_squares_of_center_square` to obtain positive `B,C`.
11. Construct

   E := { A := A, D := D, B := B, C := C,
          hApos := ..., hDpos := ..., hDodd := ..., hAeven := ...,
          hADcop := ..., hBpos := ..., hCpos := ...,
          hB := ..., hC := ... }

12. The required equality is exactly `S.N = E.A * E.D`, from the split theorem.
```

## 7. Hidden sign and absolute-value choices

These are the places where false statements can creep in:

1. **Do not use an absolute-value hypotenuse unless necessary.** Here `S.X^2 - 20*S.N^2 > 0`, so the Mathlib positive-hypotenuse theorem applies directly.

2. **Do not assume `S.p*S.q*S.r*S.s > 0`.** The odd leg may be negative. This is fine: `PythagoreanTriple.coprime_classification'` permits a negative odd leg and returns `m^2-n^2 = O`, which records the sign through the order of `m,n`.

3. **Do not state the `8*N^2` split with `A` even unless `Even N` is supplied.** `Even S.N` follows from the AP odd-square gap and must be part of the dependency chain.

4. **Do not require `X = B*C` for the EulerSquarePair structure.** It is probably true with positive roots and `X>0`, but the structure only needs the two square equations. Avoiding `X=B*C` keeps the construction shorter.

5. **The signs of extracted square roots for `B,C` are irrelevant only if you choose positive roots.** If the local square-extraction lemma returns arbitrary roots, define `B := |b0|`, `C := |c0|` and use factor positivity to prove strict positivity.

## 8. Dependency DAG

Minimal DAG:

```text
PrimitiveCentered fields
  -> gap lemmas pq/qr/rs
  -> root-step gcd lemmas
  -> root_product_coprime_N
  -> root_product_coprime_16
  -> big_triple_coprime

PrimitiveCentered fields
  -> root_product_mod_two
  -> big_hyp_pos
  -> big_pyth_triple
  -> PythagoreanTriple.coprime_classification'
  -> m,n with 16*N^2 = 2mn and gcd(m,n)=1

odd adjacent square gap
  -> Even S.N

m,n data + Even S.N
  -> coprime_product_eq_eight_square_split_int
  -> A,D with S.N=A*D, A even, D odd, gcd(A,D)=1

Z=m^2+n^2 + split + S.N=A*D
  -> center_square_eq_euler_cofactor_product_of_big_split
  -> X^2=(16A^2+D^2)(4A^2+D^2)

A,D data
  -> euler_cofactor_coprime
  -> euler_cofactors_are_squares_of_center_square
  -> positive B,C

A,D,B,C
  -> EulerSquarePair
  -> S.N = E.A*E.D
```

The only residual I would mark as genuinely nontrivial is `coprime_product_eq_eight_square_split_int`; it is standard finite valuation arithmetic. The remaining helpers are local gcd/parity/algebra lemmas and should be implementable without axioms or paper-scale work.
