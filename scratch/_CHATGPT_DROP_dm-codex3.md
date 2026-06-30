# Q2556: EulerSquarePairDescent proof plan

This is the honest Lean-oriented route for the N=12 four-squares AP descent interface.

## Immediate flags

1. The final statement

```lean
def EulerSquarePairDescent : Prop :=
  forall E : EulerSquarePair, exists F : EulerSquarePair, F.A * F.D < E.A * E.D
```

is not visibly false from the stated hypotheses. The classical descent should have this shape.

2. The Q2548 one-line construction `F = (a,d,b,c)` only works after a **same-orientation** normalization of the two Pythagorean parametrizations. From the current `EulerSquarePair` fields alone, the even Pythagorean parameter need not a priori be the larger parameter in either triple. Do not silently assume formulas `D = U^2 - V^2` and `D = 4*U'^2 - V'^2`; either prove the same-orientation lemma or carry a signed parametrization and handle the mixed cases separately.

3. As stated in the prompt, the lemma

> from `b^2*M = c^2*N`, `b,c,M,N>0`, `IsCoprime b c`, infer `M = c^2` and `N = b^2`

is mathematically false without a coprimality/normalization hypothesis on `M,N`; for example `2^2 * 18 = 3^2 * 8`. The usable version must also consume `IsCoprime M N`, or be specialized to the Euler cofactors after proving they are coprime.

The rest of this note gives the decomposition that closes the same-orientation branch and isolates the exact remaining orientation obligation.

## 1. Primitive triples from `E`

From `E.hADcop`, `E.hDodd`, and `E.hAeven`, prove:

- `IsCoprime (2 * E.A) E.D`.
- `IsCoprime (4 * E.A) E.D`.
- `(2 * E.A)^2 + E.D^2 = E.C^2` from `E.hC`.
- `(4 * E.A)^2 + E.D^2 = E.B^2` from `E.hB`.

The Pythagorean parametrization needed is the primitive even-leg version.

```lean
theorem pythagorean_param_even_leg_int
    {X Y Z : Int}
    (hXpos : 0 < X) (hYpos : 0 < Y) (hZpos : 0 < Z)
    (hXeven : Even X) (hYodd : Odd Y)
    (hcop : IsCoprime X Y)
    (h : Z ^ 2 = X ^ 2 + Y ^ 2) :
    exists m n : Int,
      0 < n /\ n < m /\
      IsCoprime m n /\
      ((Even m /\ Odd n) \/ (Odd m /\ Even n)) /\
      X = 2 * m * n /\
      Y = m ^ 2 - n ^ 2 /\
      Z = m ^ 2 + n ^ 2
```

Expected proof method if Mathlib's Pythagorean-triple API is awkward: factor `(Z+Y)*(Z-Y)=X^2`, show `(Z+Y)/2` and `(Z-Y)/2` are coprime positive square factors, then recover `m,n`. This avoids depending on fragile theorem names.

Apply this twice:

- C-triple: even leg `2*A`, odd leg `D`, hypotenuse `C`.
- B-triple: even leg `4*A`, odd leg `D`, hypotenuse `B`.

## 2. Signed normalized parametrizations

For the C-triple, let `U` be the even Pythagorean parameter and `V` the odd one. Then there is a sign `epsC = 1` or `epsC = -1` such that:

```lean
theorem EulerSquarePair.C_param_signed (E : EulerSquarePair) :
    exists U V epsC : Int,
      0 < U /\ 0 < V /\
      IsCoprime U V /\ Even U /\ Odd V /\
      (epsC = 1 \/ epsC = -1) /\
      E.A = U * V /\
      E.D = epsC * (U ^ 2 - V ^ 2) /\
      E.C = U ^ 2 + V ^ 2
```

Explanation: standard parameters give `A = m*n`, `D = m^2-n^2`, `C=m^2+n^2`. If `m` is even, take `U=m,V=n,epsC=1`; if `n` is even, take `U=n,V=m,epsC=-1`.

For the B-triple, let the even standard parameter be `2*U'` and the odd one be `V'`. Since the standard product is `2*A` and `A` is even while `V'` is odd, `U'` is even. There is a sign `epsB = 1` or `epsB = -1` such that:

```lean
theorem EulerSquarePair.B_param_signed (E : EulerSquarePair) :
    exists Up Vp epsB : Int,
      0 < Up /\ 0 < Vp /\
      IsCoprime Up Vp /\ Even Up /\ Odd Vp /\
      (epsB = 1 \/ epsB = -1) /\
      E.A = Up * Vp /\
      E.D = epsB * (4 * Up ^ 2 - Vp ^ 2) /\
      E.B = 4 * Up ^ 2 + Vp ^ 2
```

Explanation: standard parameters give `2*A = r*s`, `D=r^2-s^2`, `B=r^2+s^2`. If the even standard parameter is the larger one, write it as `2*Up` and take `epsB=1`; if it is the smaller one, take `epsB=-1`.

## 3. Refining the two factorizations of `A`

Use the banked raw refinement on

```lean
E.A = U * V
E.A = Up * Vp
```

with `U,Up` even and `V,Vp` odd. The Euler-specialized wrapper should expose exactly the factors needed downstream:

```lean
theorem euler_two_coprime_factorizations_refine
    {A U V Up Vp : Int}
    (hApos : 0 < A)
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hUV : A = U * V) (hUpVp : A = Up * Vp)
    (hcopUV : IsCoprime U V) (hcopUpVp : IsCoprime Up Vp)
    (hUeven : Even U) (hUpeven : Even Up)
    (hVodd : Odd V) (hVpodd : Odd Vp) :
    exists a b c d : Int,
      0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
      U = 2 * a * b /\ V = c * d /\
      Up = 2 * a * c /\ Vp = b * d /\
      IsCoprime a d /\ IsCoprime b c /\
      Odd b /\ Odd c /\ Odd d
```

The important outputs are:

- `E.A = 2*a*b*c*d`.
- `IsCoprime b c`, for square-factor balance.
- `IsCoprime a d` and `Odd d`, for the new Euler pair.
- `Odd b`, `Odd c`, `Odd d`, from `V=c*d` and `Vp=b*d` odd.

## 4. Same-orientation balance

If the signs agree, `epsC = epsB`, the two D-formulas imply the Q2548 balance.

```lean
theorem euler_balance_of_same_orientation
    {D U V Up Vp eps a b c d : Int}
    (heps : eps = 1 \/ eps = -1)
    (hD_C : D = eps * (U ^ 2 - V ^ 2))
    (hD_B : D = eps * (4 * Up ^ 2 - Vp ^ 2))
    (hU : U = 2 * a * b) (hV : V = c * d)
    (hUp : Up = 2 * a * c) (hVp : Vp = b * d) :
    b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2)
```

Proof shape: case on `heps`; in both cases substitute and use `ring_nf` or `nlinarith` after normalizing.

Algebra in the `eps=1` case:

```text
(2ab)^2 - (cd)^2 = 4*(2ac)^2 - (bd)^2
4a^2 b^2 - c^2 d^2 = 16a^2 c^2 - b^2 d^2
b^2*(4a^2+d^2) = c^2*(16a^2+d^2).
```

The `eps=-1` case gives the same final equality after multiplying both D-formulas by `-1`.

## 5. Coprimality of the Euler cofactors

Before using square-factor balance, prove the two cofactors are coprime.

```lean
theorem euler_cofactors_coprime
    {a d : Int}
    (had : IsCoprime a d) (hdodd : Odd d) :
    IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2)
```

Mathematical proof: a common prime divisor divides the difference `12*a^2`. It cannot divide `a`, because then it would divide `d`. Hence it can only be `2` or `3`. The prime `2` is excluded because both cofactors are odd. The prime `3` is excluded by checking squares mod `3`: if `3` divides neither `a` nor `d`, both cofactors are `2 mod 3`; if `3` divides exactly one of `a,d`, the other term is nonzero mod `3`.

Expected Lean proof options:

- prove through `Nat.Prime.dvd_of_dvd_pow`, `Int.Prime`, and `IsCoprime` divisibility; or
- prove an `Int.gcd` divisibility bound `Int.gcd M N ∣ 12`, then use oddness and mod-3 exclusion; or
- move to `ZMod 2` and `ZMod 3` for the local exclusions.

## 6. Square-factor balance

Use the corrected/banked balance lemma in this shape:

```lean
theorem square_factor_balance_int_coprime
    {b c M N : Int}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 < M) (hN : 0 < N)
    (hbc : IsCoprime b c) (hMN : IsCoprime M N)
    (hbal : b ^ 2 * M = c ^ 2 * N) :
    M = c ^ 2 /\ N = b ^ 2
```

Apply it with

```text
M = 4*a^2 + d^2,
N = 16*a^2 + d^2.
```

The result is:

```lean
hCsmall : c ^ 2 = 4 * a ^ 2 + d ^ 2
hBsmall : b ^ 2 = 16 * a ^ 2 + d ^ 2
```

up to symmetry/rewrite orientation.

## 7. Constructing the smaller Euler pair

In the same-orientation branch, define:

```text
F.A = a
F.D = d
F.B = b
F.C = c
```

The fields are justified as follows:

- `F.hApos`: from refinement, `0<a`.
- `F.hDpos`: from refinement, `0<d`.
- `F.hDodd`: from refinement, `Odd d`.
- `F.hADcop`: from refinement, `IsCoprime a d`.
- `F.hBpos`, `F.hCpos`: from refinement, `0<b`, `0<c`.
- `F.hB`: from `hBsmall`.
- `F.hC`: from `hCsmall`.
- `F.hAeven`: this is a small but necessary modular lemma.

```lean
theorem even_a_of_small_C_square
    {a c d : Int}
    (hdodd : Odd d)
    (hC : c ^ 2 = 4 * a ^ 2 + d ^ 2) :
    Even a
```

Proof: if `a` were odd and `d` is odd, then `4*a^2 + d^2 == 5 mod 8`, impossible for a square. In Lean this is best isolated as a tiny `ZMod 8` lemma or an `omega`/`norm_num` parity lemma after case-splitting on parity.

A builder theorem for the branch:

```lean
theorem EulerSquarePair.mk_smaller_from_same_orientation_refinement
    (E : EulerSquarePair)
    {a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (had : IsCoprime a d) (hbc : IsCoprime b c)
    (hdodd : Odd d)
    (hCsmall : c ^ 2 = 4 * a ^ 2 + d ^ 2)
    (hBsmall : b ^ 2 = 16 * a ^ 2 + d ^ 2)
    (hEA : E.A = 2 * a * b * c * d) :
    exists F : EulerSquarePair,
      F.A = a /\ F.D = d /\ F.B = b /\ F.C = c /\
      F.A * F.D < E.A * E.D
```

## 8. Strict descent inequality

Using `E.A = 2*a*b*c*d`, positivity of `a,b,c,d`, and `E.hDpos`:

```text
F.A * F.D = a*d.
E.A * E.D = (2*a*b*c*d) * E.D
           = a*d * (2*b*c*E.D).
```

Since `b,c,E.D` are positive integers,

```text
1 < 2*b*c*E.D.
```

Since `0 < a*d`, multiply by `a*d`:

```text
a*d < a*d * (2*b*c*E.D) = E.A * E.D.
```

Lean proof shape:

```lean
theorem euler_smaller_product_from_refinement
    (E : EulerSquarePair)
    {a b c d : Int}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hEA : E.A = 2 * a * b * c * d) :
    a * d < E.A * E.D := by
  have had_pos : 0 < a * d := mul_pos ha hd
  have hfactor : 1 < 2 * b * c * E.D := by
    nlinarith [hb, hc, E.hDpos]
  calc
    a * d = a * d * 1 := by ring
    _ < a * d * (2 * b * c * E.D) := by
      exact mul_lt_mul_of_pos_left hfactor had_pos
    _ = E.A * E.D := by
      rw [hEA]
      ring
```

This inequality is robust: it does not require proving `d < E.D`.

## 9. Final theorem DAG

Use these as the Lean milestones:

1. `EulerSquarePair.coprime_twoA_D` and `EulerSquarePair.coprime_fourA_D`.
2. `pythagorean_param_even_leg_int`.
3. `EulerSquarePair.C_param_signed`.
4. `EulerSquarePair.B_param_signed`.
5. `euler_two_coprime_factorizations_refine` wrapping the banked `two_coprime_factorizations_refine_raw_pos`.
6. `euler_balance_of_same_orientation`.
7. `euler_cofactors_coprime`.
8. corrected `square_factor_balance_int_coprime` or a wrapper around the banked lemma with the missing cofactor coprimality supplied.
9. `even_a_of_small_C_square`.
10. `EulerSquarePair.mk_smaller_from_same_orientation_refinement`.
11. `euler_smaller_product_from_refinement`.
12. Orientation closure:

```lean
def EulerSquarePairHasSameOrientation (E : EulerSquarePair) : Prop :=
  exists U V Up Vp eps : Int,
    0 < U /\ 0 < V /\ 0 < Up /\ 0 < Vp /\
    IsCoprime U V /\ IsCoprime Up Vp /\
    Even U /\ Odd V /\ Even Up /\ Odd Vp /\
    (eps = 1 \/ eps = -1) /\
    E.A = U * V /\ E.A = Up * Vp /\
    E.D = eps * (U ^ 2 - V ^ 2) /\
    E.C = U ^ 2 + V ^ 2 /\
    E.D = eps * (4 * Up ^ 2 - Vp ^ 2) /\
    E.B = 4 * Up ^ 2 + Vp ^ 2

theorem EulerSquarePairDescent_of_sameOrientation
    (hsame : forall E : EulerSquarePair, EulerSquarePairHasSameOrientation E) :
    EulerSquarePairDescent
```

To prove the unconditional `EulerSquarePairDescent`, either prove `hsame`, or add a separate mixed-orientation descent theorem. The mixed case gives a different algebraic balance with difference cofactors, not the Q2548 positive-cofactor balance, so it must not be hidden inside the same proof.

## Bottom line

The clean branch is:

```text
E
 -> signed C/B primitive parametrizations
 -> same-orientation normalized parameters
 -> U=2ab, V=cd, Up=2ac, Vp=bd
 -> b^2*(4a^2+d^2)=c^2*(16a^2+d^2)
 -> coprime cofactors + square-factor balance
 -> c^2=4a^2+d^2 and b^2=16a^2+d^2
 -> F=(a,d,b,c)
 -> F.A*F.D < E.A*E.D.
```

The two critical proof obligations not to paper over are the signed-orientation closure and the cofactor-coprime input to square-factor balance.
