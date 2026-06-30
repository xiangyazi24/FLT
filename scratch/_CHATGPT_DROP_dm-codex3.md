# Q2577: `EulerSquarePairDescent` steps 1--4 theorem DAG

Target family: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Target interface:

```lean
def EulerSquarePairDescent : Prop :=
  forall E : EulerSquarePair, exists F : EulerSquarePair, F.A * F.D < E.A * E.D
```

This note focuses on the parametrization/refinement part of the descent:

```text
primitive Pythagorean triples
 -> signed even/odd Euler parameters
 -> same-orientation proof
 -> two-factorization refinement
 -> balance equation.
```

## 0. Main warning

Do **not** ask directly for both formulas

```text
D = U^2 - V^2,
D = 4*U'^2 - V'^2
```

with `U,U'` the even parameters and `V,V'` the odd parameters. That is stronger than the raw primitive-triple output. Since `D > 0` only says the **larger** Pythagorean parameter comes first, the even parameter may be the larger or the smaller one.

The right normalized interface is either:

1. Mathlib-normalized larger/smaller parameters, with no fixed even-variable name; or
2. even/odd parameters plus a sign.

For the descent/refinement route, use option 2:

```text
C-triple: A = U*V,  D = epsC * (U^2 - V^2),       C = U^2 + V^2,
          U even, V odd, epsC in {1,-1}.

B-triple: A = Up*Vp, D = epsB * (4*Up^2 - Vp^2), B = 4*Up^2 + Vp^2,
          Up even, Vp odd, epsB in {1,-1}.
```

Then prove `epsC = epsB` after the two factorizations are refined. The shortest same-orientation proof uses parity of the refined odd factors; proving it before refinement is possible but less convenient.

## 1. Mathlib Pythagorean-triple API to use

Use the file:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
```

Do not import all of `Mathlib` just for this.

The useful theorem is exactly:

```lean
-- in namespace PythagoreanTriple
-- theorem coprime_classification'
--     {x y z : Int} (h : PythagoreanTriple x y z)
--     (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
--     exists m n,
--       x = m ^ 2 - n ^ 2 /\
--       y = 2 * m * n /\
--       z = m ^ 2 + n ^ 2 /\
--       Int.gcd m n = 1 /\
--       ((m % 2 = 0 /\ n % 2 = 1) \/ (m % 2 = 1 /\ n % 2 = 0)) /\
--       0 <= m
```

It is better than the general `PythagoreanTriple.coprime_classification` because it fixes the odd leg as `x = m^2 - n^2` and the positive hypotenuse as `z = m^2+n^2`.

Apply it with the **odd leg first**:

```text
C-triple: x = E.D, y = 2*E.A, z = E.C.
B-triple: x = E.D, y = 4*E.A, z = E.B.
```

## 2. Primitive hypotheses for the two triples

From the structure fields, isolate these wrappers.

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair

-- Suggested local wrappers. These are not residuals; they should be short local lemmas.
-- theorem gcd_D_twoA_eq_one (E : EulerSquarePair) :
--     Int.gcd E.D (2 * E.A) = 1
--
-- theorem gcd_D_fourA_eq_one (E : EulerSquarePair) :
--     Int.gcd E.D (4 * E.A) = 1
--
-- theorem D_mod_two_eq_one (E : EulerSquarePair) :
--     E.D % 2 = 1
--
-- theorem pythagorean_D_twoA_C (E : EulerSquarePair) :
--     PythagoreanTriple E.D (2 * E.A) E.C
--
-- theorem pythagorean_D_fourA_B (E : EulerSquarePair) :
--     PythagoreanTriple E.D (4 * E.A) E.B

end MazurProof.RationalPointsN12.EulerSquarePair
```

Proof hints:

* `D_mod_two_eq_one` comes from `E.hDodd`. If the `Odd` API is annoying, use `Int.emod_two_eq_zero_or_one E.D` and rule out `% 2 = 0` by `Odd.not_even`.
* `gcd_D_twoA_eq_one`: use `E.hADcop` plus oddness of `D`. Any prime divisor of `D` and `2*A` either divides `2` or `A`; `D` odd excludes `2`, and `IsCoprime A D` excludes `A`.
* `gcd_D_fourA_eq_one`: same proof, replacing `2` by `4`. A divisor of `4` is a power of `2`, again excluded by `D` odd.
* `pythagorean_D_twoA_C`: unfold `PythagoreanTriple`; use `E.hC` and `ring_nf`/`nlinarith`.
* `pythagorean_D_fourA_B`: unfold `PythagoreanTriple`; use `E.hB` and `ring_nf`/`nlinarith`.

## 3. Larger/smaller parameter outputs from Mathlib

After applying `coprime_classification'`, wrap the outputs into project-specific structures or theorem outputs.

For `(2A)^2 + D^2 = C^2`:

```lean
-- theorem C_larger_smaller_params (E : EulerSquarePair) :
--     exists m n : Int,
--       0 < m /\ 0 < n /\ n < m /\
--       E.D = m ^ 2 - n ^ 2 /\
--       E.A = m * n /\
--       E.C = m ^ 2 + n ^ 2 /\
--       Int.gcd m n = 1 /\
--       ((m % 2 = 0 /\ n % 2 = 1) \/ (m % 2 = 1 /\ n % 2 = 0))
```

For `(4A)^2 + D^2 = B^2`:

```lean
-- theorem B_larger_smaller_params (E : EulerSquarePair) :
--     exists r s : Int,
--       0 < r /\ 0 < s /\ s < r /\
--       E.D = r ^ 2 - s ^ 2 /\
--       2 * E.A = r * s /\
--       E.B = r ^ 2 + s ^ 2 /\
--       Int.gcd r s = 1 /\
--       ((r % 2 = 0 /\ s % 2 = 1) \/ (r % 2 = 1 /\ s % 2 = 0))
```

Derivations after Mathlib output:

* For C, Mathlib gives `2*A = 2*m*n`; cancel `2` to get `A=m*n`.
* For B, Mathlib gives `4*A = 2*r*s`; cancel `2` to get `2*A=r*s`.
* Positivity of `m,n,r,s`: from `A>0`, `2A=r*s>0`, and Mathlib's `0 <= m`/`0 <= r`; then rule out zero and show the other factor is positive.
* `n<m` and `s<r`: from `D>0` and `D=m^2-n^2` / `D=r^2-s^2`, with both parameters positive.

## 4. Signed even/odd Euler parameters

The Mathlib output is larger/smaller. For refinement, convert it to even/odd variables.

C-side signed wrapper:

```lean
-- theorem C_signed_even_odd_params (E : EulerSquarePair) :
--     exists U V epsC : Int,
--       0 < U /\ 0 < V /\
--       IsCoprime U V /\ Even U /\ Odd V /\
--       (epsC = 1 \/ epsC = -1) /\
--       E.A = U * V /\
--       E.D = epsC * (U ^ 2 - V ^ 2) /\
--       E.C = U ^ 2 + V ^ 2
```

Construction:

* If the larger parameter `m` is even and `n` is odd, set `U=m`, `V=n`, `epsC=1`.
* If `m` is odd and `n` is even, set `U=n`, `V=m`, `epsC=-1`.

B-side signed wrapper:

```lean
-- theorem B_signed_even_odd_params (E : EulerSquarePair) :
--     exists Up Vp epsB : Int,
--       0 < Up /\ 0 < Vp /\
--       IsCoprime Up Vp /\ Even Up /\ Odd Vp /\
--       (epsB = 1 \/ epsB = -1) /\
--       E.A = Up * Vp /\
--       E.D = epsB * (4 * Up ^ 2 - Vp ^ 2) /\
--       E.B = 4 * Up ^ 2 + Vp ^ 2
```

Construction:

* If the larger B-parameter `r` is even and `s` is odd, prove `r = 2*Up` with `0<Up`; since `2*A=r*s` and `A` is even while `s` is odd, prove `Even Up`. Set `Vp=s`, `epsB=1`.
* If `r` is odd and `s` is even, prove `s = 2*Up` with `0<Up`; since `2*A=r*s` and `A` is even while `r` is odd, prove `Even Up`. Set `Vp=r`, `epsB=-1`.

The small divisibility lemma needed here is:

```lean
-- theorem half_even_parameter_even
--     {A R S : Int}
--     (hAeven : Even A) (hRS : 2 * A = R * S)
--     (hSeven : Even R) (hSodd : Odd S) :
--     exists Up : Int, 0 < Up /\ Even Up /\ R = 2 * Up
```

You may want two versions, one for the even factor on the left and one with the even factor on the right. Mathematically: `A` even implies `4 | 2*A = R*S`; if `S` is odd, then `4 | R`; hence `R/2` is even.

## 5. Factorization refinement theorem

I do not know of a ready-made Mathlib theorem that gives this exact 2-by-2 refinement with parity. Mathlib has all the ingredients (`Nat.gcd`, `Nat.Coprime`, UFD/prime-factor arguments), but this should be isolated as a project residual or proved once over `Nat` and wrapped for positive `Int`.

Recommended project residual over positive `Int`:

```lean
-- RESIDUAL: two coprime factorizations, parity-specialized.
-- theorem two_coprime_factorizations_refine_even_odd_int
--     {A U V Up Vp : Int}
--     (hApos : 0 < A)
--     (hUpos : 0 < U) (hVpos : 0 < V)
--     (hUppos : 0 < Up) (hVppos : 0 < Vp)
--     (hUV : A = U * V) (hUpVp : A = Up * Vp)
--     (hcopUV : IsCoprime U V) (hcopUpVp : IsCoprime Up Vp)
--     (hUeven : Even U) (hUpeven : Even Up)
--     (hVodd : Odd V) (hVpodd : Odd Vp) :
--     exists a b c d : Int,
--       0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
--       U = 2 * a * b /\ V = c * d /\
--       Up = 2 * a * c /\ Vp = b * d /\
--       IsCoprime a d /\ IsCoprime b c /\
--       Odd b /\ Odd c /\ Odd d
```

A cleaner proof target is the Nat core:

```lean
-- RESIDUAL/core: no signs, no parity.
-- theorem two_coprime_factorizations_refine_nat
--     {A U V Up Vp : Nat}
--     (hUV : A = U * V) (hUpVp : A = Up * Vp)
--     (hcopUV : Nat.Coprime U V)
--     (hcopUpVp : Nat.Coprime Up Vp) :
--     exists alpha beta gamma delta : Nat,
--       U = alpha * beta /\ V = gamma * delta /\
--       Up = alpha * gamma /\ Vp = beta * delta
```

Then the parity-specialized `Int` wrapper observes:

* `V,Vp` odd force `beta,gamma,delta` odd.
* `U,Up` even force `alpha` even.
* Write `alpha = 2*a`; then rename `beta=b`, `gamma=c`, `delta=d`.

Suggested proof of the Nat core: use prime valuations or define the four corners by gcds

```text
alpha = gcd U Up,
beta  = gcd U Vp,
gamma = gcd V Up,
delta = gcd V Vp,
```

and prove the four equations with `Nat.Coprime` cancellation. This is a small project lemma, not a paper-scale residual.

## 6. Same-orientation theorem

After obtaining signed parameters and the refinement, prove `epsC = epsB`. This is the key obstruction check.

```lean
-- theorem same_orientation_of_refined_signed_params
--     {a b c d epsC epsB : Int}
--     (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
--     (hbodd : Odd b) (hcodd : Odd c) (hdodd : Odd d)
--     (hepsC : epsC = 1 \/ epsC = -1)
--     (hepsB : epsB = 1 \/ epsB = -1)
--     (hD : epsC * ((2 * a * b) ^ 2 - (c * d) ^ 2)
--         = epsB * (4 * (2 * a * c) ^ 2 - (b * d) ^ 2)) :
--     epsC = epsB
```

Proof idea: case-split on `epsC, epsB`. If the signs differ, `ring_nf` gives

```text
4*a^2*(b^2 + 4*c^2) = d^2*(b^2 + c^2).
```

Modulo `4`, the left side is `0`, while the right side is `2`, because `b,c,d` are odd. Contradiction. Therefore the signs are equal.

This is the shortest reliable way to prove same orientation. It also explains why the route is not merely assuming the desired orientation.

## 7. Balance equation after same orientation

Once `epsC = epsB`, the balance is pure algebra.

```lean
-- theorem balance_of_refined_same_orientation
--     {a b c d eps : Int}
--     (heps : eps = 1 \/ eps = -1)
--     (hD : eps * ((2 * a * b) ^ 2 - (c * d) ^ 2)
--         = eps * (4 * (2 * a * c) ^ 2 - (b * d) ^ 2)) :
--     b ^ 2 * (4 * a ^ 2 + d ^ 2)
--       = c ^ 2 * (16 * a ^ 2 + d ^ 2)
```

Proof: case on `heps`; both cases reduce by `ring_nf` / `nlinarith` to the same identity.

Expanded algebra:

```text
(2ab)^2 - (cd)^2 = 4*(2ac)^2 - (bd)^2
4a^2b^2 - c^2d^2 = 16a^2c^2 - b^2d^2
b^2*(4a^2+d^2) = c^2*(16a^2+d^2).
```

## 8. Final step outside this request, but do not forget

To build the smaller Euler pair `F=(a,d,b,c)`, the balance equation must be combined with square-factor extraction:

```text
b^2*(4*a^2+d^2) = c^2*(16*a^2+d^2)
```

The extraction lemma needs cofactor coprimality:

```text
IsCoprime (4*a^2+d^2) (16*a^2+d^2).
```

Also `F.hAeven` is not automatic from the refinement alone; prove it from

```text
c^2 = 4*a^2+d^2,  Odd d.
```

If `a` were odd, the right side would be `5 mod 8`, impossible for a square. Isolate this as a small `ZMod 8` lemma.

## 9. Recommended theorem DAG

1. `gcd_D_twoA_eq_one`, `gcd_D_fourA_eq_one`, `D_mod_two_eq_one`.
2. `pythagorean_D_twoA_C`, `pythagorean_D_fourA_B`.
3. Use Mathlib `PythagoreanTriple.coprime_classification'`.
4. `C_larger_smaller_params`, `B_larger_smaller_params`.
5. `C_signed_even_odd_params`, `B_signed_even_odd_params`.
6. `two_coprime_factorizations_refine_nat` as a project core lemma.
7. `two_coprime_factorizations_refine_even_odd_int` as the Euler-facing wrapper.
8. `same_orientation_of_refined_signed_params` by mod `4`.
9. `balance_of_refined_same_orientation` by algebra.
10. Then continue with cofactor coprimality, square-factor balance, `F=(a,d,b,c)`, and product descent.

## Bottom line

Use Mathlib for primitive Pythagorean parametrization, but do not force the even parameter to be the larger one. The Lean-safe route is:

```text
Mathlib larger/smaller params
 -> signed even/odd params
 -> refine A=U*V=Up*Vp into U=2ab,V=cd,Up=2ac,Vp=bd
 -> prove signs equal by mod 4
 -> derive the balance identity.
```

There is no apparent mathematical falsehood in steps 1--4, but there are two hidden Lean traps: the same-orientation proof must not be assumed, and the final smaller-pair construction still needs cofactor coprimality plus the `a`-even mod-8 lemma.
