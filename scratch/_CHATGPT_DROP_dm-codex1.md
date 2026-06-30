# Q2603: `PrimitiveCenteredFourSqAP → EulerSquarePair` theorem DAG

Target file:

```text
FLT/Assumptions/MazurProof/N12FourSquaresAP.lean
```

Target namespace:

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair
```

The safe route is exactly the classical route in the prompt, but it should be split into three genuine interfaces plus AP-specific local gcd/parity lemmas:

```text
PrimitiveCenteredFourSqAP S
  -> primitive Pythagorean triple
       (16*N^2)^2 + Y^2 = (X^2 - 20*N^2)^2
  -> u,v with 16*N^2 = 4*u*v and X^2 - 20*N^2 = 4*u^2 + v^2
  -> square extraction u=4*A^2, v=D^2, N=A*D
  -> X^2 = (16*A^2+D^2)*(4*A^2+D^2)
  -> coprime factor square extraction gives B,C.
```

The important warning is that the Pythagorean and coprime-product square-extraction lemmas are the genuine reusable residuals unless your current Mathlib/project already has them.  The AP-specific gcd facts should be local lemmas.

---

## 0. Local notation

Introduce this local abbreviation if it is not already present:

```lean
namespace PrimitiveCenteredFourSqAP

def Y (S : PrimitiveCenteredFourSqAP) : ℤ :=
  S.p * S.q * S.r * S.s

end PrimitiveCenteredFourSqAP
```

Use `S.Y` below for readability.

---

## 1. AP identities and positivity needed for the big triple

These are local, routine `ring`/`nlinarith` lemmas.

```lean
/-- Difference identity from the centered equations. -/
lemma q_sq_sub_p_sq_eq_fourN (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 - S.p ^ 2 = 4 * S.N

/-- Difference identity from the centered equations. -/
lemma r_sq_sub_q_sq_eq_fourN (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 2 - S.q ^ 2 = 4 * S.N

/-- Difference identity from the centered equations. -/
lemma s_sq_sub_r_sq_eq_fourN (S : PrimitiveCenteredFourSqAP) :
    S.s ^ 2 - S.r ^ 2 = 4 * S.N

/-- Odd-root fields imply the roots are nonzero. -/
lemma p_ne_zero (S : PrimitiveCenteredFourSqAP) : S.p ≠ 0
lemma q_ne_zero (S : PrimitiveCenteredFourSqAP) : S.q ≠ 0
lemma r_ne_zero (S : PrimitiveCenteredFourSqAP) : S.r ≠ 0
lemma s_ne_zero (S : PrimitiveCenteredFourSqAP) : S.s ≠ 0

/-- The left endpoint value is positive, so `X > 6*N`. -/
lemma sixN_lt_X (S : PrimitiveCenteredFourSqAP) :
    6 * S.N < S.X

/-- Therefore the big hypotenuse `X^2 - 20*N^2` is positive. -/
lemma bigHyp_pos (S : PrimitiveCenteredFourSqAP) :
    0 < S.X ^ 2 - 20 * S.N ^ 2
```

Proof hints:

* `p_ne_zero`: from `S.p % 2 = 1`; if `S.p = 0`, then `0 % 2 = 0`.
* `sixN_lt_X`: rewrite `S.hp`; `0 < S.p^2` because `p ≠ 0`; then `nlinarith`.
* `bigHyp_pos`: from `0 < S.N` and `6N < X`, get `X^2 > 36N^2`, hence `X^2 - 20N^2 > 0`.

The big triple identity itself:

```lean
lemma big_pythagorean_identity (S : PrimitiveCenteredFourSqAP) :
    (S.Y) ^ 2 + (16 * S.N ^ 2) ^ 2 =
      (S.X ^ 2 - 20 * S.N ^ 2) ^ 2
```

Proof hint: expand `S.Y^2` as the product of the four centered square values:

```text
Y^2 = p^2*q^2*r^2*s^2
    = (X-6N)(X-2N)(X+2N)(X+6N)
    = (X^2 - 36N^2)(X^2 - 4N^2).
```

Then `ring` closes:

```text
(X^2 - 36N^2)(X^2 - 4N^2) + (16N^2)^2
= (X^2 - 20N^2)^2.
```

---

## 2. Primitive gcd of the big triple

Goal:

```lean
lemma bigLeg_coprime_Y (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (16 * S.N ^ 2) S.Y
```

Do this with local lemmas, not inside the Pythagorean theorem.

### 2.1 Oddness of `Y` and coprimality with powers of `2`

```lean
lemma p_odd (S : PrimitiveCenteredFourSqAP) : Odd S.p
lemma q_odd (S : PrimitiveCenteredFourSqAP) : Odd S.q
lemma r_odd (S : PrimitiveCenteredFourSqAP) : Odd S.r
lemma s_odd (S : PrimitiveCenteredFourSqAP) : Odd S.s

lemma Y_odd (S : PrimitiveCenteredFourSqAP) : Odd S.Y

lemma sixteen_coprime_Y (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (16 : ℤ) S.Y
```

Proof hints:

* `p_odd`: `Int.odd_iff.mpr S.hp_odd` if the field is `S.hp_odd : S.p % 2 = 1`.
* `Y_odd`: repeated `Odd.mul`.
* `sixteen_coprime_Y`: use the local helper from Q2576, or prove Bezout from oddness; orientation can be fixed with `.symm`.

### 2.2 `N` is coprime to each root

State the four root lemmas explicitly:

```lean
lemma N_coprime_p (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.p

lemma N_coprime_q (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.q

lemma N_coprime_r (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.r

lemma N_coprime_s (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.s
```

Proof pattern for `N_coprime_p`:

* Use a prime-divisor criterion for `Int.gcd = 1`/`IsCoprime`.
* If a natural prime `ℓ` divides both `N` and `p`, then from

```text
p^2 = X - 6N
```

  it divides `X`.
* Then from

```text
q^2 = X - 2N,
r^2 = X + 2N,
s^2 = X + 6N
```

  it divides `q^2,r^2,s^2`, hence `q,r,s` by primality.
* This contradicts any pairwise root gcd field, for example `Int.gcd p q = 1`.

The same proof works for `q,r,s`: a prime dividing `N` and one root divides `X`, hence all roots.

Useful local criterion if not already present:

```lean
/-- Prime-divisor criterion for proving integer Bezout coprimality. -/
lemma isCoprime_int_of_no_common_nat_prime
    {a b : ℤ}
    (hno : ∀ ℓ : ℕ, Nat.Prime ℓ →
      (ℓ : ℤ) ∣ a → (ℓ : ℤ) ∣ b → False) :
    IsCoprime a b
```

This is a local lemma; it is small and often easier than fighting `Int.gcd` APIs.

### 2.3 `N` is coprime to `Y`, hence `16*N^2` is coprime to `Y`

```lean
lemma N_coprime_Y (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.Y

lemma Nsq_coprime_Y (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (S.N ^ 2) S.Y

lemma bigLeg_coprime_Y (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (16 * S.N ^ 2) S.Y
```

Proof hints:

* `N_coprime_Y`: combine `N_coprime_p/q/r/s` using `IsCoprime.mul_right`, or use the direct Bezout helper `isCoprime_mul_right_int` from Q2576 repeatedly.
* `Nsq_coprime_Y`: either `h.pow_left` if available, or use `isCoprime_mul_left` with `N_coprime_Y` twice.
* `bigLeg_coprime_Y`: combine `sixteen_coprime_Y` and `Nsq_coprime_Y` on the left; if orientation is awkward, prove the product version with direct Bezout.

This proves the primitive input for the Pythagorean step.

---

## 3. Primitive Pythagorean parametrization interface

This should be isolated as a genuine reusable theorem.  Do **not** bury it in AP code.

### Residual theorem signature

```lean
/--
Primitive Pythagorean parametrization in the form needed here.
The first leg `a` is the even leg; `b` is the odd leg.
Only `a = 4*u*v` and `c = 4*u^2+v^2` are needed downstream.
-/
theorem primitive_pythagorean_even_leg_four_param_int
    {a b c : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hbOdd : Odd b)
    (hab : IsCoprime a b)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2) :
    ∃ u v : ℤ,
      0 < u ∧ 0 < v ∧
      Odd v ∧
      IsCoprime (2 * u) v ∧
      a = 4 * u * v ∧
      c = 4 * u ^ 2 + v ^ 2
```

For the AP, apply it with:

```text
a = 16*S.N^2
b = |S.Y|
c = S.X^2 - 20*S.N^2
```

Inputs:

```lean
lemma bigLeg_pos (S : PrimitiveCenteredFourSqAP) :
    0 < 16 * S.N ^ 2

lemma Y_abs_pos (S : PrimitiveCenteredFourSqAP) :
    0 < |S.Y|

lemma absY_odd (S : PrimitiveCenteredFourSqAP) :
    Odd |S.Y|

lemma bigLeg_coprime_absY (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (16 * S.N ^ 2) |S.Y|
```

`absY_odd` and `bigLeg_coprime_absY` are harmless wrappers around `Y_odd` and `bigLeg_coprime_Y`.

After parametrization, normalize the result as:

```text
16*N^2 = 4*u*v,
X^2 - 20*N^2 = 4*u^2 + v^2,
0<u, 0<v, Odd v, IsCoprime (2*u) v.
```

Then cancel `4`:

```lean
lemma uv_eq_four_N_sq_of_big_leg
    {N u v : ℤ}
    (h : 16 * N ^ 2 = 4 * u * v) :
    u * v = 4 * N ^ 2
```

Proof hint: `nlinarith` or `ring_nf` plus integral-domain cancellation by `4`.  Because this is over `ℤ`, `nlinarith` usually closes it.

---

## 4. Extracting `A,D` from `u*v = 4*N^2`

This is the second genuine reusable interface.  State it over positive integers to avoid sign ambiguity.

### AP parity needed for `A` even

First prove locally:

```lean
lemma N_even_of_primitive_centered (S : PrimitiveCenteredFourSqAP) :
    Even S.N
```

Proof hint: from `q^2 - p^2 = 4*N` and `p,q` odd.  Odd squares are congruent to `1 mod 8`, hence `8 ∣ q^2-p^2`, hence `2 ∣ N`.

A small reusable lemma is useful:

```lean
lemma odd_sq_sub_odd_sq_dvd_eight
    {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ b ^ 2 - a ^ 2
```

Then combine with `q_sq_sub_p_sq_eq_fourN`.

### Residual theorem signature

```lean
/--
Coprime square extraction specialized to `u*v = 4*N^2`.
The positivity hypotheses are essential; without them the signs of `A,D` are ambiguous.
-/
theorem extract_AD_of_coprime_uv_eq_four_square
    {u v N : ℤ}
    (hu : 0 < u)
    (hv : 0 < v)
    (hN : 0 < N)
    (hNeven : Even N)
    (hvOdd : Odd v)
    (huv_cop : IsCoprime u v)
    (huv : u * v = 4 * N ^ 2) :
    ∃ A D : ℤ,
      0 < A ∧ 0 < D ∧
      Even A ∧ Odd D ∧
      IsCoprime A D ∧
      u = 4 * A ^ 2 ∧
      v = D ^ 2 ∧
      N = A * D
```

Proof route:

1. Convert to `Nat` using positivity.
2. Use the natural theorem “coprime factors of a square are squares”:

```lean
/-- Local residual if Mathlib does not have the exact theorem. -/
theorem Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
    {x y z : ℕ}
    (hcop : x.Coprime y)
    (h : x * y = z ^ 2) :
    ∃ r s : ℕ, x = r ^ 2 ∧ y = s ^ 2
```

3. Apply it to `u*v = (2*N)^2`.
4. Get `u=U^2`, `v=D^2`, and from positivity get `U*D = 2*N`.
5. Since `v` is odd, `D` is odd.
6. From `U*D = 2*N` and `D` odd, get `U=2*A` and `N=A*D`.
7. From `N` even and `D` odd, get `A` even.
8. From `IsCoprime u v`, get `IsCoprime U D`, hence `IsCoprime A D`.

Do not claim `u=4*A^2` without the positivity and parity steps above; that is where sign mistakes usually enter.

For the Pythagorean output you have `IsCoprime (2*u) v`; derive the required `IsCoprime u v` by stripping the left factor:

```lean
lemma isCoprime_of_two_mul_left
    {u v : ℤ} (h : IsCoprime (2 * u) v) :
    IsCoprime u v
```

Proof hint: if `a*(2u)+b*v=1`, then `(2a)*u+b*v=1`.

---

## 5. Deriving the Euler factor product

After extracting `A,D`, you have:

```text
N = A*D,
u = 4*A^2,
v = D^2,
X^2 - 20*N^2 = 4*u^2 + v^2.
```

The ring lemma should be local:

```lean
lemma center_square_eq_euler_factor_product
    {X N u v A D : ℤ}
    (hN : N = A * D)
    (hu : u = 4 * A ^ 2)
    (hv : v = D ^ 2)
    (hc : X ^ 2 - 20 * N ^ 2 = 4 * u ^ 2 + v ^ 2) :
    X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)
```

Proof hint: substitute and `ring`/`nlinarith`.

---

## 6. Coprimality of the two Euler factors

This is local, not a global residual.

```lean
/-- The two Euler factors are coprime. -/
lemma euler_factors_coprime
    {A D : ℤ}
    (hAD : IsCoprime A D)
    (hDodd : Odd D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2)
```

Proof hint using the factor-coprime style already in the file:

* Let

```text
F = 16*A^2 + D^2,
G = 4*A^2 + D^2.
```

* A common divisor of `F,G` divides:

```text
F - G = 12*A^2,
4*G - F = 3*D^2.
```

* Use `IsCoprime A D` to eliminate common odd primes not dividing `12`.
* `D` odd makes both `F,G` odd, excluding `2`.
* Exclude `3` by the mod-3 square check:

```text
F ≡ A^2 + D^2 (mod 3),
G ≡ A^2 + D^2 (mod 3).
```

If `3` divided a common factor, then `A^2 + D^2 ≡ 0 mod 3`, which forces `3∣A` and `3∣D`, contradicting `IsCoprime A D`.

Useful local sublemmas:

```lean
lemma euler_factor_left_odd {A D : ℤ} (hDodd : Odd D) :
    Odd (16 * A ^ 2 + D ^ 2)

lemma euler_factor_right_odd {A D : ℤ} (hDodd : Odd D) :
    Odd (4 * A ^ 2 + D ^ 2)

lemma three_not_dvd_euler_factor_left
    {A D : ℤ} (hAD : IsCoprime A D) :
    ¬ (3 : ℤ) ∣ 16 * A ^ 2 + D ^ 2

lemma three_not_dvd_euler_factor_right
    {A D : ℤ} (hAD : IsCoprime A D) :
    ¬ (3 : ℤ) ∣ 4 * A ^ 2 + D ^ 2
```

The `3` lemmas can be proved by `ZMod 3` or by integer `% 3`; `ZMod 3` is usually cleaner.

---

## 7. Square extraction into positive `B,C`

This is the third reusable square-extraction interface.  It can be proved from the same `Nat.exists_sq_and_sq_of_coprime_mul_eq_sq` theorem.

```lean
/-- Positive integer square extraction from a coprime product equal to a square. -/
theorem Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    {x y z : ℤ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy : IsCoprime x y)
    (h : z ^ 2 = x * y) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧
      r ^ 2 = x ∧ s ^ 2 = y
```

Then specialize it:

```lean
lemma euler_factor_left_pos {A D : ℤ} (hDpos : 0 < D) :
    0 < 16 * A ^ 2 + D ^ 2

lemma euler_factor_right_pos {A D : ℤ} (hDpos : 0 < D) :
    0 < 4 * A ^ 2 + D ^ 2

lemma extract_BC_from_center_square
    {X A D : ℤ}
    (hApos : 0 < A)
    (hDpos : 0 < D)
    (hDodd : Odd D)
    (hAD : IsCoprime A D)
    (hX : X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    ∃ B C : ℤ,
      0 < B ∧ 0 < C ∧
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2
```

Proof hint:

* `hcop := euler_factors_coprime hAD hDodd`.
* Apply `Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime` to `hX`.
* The order of `x,y` should match the desired fields: `B` for `16*A^2+D^2`, `C` for `4*A^2+D^2`.

---

## 8. Final assembly statement

Once the three residual interfaces are available, the actual target is just assembly.

```lean
/-- Final assembly from a primitive centered AP to an Euler square pair. -/
theorem primitiveCenteredToEulerSquarePair_constructive
    (S : PrimitiveCenteredFourSqAP) :
    ∃ E : EulerSquarePair, S.N = E.A * E.D
```

Proof outline:

1. Set

```text
a = 16*S.N^2,
b = |S.Y|,
c = S.X^2 - 20*S.N^2.
```

2. Apply `primitive_pythagorean_even_leg_four_param_int` using:

```text
big_pythagorean_identity,
bigLeg_pos,
Y_abs_pos,
bigHyp_pos,
absY_odd,
bigLeg_coprime_absY.
```

Get `u,v` with:

```text
16*N^2 = 4*u*v,
X^2 - 20*N^2 = 4*u^2 + v^2,
0<u, 0<v, Odd v, IsCoprime (2*u) v.
```

3. Cancel `4` to get `u*v = 4*N^2`.

4. Apply `extract_AD_of_coprime_uv_eq_four_square` using:

```text
0<u, 0<v, 0<N,
N_even_of_primitive_centered S,
Odd v,
IsCoprime u v,
u*v = 4*N^2.
```

Get:

```text
0<A, 0<D, Even A, Odd D, IsCoprime A D,
u = 4*A^2, v = D^2, N = A*D.
```

5. Use `center_square_eq_euler_factor_product` to get:

```text
X^2 = (16*A^2 + D^2)*(4*A^2 + D^2).
```

6. Apply `extract_BC_from_center_square` to get positive `B,C` satisfying the two Euler equations.

7. Build:

```lean
⟨{
  A := A
  D := D
  B := B
  C := C
  hApos := hApos
  hDpos := hDpos
  hDodd := hDodd
  hAeven := hAeven
  hADcop := hADcop
  hBpos := hBpos
  hCpos := hCpos
  hB := hB
  hC := hC
}, by simpa [hN]⟩
```

where `hN : S.N = A*D`.

---

## 9. What should be residual versus local

### Genuine residuals if Mathlib/project lacks them

These are mathematically standard but nontrivial enough to isolate:

```lean
primitive_pythagorean_even_leg_four_param_int
Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
extract_AD_of_coprime_uv_eq_four_square
```

The `Int` square extraction and `extract_AD` can both be built from the `Nat` lemma, so the true primitive residual is often just:

```lean
Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
```

plus the Pythagorean parametrization.

### Local AP/Euler lemmas

These should be proved in `N12FourSquaresAP.lean` near the current helper layer:

```lean
big_pythagorean_identity
bigLeg_coprime_Y
N_even_of_primitive_centered
euler_factors_coprime
center_square_eq_euler_factor_product
extract_BC_from_center_square
```

None of these should require new axioms or classical number theory beyond prime-divisor bookkeeping, mod 8/mod 3 arithmetic, and the coprime square-product theorem.
