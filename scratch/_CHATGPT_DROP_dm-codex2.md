# Q2536 PrimitiveCenteredFourSqAP descent construction

## Executive summary

The clean classical descent is not a direct formula for the new roots as simple
polynomials in `S.p,S.q,S.r,S.s`.  The robust route is through an auxiliary
Euler square-pair:

```text
4*A^2 + D^2  is a square,
16*A^2 + D^2 is a square,
A > 0, D > 0, gcd(A,D)=1, D odd, A even.
```

From a primitive centered four-square AP with `S.N = N > 0`, one constructs such
an `(A,D)` with

```text
N = A*D.
```

Then the pair `(A,D)` descends to a new pair `(a,d)` satisfying the same two-square
conditions and

```text
a*d < A*D = N.
```

Finally, any such descended pair `(a,d)` reconstructs a primitive centered AP
with

```text
T.N = a*d,
T.X = B*C,
```

where

```text
B^2 = 16*a^2 + d^2,
C^2 =  4*a^2 + d^2.
```

The roots of `T` are not best written as closed polynomial expressions; they are
obtained as the square roots of the four coprime square factors

```text
B*C - 6*a*d,
B*C - 2*a*d,
B*C + 2*a*d,
B*C + 6*a*d.
```

This is the construction to formalize.  It gives the required strict decrease
`T.N.natAbs < S.N.natAbs` because `T.N = a*d > 0` and `S.N = A*D > 0`.

## 1. From centered AP to the Euler pair `(A,D)`

Let

```text
N = S.N,
X = S.X,
y = S.p*S.q*S.r*S.s,
H = X^2 - 20*N^2.
```

The key identity is

```text
H^2 = y^2 + (16*N^2)^2.
```

Lean algebra target:

```lean
theorem centered_big_pyth_identity (S : PrimitiveCenteredFourSqAP) :
    (S.X ^ 2 - 20*S.N ^ 2) ^ 2 =
      (S.p*S.q*S.r*S.s) ^ 2 + (16*S.N ^ 2) ^ 2 := by
  have hps : (S.p*S.s) ^ 2 = S.X ^ 2 - (6*S.N) ^ 2 := by
    calc
      (S.p*S.s) ^ 2 = S.p ^ 2 * S.s ^ 2 := by ring
      _ = (S.X - 6*S.N) * (S.X + 6*S.N) := by rw [S.hp, S.hs]
      _ = S.X ^ 2 - (6*S.N) ^ 2 := by ring
  have hqr : (S.q*S.r) ^ 2 = S.X ^ 2 - (2*S.N) ^ 2 := by
    calc
      (S.q*S.r) ^ 2 = S.q ^ 2 * S.r ^ 2 := by ring
      _ = (S.X - 2*S.N) * (S.X + 2*S.N) := by rw [S.hq, S.hr]
      _ = S.X ^ 2 - (2*S.N) ^ 2 := by ring
  calc
    (S.X ^ 2 - 20*S.N ^ 2) ^ 2 - (16*S.N ^ 2) ^ 2
        = (S.X ^ 2 - (6*S.N)^2) * (S.X ^ 2 - (2*S.N)^2) := by ring
    _ = (S.p*S.s)^2 * (S.q*S.r)^2 := by rw [← hps, ← hqr]
    _ = (S.p*S.q*S.r*S.s)^2 := by ring
  -- Rearrange the displayed subtraction identity to the theorem statement.
  -- `nlinarith` closes after naming the calc result.
```

For Lean, write the final proof as:

```lean
  have hsub :
      (S.X ^ 2 - 20*S.N ^ 2) ^ 2 - (16*S.N ^ 2) ^ 2 =
        (S.p*S.q*S.r*S.s)^2 := by
    calc
      (S.X ^ 2 - 20*S.N ^ 2) ^ 2 - (16*S.N ^ 2) ^ 2
          = (S.X ^ 2 - (6*S.N)^2) * (S.X ^ 2 - (2*S.N)^2) := by ring
      _ = (S.p*S.s)^2 * (S.q*S.r)^2 := by rw [← hps, ← hqr]
      _ = (S.p*S.q*S.r*S.s)^2 := by ring
  nlinarith
```

Side conditions needed for the primitive Pythagorean classification:

```text
y is odd,
gcd(y, N)=1,
gcd(y, 16*N^2)=1.
```

The gcd facts are not optional.  They follow from pairwise coprimality of the
roots plus the centered equations: if a prime `ℓ` divides one root and `N`, then
it divides `X`, hence all four root squares, hence all four roots, contradicting
`rootGCD4=1` or the pairwise gcd fields.

A good Lean target is:

```lean
theorem centered_root_product_coprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (S.p*S.q*S.r*S.s) S.N := by
  -- prime-divisor proof using S.hp,S.hq,S.hr,S.hs and pairwise gcd/root gcd fields
  -- this is a genuine number-theory helper, not algebra.
```

Then classify the primitive Pythagorean triple

```text
(16*N^2)^2 + y^2 = H^2.
```

Because the even leg is `16*N^2`, use the parametrization

```text
4*u*v = 16*N^2,
y = ±(4*u^2 - v^2),
|H| = 4*u^2 + v^2,
gcd(2*u, v)=1,
v odd.
```

Since

```text
u*v = 4*N^2,
gcd(u,v)=1,
v odd,
```

we get

```text
u = 4*A^2,
v = D^2,
A > 0,
D > 0,
D odd,
gcd(A,D)=1,
N = A*D.
```

Substituting into `|H| = 4*u^2 + v^2` gives

```text
|H| = 64*A^4 + D^4.
```

But also

```text
X^2 = (64*A^4 + D^4) + 20*A^2*D^2
    = (16*A^2 + D^2) * (4*A^2 + D^2).
```

The two factors are coprime under `gcd(A,D)=1`, `D` odd, and `A` even.  Hence
both are squares.  This is the first Euler pair:

```text
∃ B C,
  B^2 = 16*A^2 + D^2,
  C^2 =  4*A^2 + D^2.
```

Package this as:

```lean
structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16*A ^ 2 + D ^ 2
  hC : C ^ 2 = 4*A ^ 2 + D ^ 2

theorem primitiveCentered_to_eulerSquarePair
    (S : PrimitiveCenteredFourSqAP) :
    ∃ E : EulerSquarePair, S.N = E.A * E.D := by
  -- Use the large Pythagorean identity and primitive classification above.
```

`hAeven` follows from the already checked parity lemma: the common difference is
`4*N`, and primitive odd AP gives `(8 : ℤ) ∣ 4*N`, so `Even N`; since `D` is odd
and `N=A*D`, `A` is even.

## 2. Descent of an Euler square-pair

Assume an Euler pair

```text
C^2 = 4*A^2 + D^2,
B^2 = 16*A^2 + D^2,
A even,
D odd,
gcd(A,D)=1.
```

The first equation is a primitive Pythagorean triple with legs `D` and `2*A`:

```text
D^2 + (2*A)^2 = C^2.
```

The second is a primitive Pythagorean triple with legs `D` and `4*A`:

```text
D^2 + (4*A)^2 = B^2.
```

Classify both:

```text
A = U*V,
D = ε*(U^2 - V^2),
C = U^2 + V^2,
gcd(U,V)=1,
U even, V odd;

A = U'*V',
D = ε*(4*U'^2 - V'^2),
B = 4*U'^2 + V'^2,
gcd(U',V')=1,
U' even, V' odd.
```

The same sign `ε` can be arranged by choosing the sign of `D` once and orienting
the odd legs.  This sign alignment is the only delicate bookkeeping point in the
formal proof.

Now refine the two coprime factorizations of the even integer `A`:

```text
A = U*V = U'*V',
U even, V odd, U' even, V' odd,
gcd(U,V)=gcd(U',V')=1.
```

Use the Q2450 common-refinement lemma:

```text
U  = 2*a*b,
V  = c*d,
U' = 2*a*c,
V' = b*d,
A  = 2*a*b*c*d,
```

with

```text
a,b,c,d > 0,
d odd,
pairwise coprime among 2*a, b, c, d.
```

Substitute into the two signed odd-leg formulas:

```text
ε*D = 4*a^2*b^2 - c^2*d^2,
ε*D = 16*a^2*c^2 - b^2*d^2.
```

Equating them gives the exact balance identity:

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2).
```

Lean algebra target:

```lean
theorem euler_refinement_balance
    {a b c d D : ℤ}
    (hD1 : D = 4*a^2*b^2 - c^2*d^2)
    (hD2 : D = 16*a^2*c^2 - b^2*d^2) :
    b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2) := by
  nlinarith
```

Using pairwise coprimality, prove the two cofactors are coprime:

```text
gcd(4*a^2 + d^2, 16*a^2 + d^2) = 1.
```

Then square-balance gives

```text
4*a^2 + d^2  is a square,
16*a^2 + d^2 is a square.
```

The strongest Lean target is:

```lean
theorem eulerSquarePair_descent
    (E : EulerSquarePair) :
    ∃ F : EulerSquarePair, F.A * F.D < E.A * E.D := by
  -- F.A := a, F.D := d.
  -- F.C^2 = 4*a^2 + d^2, F.B^2 = 16*a^2 + d^2 from square-balance.
```

The strict inequality is immediate from the refinement:

```text
E.A = 2*a*b*c*d,
F.A*F.D = a*d,
```

and `b,c ≥ 1`, so

```text
a*d < 2*a*b*c*d = E.A ≤ E.A*E.D.
```

The last inequality uses `E.D ≥ 1`.  In Lean:

```lean
have hb1 : 1 ≤ b := by omega
have hc1 : 1 ≤ c := by omega
have hD1 : 1 ≤ E.D := by omega
nlinarith [hAeq]  -- hAeq : E.A = 2*a*b*c*d
```

## 3. Reconstructing a centered primitive AP from an Euler pair

Given an Euler pair `(A,D,B,C)` with

```text
B^2 = 16*A^2 + D^2,
C^2 =  4*A^2 + D^2,
```

set

```text
X := B*C,
N := A*D.
```

Then the key identities are:

```text
X^2 - (2*N)^2 = (D^2 + 8*A^2)^2,
X^2 - (6*N)^2 = (D^2 - 8*A^2)^2.
```

Lean algebra:

```lean
theorem eulerPair_middle_product_square
    {A D B C : ℤ}
    (hB : B^2 = 16*A^2 + D^2)
    (hC : C^2 = 4*A^2 + D^2) :
    (B*C)^2 - (2*(A*D))^2 = (D^2 + 8*A^2)^2 := by
  nlinarith [hB, hC]

theorem eulerPair_outer_product_square
    {A D B C : ℤ}
    (hB : B^2 = 16*A^2 + D^2)
    (hC : C^2 = 4*A^2 + D^2) :
    (B*C)^2 - (6*(A*D))^2 = (D^2 - 8*A^2)^2 := by
  nlinarith [hB, hC]
```

Equivalently:

```text
(B*C - 2*A*D)*(B*C + 2*A*D) = (D^2 + 8*A^2)^2,
(B*C - 6*A*D)*(B*C + 6*A*D) = (D^2 - 8*A^2)^2.
```

Under the Euler pair coprimality/parity hypotheses the two factors in each line
are positive and coprime, hence each factor is a square.  Therefore choose
integers `p,q,r,s` such that

```text
p^2 = B*C - 6*A*D,
q^2 = B*C - 2*A*D,
r^2 = B*C + 2*A*D,
s^2 = B*C + 6*A*D.
```

This is the exact centered AP reconstruction:

```lean
theorem eulerSquarePair_to_primitiveCentered
    (E : EulerSquarePair) :
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D ∧ T.X = E.B * E.C := by
  -- Use the two product-square identities plus coprime-factor-square lemmas.
  -- The roots are obtained existentially, not by polynomial formulas.
```

The pairwise gcd and oddness fields of `T` follow from the same coprime-factor
arguments and the facts `D` odd, `A` even, `gcd(A,D)=1`.  Keep this in one
reconstruction theorem rather than spreading it through the final descent proof.

## 4. Final descent assembly

With the three theorem families above, the final Lean proof is short:

```lean
theorem primitiveCenteredFourSqAP_descent :
    PrimitiveCenteredFourSqAPDescent := by
  intro S
  obtain ⟨E, hSN⟩ := primitiveCentered_to_eulerSquarePair S
  obtain ⟨F, hsmallEF⟩ := eulerSquarePair_descent E
  obtain ⟨T, hTN, hTX⟩ := eulerSquarePair_to_primitiveCentered F
  refine ⟨T, ?_⟩
  have hSpos : 0 < S.N := S.hNpos
  have hEpos : 0 < E.A * E.D := by nlinarith [E.hApos, E.hDpos]
  have hFpos : 0 < F.A * F.D := by nlinarith [F.hApos, F.hDpos]
  have hTNpos : 0 < T.N := T.hNpos
  -- `hSN : S.N = E.A*E.D`, `hTN : T.N = F.A*F.D`.
  -- Convert positive integer inequalities to natAbs inequalities.
  have hsmallZ : T.N < S.N := by nlinarith [hSN, hTN, hsmallEF]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hTNpos) hsmallZ
```

If `Int.natAbs_lt_natAbs_of_nonneg_of_lt` is not available in your Mathlib
snapshot, replace the last line by:

```lean
  have hTnat : T.N.natAbs = T.N.toNat := Int.natAbs_of_nonneg (le_of_lt hTNpos)
  have hSnat : S.N.natAbs = S.N.toNat := Int.natAbs_of_nonneg (le_of_lt hSpos)
  omega
```

or prove the tiny local lemma:

```lean
theorem int_natAbs_lt_natAbs_of_pos_lt {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (h : a < b) :
    a.natAbs < b.natAbs := by
  exact_mod_cast h
```

## Minimal honest residual list

For Lean, isolate the work into these theorem targets:

```lean
structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16*A ^ 2 + D ^ 2
  hC : C ^ 2 = 4*A ^ 2 + D ^ 2

theorem primitiveCentered_to_eulerSquarePair
    (S : PrimitiveCenteredFourSqAP) :
    ∃ E : EulerSquarePair, S.N = E.A * E.D

theorem eulerSquarePair_descent
    (E : EulerSquarePair) :
    ∃ F : EulerSquarePair, F.A * F.D < E.A * E.D

theorem eulerSquarePair_to_primitiveCentered
    (E : EulerSquarePair) :
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D ∧ T.X = E.B * E.C
```

Then `PrimitiveCenteredFourSqAPDescent` follows immediately.  This is the
classical Fermat/Euler descent translated into the current `(p,q,r,s,X,N)`
centered primitive form.
