# Q1972 (dm3): sign-parametric quartic descent for `eps = ±1`

## Setup

Write the primitive quartic as

```text
t^2 = s^4 + eps*D^2*s^2 - D^4,
```

where

```text
eps ∈ {+1, -1},    D > 0,    gcd(s,D) = 1.
```

The shared identity is exactly

```text
(2*s^2 + eps*D^2 - 2*t) * (2*s^2 + eps*D^2 + 2*t) = 5*D^4.
```

The `eps = +1` case is the N = 10 descent. The `eps = -1` case is the N = 16 descent.

The sign-parametric descent is real, but it should not be implemented as a blind textual replacement of `+D^2*s^2` by `eps*D^2*s^2`. There are three algebraic changes to account for.

## 1. Parity analysis

The parity analysis **does change** in the odd-denominator branch.

Let `D` be the original primitive denominator. Since `gcd(s,D)=1`, the following congruence facts are decisive.

### If `D` is odd

If `s` were even, then modulo `4` one gets

```text
t^2 ≡ -D^4 ≡ -1 ≡ 3  (mod 4),
```

which is impossible. Thus `s` is odd.

With `D` and `s` both odd, modulo `8` gives

```text
s^4 + eps*D^2*s^2 - D^4 ≡ 1 + eps - 1 ≡ eps  (mod 8).
```

So:

```text
eps = +1:  t^2 ≡ 1 (mod 8), allowed;
eps = -1:  t^2 ≡ -1 ≡ 7 (mod 8), impossible.
```

Therefore the odd-`D` branch exists only for N = 10. For N = 16, the odd-denominator branch is killed immediately by the mod-8 contradiction.

### If `D` is even

Then `s` is odd. If `D ≡ 2 (mod 4)`, then `D^2 ≡ 4 (mod 8)` and `D^4 ≡ 0 (mod 8)`, so

```text
t^2 ≡ 1 + eps*4  (mod 8).
```

For both signs this is

```text
1 + 4 ≡ 5 (mod 8),
1 - 4 ≡ -3 ≡ 5 (mod 8),
```

again impossible. Hence in the even branch one always has

```text
4 ∣ D.
```

### Practical conclusion for an existing N = 10 file

If your current file has lemmas of the form “`B` odd” versus “`B` even,” be careful about what `B` denotes.

If `B` is the original denominator, then:

```text
eps = +1, B odd: possible; prove numerator odd and continue.
eps = -1, B odd: impossible; close by mod 8.
B even, either sign: primitive numerator is odd and in fact 4 ∣ B.
```

If `B` is the half-denominator in the even branch, so `D = 2*B`, then for `eps = -1` this `B` is automatically even, because the original denominator satisfies `4 ∣ D`.

Thus N = 16 does **not** introduce a new odd-`B` descent branch. It removes the odd branch and leaves only the even normalized branch.

## 2. Coprime factorization structure

The coprime factorization structure is essentially unchanged, but the 2-adic normalization must be made explicit.

Define the raw factors

```text
L = 2*s^2 + eps*D^2 - 2*t,
R = 2*s^2 + eps*D^2 + 2*t.
```

Then

```text
L*R = 5*D^4.
```

### Odd branch

This branch occurs only for `eps = +1`. Here `D,s,t` are all odd, and `L,R` are odd. The usual prime-divisor argument shows

```text
gcd(L,R) = 1.
```

Then the factorization of a coprime product `5*D^4` gives the two cases

```text
L = a^4,      R = 5*b^4,     D = a*b,
```

or

```text
L = 5*a^4,    R = b^4,       D = a*b,
```

up to the harmless order/sign conventions fixed by positivity.

There is no corresponding odd branch for `eps = -1`.

### Even branch

Write

```text
D = 2*B.
```

In any primitive solution in the even branch, the parity analysis actually gives `B` even. The raw factors `L,R` are both divisible by `4`, so the useful normalized factors are

```text
U = L/4 = (s^2 + 2*eps*B^2 - t)/2,
V = R/4 = (s^2 + 2*eps*B^2 + t)/2.
```

They satisfy

```text
U*V = 5*B^4.
```

The same coprimality proof works for both signs:

```text
gcd(U,V) = 1.
```

The reason is unchanged. A common odd prime divisor of `U,V` divides their sum and difference, hence divides

```text
s^2 + 2*eps*B^2
```

and `t`; using the product identity and `gcd(s,D)=1`, no prime dividing `B` can occur, and the lone extra prime `5` can occur in only one coprime factor. The common factor `2` is also excluded because `U+V = s^2 + 2*eps*B^2` is odd when `s` is odd and `B` is even.

Thus the same fourth-power split applies:

```text
U = a^4,      V = 5*b^4,     B = a*b,
```

or

```text
U = 5*a^4,    V = b^4,       B = a*b.
```

### Where the sign actually appears

The sign appears in the next identity, after adding the two factor equations.

In the branch

```text
U = a^4,    V = 5*b^4,    B = a*b,
```

the even normalized sum gives

```text
s^2 + 2*eps*a^2*b^2 = a^4 + 5*b^4,
```

hence

```text
s^2 = a^4 - 2*eps*a^2*b^2 + 5*b^4
    = (a^2 - eps*b^2)^2 + 4*b^4.
```

So:

```text
eps = +1:  s^2 = (a^2 - b^2)^2 + 4*b^4;
eps = -1:  s^2 = (a^2 + b^2)^2 + 4*b^4.
```

The reversed factor case gives the symmetric formula

```text
s^2 = (b^2 - eps*a^2)^2 + 4*a^4.
```

This is the key algebraic edit for N = 16: the Pythagorean leg becomes `a^2 + b^2`, not `a^2 - b^2`. Positivity is easier in the negative-sign case, because `a^2 + b^2` is automatically positive.

## 3. Does the same descent return the same sign?

Yes. This is the main reason the sign-parametric file is feasible.

From the common post-factorization identity

```text
z^2 = (a^2 - eps*b^2)^2 + 4*b^4,
```

view this as a primitive Pythagorean triple with legs

```text
a^2 - eps*b^2,
2*b^2,
```

or, for `eps = -1`, legs

```text
a^2 + b^2,
2*b^2.
```

In the primitive parametrization, write

```text
b^2 = m*n,
gcd(m,n) = 1,
```

so, since `m*n` is a square and `m,n` are coprime,

```text
m = r^2,
n = h^2.
```

The other Pythagorean equation is

```text
a^2 - eps*b^2 = r^4 - h^4.
```

Since `b^2 = r^2*h^2`, this gives

```text
a^2 = r^4 + eps*r^2*h^2 - h^4.
```

That is exactly the same signed quartic again:

```text
a^2 = r^4 + eps*h^2*r^2 - h^4.
```

So the descent preserves `eps`.

For `eps = -1` this reads

```text
a^2 = r^4 - r^2*h^2 - h^4,
```

which is the N = 16 quartic again, with new solution

```text
(s', D', t') = (r, h, a)
```

up to whichever naming convention your file uses.

The reversed factor case gives the same statement with `a` and `b` interchanged.

## 4. Strong induction and descent variable

The strong induction still works with the same descent variable: the positive primitive denominator.

In the even branch, including all of N = 16, we first write

```text
D = 2*B,
```

and after normalized factorization obtain

```text
B = a*b.
```

The Pythagorean step gives

```text
b = r*h
```

in the first branch, with

```text
0 < h < b ≤ a*b = B < D.
```

Therefore the new denominator `h` is strictly smaller than the original denominator `D`. In fact it is smaller than the normalized denominator `B = D/2`.

So either of the following induction measures is valid:

```text
D.natAbs                  -- original primitive denominator;
B.natAbs = (D/2).natAbs   -- normalized even-branch denominator.
```

If the current N = 10 proof already inducts on the original denominator, N = 16 is easier: every N = 16 solution starts in the even branch, and the descent drops below `D/2`, hence certainly below `D`.

No lexicographic measure involving `eps` is needed, because the descent never changes `eps`.

## Summary of required algebraic edits

For a sign-parametric `QuarticDescent`, the clean branch structure is:

```text
Input: eps ∈ {+1,-1}, primitive solution to
       t^2 = s^4 + eps*D^2*s^2 - D^4.

Case D odd:
  eps = +1: use the existing N = 10 odd-denominator branch.
  eps = -1: contradiction modulo 8.

Case D even:
  prove 4 ∣ D for both signs;
  write D = 2*B, with B even;
  define U,V by dividing the raw factors by 4;
  prove U*V = 5*B^4 and gcd(U,V)=1;
  split into U=a^4,V=5*b^4 or U=5*a^4,V=b^4;
  replace the N = 10 identity
      (a^2 - b^2)^2 + 4*b^4
    by the sign-parametric identity
      (a^2 - eps*b^2)^2 + 4*b^4;
  run the same Pythagorean square-leg descent;
  obtain a smaller primitive solution with the same eps.
```

For `eps = -1`, the only genuinely new facts are:

```text
1. The odd-denominator branch is impossible modulo 8.
2. The post-factorization Pythagorean leg is a^2 + b^2 rather than a^2 - b^2.
3. The induction decrease is unchanged, and actually stronger in the only surviving branch.
```
