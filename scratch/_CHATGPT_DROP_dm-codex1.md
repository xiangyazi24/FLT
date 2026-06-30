# Q2544: explicit descent for primitive centered four-square APs

## Source and high-level verdict

The most usable descent I found is Alf van der Poorten's direct proof in *Fermat's Four Squares Theorem*, arXiv:0712.3850.  It is exactly the classical Fermat/Euler descent, phrased through the two concordant forms

\[
D^2+4A^2 \quad\text{and}\quad D^2+16A^2.
\]

This gives a clean Lean frontier:

1. Convert a primitive centered four-square AP with common difference `4N` to a pair `(A,D)` with `N = A D` and both `D^2+4A^2`, `D^2+16A^2` squares.
2. Descend the pair `(A,D)` to a smaller pair `(a,d)` with `|a d| < |A D|` and the same square-form property.
3. Convert `(a,d)` back to a primitive centered four-square AP with `N' = a d`.

So the explicit descent is **not** an AP-to-Fermat42 substitution.  The right intermediate theorem is a descent for the concordant-form package.

Important correction for the residual:

\[
\forall S : \texttt{PrimitiveCenteredFourSqAP},\ \exists T,\ |T.N| < |S.N|
\]

is false if `PrimitiveCenteredFourSqAP` permits the degenerate constant case `N = 0`.  The residual must either have `S.N ≠ 0`, or `PrimitiveCenteredFourSqAP` must already exclude `N = 0`.

---

## Normalization

Start from a primitive centered AP with roots `p,q,r,s` and center `X`:

\[
p^2 = X - 6N,\qquad
q^2 = X - 2N,\qquad
r^2 = X + 2N,\qquad
s^2 = X + 6N.
\]

Equivalently the common difference is `4N`:

\[
q^2-p^2 = r^2-q^2 = s^2-r^2 = 4N.
\]

Your checked identities

\[
p^2+r^2=2q^2,\qquad q^2+s^2=2r^2,
\]

and

\[
(r-p)(r+p)=8N,\qquad (s-q)(s+q)=8N
\]

are consistent with this normalization.

For the descent, normalize by sign/reversal as follows.

* Replace roots by absolute values when convenient; only their squares matter.
* If `N < 0`, reverse the progression.  This replaces `N` by `-N` and does not change `N.natAbs`.
* Work with `N > 0`, `X > 6N`, roots odd, and pairwise coprime.

Then

\[
X = \frac{q^2+r^2}{2}=q^2+2N=r^2-2N.
\]

---

## AP to concordant forms

Let

\[
Y = p q r s.
\]

Then

\[
Y^2
= (X^2-4N^2)(X^2-36N^2)
= (X^2-20N^2)^2 - (16N^2)^2.
\]

Thus

\[
(16N^2)^2 + Y^2 = (X^2-20N^2)^2.
\]

Under the primitive hypotheses this is a primitive Pythagorean triple, with even leg `16N^2`.  Hence there are coprime integers `2u` and `v`, with `v` odd, such that

\[
4uv = 16N^2,
\]

\[
Y = \pm(4u^2-v^2),
\]

\[
X^2-20N^2 = 4u^2+v^2.
\]

Since `uv = 4N^2`, `gcd(u,v)=1`, and `v` is odd, square-factor extraction gives

\[
u = 4A^2,\qquad v = D^2,
\]

with `D` odd and

\[
N = A D
\]

after choosing positive signs.

Now

\[
X^2-20N^2 = 4u^2+v^2
\]

and `uv = 4N^2` imply

\[
X^2 = 4u^2+5uv+v^2 = (4u+v)(u+v).
\]

Substituting `u = 4A^2`, `v = D^2` gives

\[
X^2 = (16A^2+D^2)(4A^2+D^2).
\]

The two factors are coprime under the primitive hypotheses, so both are squares.  Thus there exist integers `B,C` such that

\[
B^2 = 16A^2+D^2,
\]

\[
C^2 = 4A^2+D^2.
\]

This is the first key intermediate theorem.

### Suggested theorem statement

```text
CenteredAP_to_concordant_forms:
Given a nonconstant primitive centered four-square AP with N > 0,
there exist integers A,D,B,C such that
  N = A*D,
  D is odd,
  gcd(A,D)=1,
  B^2 = 16*A^2 + D^2,
  C^2 = 4*A^2 + D^2.
```

This is exactly the Euler/concordant-forms reduction: `D^2+(2A)^2` and `D^2+(4A)^2` are both squares.

---

## Concordant-form descent

Assume now that

\[
C^2 = 4A^2+D^2,
\]

\[
B^2 = 16A^2+D^2,
\]

with `gcd(A,D)=1`, `D` odd, and `A D ≠ 0`.

The first equation is the primitive Pythagorean triple

\[
(2A)^2 + D^2 = C^2.
\]

Hence there are coprime `U,V`, of opposite parity, such that, after choosing the sign of `D`,

\[
A = U V,
\]

\[
D = \pm(U^2 - V^2).
\]

The second equation is the primitive Pythagorean triple

\[
(4A)^2 + D^2 = B^2.
\]

Parametrize it as

\[
A = U' V',
\]

\[
D = \pm(4U'^2 - V'^2),
\]

with `gcd(2U',V')=1` and `V'` odd.

Because `A = UV = U'V'` in two coprime factorizations, and the even part lies in `U` and `U'`, there are pairwise coprime integers

\[
2a,\ b,\ c,\ d
\]

such that, after harmless sign changes,

\[
U = 2ab,\qquad V = cd,
\]

\[
U' = 2ac,\qquad V' = bd.
\]

Thus

\[
A = UV = U'V' = 2abcd.
\]

The two formulae for `D` become, with a common sign,

\[
\pm D = 4a^2b^2 - c^2d^2
      = 16a^2c^2 - b^2d^2.
\]

Equating the two right-hand sides gives

\[
4a^2b^2 - c^2d^2 = 16a^2c^2 - b^2d^2.
\]

Rearrange this as

\[
b^2(4a^2+d^2)=c^2(16a^2+d^2).
\]

Since `2a,b,c,d` are pairwise coprime, one has

\[
\gcd(4a^2+d^2,\ 16a^2+d^2)=1.
\]

The only possible common prime would divide `12a^2` and `d^2`; by `gcd(a,d)=1` it must divide `12`; parity excludes `2`, and modulo `3` excludes `3` unless both `a,d` are divisible by `3`, which is impossible.

Therefore the reduced rational equality

\[
\frac{4a^2+d^2}{16a^2+d^2}=\left(\frac{c}{b}\right)^2
\]

forces both factors to be squares.  In fact, after choosing signs,

\[
c^2 = 4a^2+d^2,
\]

\[
b^2 = 16a^2+d^2.
\]

So `(a,d)` is a new concordant-form solution of the same type.

The descent inequality is immediate from

\[
A = 2abcd.
\]

Indeed

\[
|ad| < |A| \le |AD|.
\]

Since the original centered AP had `N = AD`, the new candidate has

\[
N' = ad,
\]

and

\[
|N'| = |ad| < |AD| = |N|.
\]

### Suggested theorem statement

```text
concordant_forms_descent:
Assume gcd(A,D)=1, D odd, A*D ≠ 0, and
  B^2 = 16*A^2 + D^2,
  C^2 = 4*A^2 + D^2.
Then there exist a,d,b,c such that
  2*a, b, c, d are pairwise coprime,
  d is odd,
  b^2 = 16*a^2 + d^2,
  c^2 = 4*a^2 + d^2,
  0 < |a*d| < |A*D|.
```

This is the real descent step.

---

## Concordant forms back to a smaller centered AP

Now suppose the descent has produced `a,d,b,c` with

\[
b^2 = 16a^2+d^2,
\]

\[
c^2 = 4a^2+d^2.
\]

Define the smaller center and common-difference parameter by

\[
X' = b c,
\]

\[
N' = a d.
\]

The four square **values** in the smaller centered progression are

\[
X' - 6N',\qquad X' - 2N',\qquad X' + 2N',\qquad X' + 6N'.
\]

The product identities that make them squares are:

\[
(X'-2N')(X'+2N')
= (bc)^2 - 4a^2d^2
= (d^2+8a^2)^2,
\]

and

\[
(X'-6N')(X'+6N')
= (bc)^2 - 36a^2d^2
= (d^2-8a^2)^2.
\]

The relevant gcd facts are:

\[
\gcd(X'-2N', X'+2N')=1,
\]

\[
\gcd(X'-6N', X'+6N')=1.
\]

For the outer pair, the only extra possible common divisor is `3`; modulo `3` and `gcd(a,d)=1` exclude it.  Hence each factor in both products is itself a square.

Therefore choose integers `p',q',r',s'` satisfying

\[
p'^2 = X' - 6N',
\]

\[
q'^2 = X' - 2N',
\]

\[
r'^2 = X' + 2N',
\]

\[
s'^2 = X' + 6N'.
\]

Then

\[
q'^2-p'^2 = r'^2-q'^2 = s'^2-r'^2 = 4N'.
\]

So the constructed `T` is a centered four-square AP with

\[
T.N = N' = ad,
\]

and the descent inequality is

\[
|T.N| = |ad| < |AD| = |N| = |S.N|.
\]

### Suggested theorem statement

```text
concordant_forms_to_centered_AP:
Assume gcd(a,d)=1, d odd, a*d ≠ 0, and
  b^2 = 16*a^2 + d^2,
  c^2 = 4*a^2 + d^2.
Let
  X' = b*c,
  N' = a*d.
Then the four integers
  X' - 6*N', X' - 2*N', X' + 2*N', X' + 6*N'
are squares and form a primitive centered four-square AP with parameter N'.
```

This statement is enough to build the `T : PrimitiveCenteredFourSqAP` required by the residual.  The roots `p',q',r',s'` are obtained by square extraction from the product/gcd identities above; they are not simple polynomial expressions in `a,d,b,c`.

---

## Relation to `(xy-wz)(xy+wz)=2Δ^2`

For the original roots `p,q,r,s`, with common difference

\[
\Delta = q^2-p^2 = 4N,
\]

the standard identity is

\[
(qr-ps)(qr+ps)
= q^2r^2-p^2s^2
= 2\Delta^2
= 32N^2.
\]

This identity is correct and useful for local algebra/gcd checks, but by itself it only gives a product of two factors equal to twice a square.  It does not directly produce the smaller progression.  The van der Poorten/Euler descent packages the needed square extraction through the Pythagorean triple

\[
(16N^2)^2 + (pqrs)^2 = (X^2-20N^2)^2
\]

and then through the concordant forms

\[
D^2+4A^2,\qquad D^2+16A^2.
\]

That is the route I would formalize.

---

## Final Lean-facing DAG

Use the following theorem DAG rather than trying to prove the residual in one step.

```text
Primitive centered AP S, S.N ≠ 0
  -> normalize N > 0 by reversal/signs
  -> AP_to_concordant_forms:
       ∃ A D B C,
         S.N = A*D,
         gcd(A,D)=1,
         D odd,
         B^2 = 16*A^2 + D^2,
         C^2 = 4*A^2 + D^2
  -> concordant_forms_descent:
       ∃ a d b c,
         0 < |a*d| < |A*D|,
         b^2 = 16*a^2 + d^2,
         c^2 = 4*a^2 + d^2,
         primitive parity/gcd package
  -> concordant_forms_to_centered_AP:
       construct T with T.N = a*d
  -> T.N.natAbs < S.N.natAbs.
```

The genuinely hard classical proof obligation is `concordant_forms_descent`.  Its explicit formulas are the factorization

\[
U = 2ab,\quad V = cd,\quad U' = 2ac,\quad V' = bd,
\]

leading to

\[
A = 2abcd,
\]

\[
\pm D = 4a^2b^2 - c^2d^2 = 16a^2c^2 - b^2d^2,
\]

and hence to the smaller pair

\[
N' = ad,
\qquad
|N'| < |N|.
\]
