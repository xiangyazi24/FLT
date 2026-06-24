The clean elementary route is:

1. clear denominators;
2. do the full \(2\)-torsion squareclass split;
3. reduce the surviving cases to two classical elementary descent lemmas:
   no four rational squares in a nonconstant arithmetic progression, and the closely related “\(0,1,4\)” square-step lemma.

No elliptic-curve API is needed after denominator clearing.

---

## Two descent lemmas to prove once

Use these as the elementary descent core.

### Lemma A: no four squares in arithmetic progression

If

\[
a^2,\ b^2,\ c^2,\ d^2
\]

are four rational squares in arithmetic progression, then the common difference is zero. Equivalently, after clearing denominators:

\[
b^2-a^2=c^2-b^2=d^2-c^2
\quad\Longrightarrow\quad
a^2=b^2=c^2=d^2.
\]

This is Fermat’s classical no-four-squares-in-AP theorem; it has a standard infinite descent proof. The classical statement that no four rational squares occur in a nonconstant arithmetic progression is a known equivalent form of Fermat/Euler descent. citeturn222409search2

Lean-shaped statement:

```lean
lemma no_four_sq_AP
    (a b c d Δ : ℤ)
    (h1 : b^2 = a^2 + Δ)
    (h2 : c^2 = a^2 + 2*Δ)
    (h3 : d^2 = a^2 + 3*Δ) :
    Δ = 0 := by
  -- Fermat infinite descent
```

### Lemma B: the \(0,1,4\) square-step lemma

If

\[
B^2=A^2+D^2,\qquad C^2=A^2+4D^2,
\]

then

\[
AD=0.
\]

Equivalently: there are no nontrivial rational squares at positions \(0,1,4\) with square step:

\[
A^2,\quad A^2+D^2,\quad A^2+4D^2.
\]

Lean-shaped statement:

```lean
lemma no_sq_at_0_1_4_with_sq_step
    (A B C D : ℤ)
    (h1 : B^2 = A^2 + D^2)
    (h2 : C^2 = A^2 + 4*D^2) :
    A * D = 0 := by
  -- Euler/Fermat descent; equivalently reduce to
  -- X^4 - X^2*Y^2 + Y^4 = Z^2
```

A convenient proof of Lemma B is by primitive Pythagorean parametrization and descent on the resulting quartic

\[
Z^2=X^4-X^2Y^2+Y^4.
\]

This is the same elementary-descent family as Fermat’s right-triangle theorem: rational right triangles cannot have square area, proved by infinite descent. citeturn222409search5

These two lemmas are the only genuinely nonlocal ingredients.

---

# 1. Denominator clearing

Let

\[
w^2=(u-1)(u-2)(u+2).
\]

Write \(u=A/N^2\) with

\[
A,N\in\mathbb Z,\qquad N>0,\qquad \gcd(A,N)=1.
\]

This is the usual monic-cubic denominator lemma: if \(u=a/b\) in lowest terms, then every prime exponent in \(b\) is even, because the denominator of the right-hand side is \(b^3\), while \(w^2\) has square denominator.

Then

\[
u-1=\frac{A-N^2}{N^2},\qquad
u-2=\frac{A-2N^2}{N^2},\qquad
u+2=\frac{A+2N^2}{N^2}.
\]

Also \(N^3w\in\mathbb Z\), say \(C=N^3w\), and therefore

\[
C^2=(A-N^2)(A-2N^2)(A+2N^2).
\]

Set

\[
F_1=A-N^2,\qquad
F_2=A-2N^2,\qquad
F_3=A+2N^2.
\]

If one \(F_i\) vanishes, then immediately

\[
F_1=0\Rightarrow u=1,\qquad
F_2=0\Rightarrow u=2,\qquad
F_3=0\Rightarrow u=-2.
\]

So assume from now on that all \(F_i\neq0\).

---

# 2. GCD and squareclass support

We have

\[
F_1-F_2=N^2,\qquad
F_3-F_2=4N^2,\qquad
F_3-F_1=3N^2.
\]

Since \(\gcd(A,N)=1\), each \(F_i\) is coprime to \(N\). Therefore:

\[
\gcd(F_1,F_2)=1,
\]

\[
\gcd(F_1,F_3)\mid 3,
\]

\[
\gcd(F_2,F_3)\mid 4.
\]

Write

\[
F_1=d_1X^2,\qquad
F_2=d_2Y^2,\qquad
F_3=d_3Z^2,
\]

with \(d_i\) squarefree integers carrying the sign of \(F_i\).

Because

\[
F_1F_2F_3=C^2,
\]

the product \(d_1d_2d_3\) is a squareclass \(1\). The gcd restrictions force the only possible prime supports:

\[
d_1\in\{\pm1,\pm3\},
\]

\[
d_2\in\{\pm1,\pm2\},
\]

\[
d_3\in\{\pm1,\pm2,\pm3,\pm6\}.
\]

More precisely, prime \(2\) can only occur in \(d_2,d_3\), and prime \(3\) can only occur in \(d_1,d_3\).

Now use signs. Since

\[
(u-1)(u-2)(u+2)=w^2\ge0
\]

and none of the factors is zero, either

\[
u>2
\]

so all three factors are positive, or

\[
-2<u<1
\]

so \(u-1,u-2<0\) and \(u+2>0\). The intervals \(1<u<2\) and \(u<-2\) give negative product and are impossible.

Thus the only squareclass triples are:

\[
(1,1,1),\quad (1,2,2),\quad (3,1,3),\quad (3,2,6),
\]

and

\[
(-1,-1,1),\quad (-1,-2,2),\quad (-3,-1,3),\quad (-3,-2,6).
\]

That is the finite full-\(2\)-torsion descent list.

---

# 3. Case analysis

Throughout,

\[
F_1=d_1X^2,\qquad
F_2=d_2Y^2,\qquad
F_3=d_3Z^2,
\]

and

\[
F_1-F_2=N^2,\qquad
F_3-F_1=3N^2,\qquad
F_3-F_2=4N^2.
\]

Also

\[
\gcd(X,N)=\gcd(Y,N)=\gcd(Z,N)=1.
\]

---

## Case \((d_1,d_2,d_3)=(1,1,1)\)

Then

\[
F_1=X^2,\qquad F_2=Y^2,\qquad F_3=Z^2.
\]

The differences give

\[
X^2=Y^2+N^2,
\]

\[
Z^2=Y^2+4N^2.
\]

Apply Lemma B with

\[
A=Y,\qquad D=N,\qquad B=X,\qquad C=Z.
\]

Since \(N>0\), Lemma B gives \(Y=0\). Hence

\[
F_2=0,
\]

so

\[
A-2N^2=0,
\]

and therefore

\[
u=2.
\]

So this case gives only the torsion value \(u=2\).

---

## Case \((d_1,d_2,d_3)=(1,2,2)\)

Then

\[
F_1=X^2,\qquad F_2=2Y^2,\qquad F_3=2Z^2.
\]

The first difference gives

\[
X^2-2Y^2=N^2.
\]

The second useful difference gives

\[
2Z^2-X^2=3N^2.
\]

This case is impossible modulo \(8\).

Indeed, from

\[
X^2-2Y^2=N^2
\]

and \(\gcd(Y,N)=1\):

- if \(N\) is even, then \(Y\) is odd, and the equation is impossible modulo \(8\);
- hence \(N\) is odd;
- then \(Y\) must be even, and \(X\) is odd.

Now reduce

\[
2Z^2-X^2=3N^2
\]

modulo \(8\). Since \(N\) and \(X\) are odd,

\[
3N^2\equiv 3\pmod 8,\qquad X^2\equiv1\pmod 8.
\]

But \(2Z^2-X^2\) is either

\[
-1\equiv7\pmod8
\]

if \(Z\) is even, or

\[
2-1\equiv1\pmod8
\]

if \(Z\) is odd. It is never \(3\). Contradiction.

So this squareclass triple is impossible.

---

## Case \((d_1,d_2,d_3)=(3,1,3)\)

Then

\[
F_1=3X^2,\qquad F_2=Y^2,\qquad F_3=3Z^2.
\]

The first difference gives

\[
3X^2-Y^2=N^2.
\]

Modulo \(3\),

\[
-Y^2\equiv N^2\pmod3.
\]

The only square residues modulo \(3\) are \(0,1\), so this forces

\[
3\mid Y,\qquad 3\mid N,
\]

contradicting \(\gcd(Y,N)=1\).

So this triple is impossible.

---

## Case \((d_1,d_2,d_3)=(3,2,6)\)

Then

\[
F_1=3X^2,\qquad F_2=2Y^2,\qquad F_3=6Z^2.
\]

The differences give

\[
3X^2-2Y^2=N^2,
\]

\[
6Z^2-3X^2=3N^2,
\]

\[
6Z^2-2Y^2=4N^2.
\]

Divide the second equation by \(3\):

\[
2Z^2-X^2=N^2,
\]

so

\[
X^2=2Z^2-N^2.
\]

Divide the third equation by \(2\):

\[
3Z^2-Y^2=2N^2,
\]

so

\[
Y^2=3Z^2-2N^2.
\]

Therefore

\[
N^2,\quad Z^2,\quad X^2,\quad Y^2
\]

are four squares in arithmetic progression. Indeed, if

\[
\Delta=Z^2-N^2,
\]

then

\[
Z^2=N^2+\Delta,
\]

\[
X^2=2Z^2-N^2=N^2+2\Delta,
\]

\[
Y^2=3Z^2-2N^2=N^2+3\Delta.
\]

By Lemma A,

\[
\Delta=0.
\]

Thus

\[
Z^2=N^2.
\]

Now

\[
F_3=A+2N^2=6Z^2=6N^2,
\]

so

\[
A=4N^2.
\]

Hence

\[
u=\frac{A}{N^2}=4.
\]

So this case gives \(u=4\).

---

## Case \((d_1,d_2,d_3)=(-1,-1,1)\)

Then

\[
F_1=-X^2,\qquad F_2=-Y^2,\qquad F_3=Z^2.
\]

The difference \(F_3-F_1=3N^2\) gives

\[
Z^2+X^2=3N^2.
\]

Modulo \(3\), this forces

\[
3\mid X,\qquad 3\mid Z.
\]

Then the left side is divisible by \(9\), so \(3N^2\) is divisible by \(9\), hence

\[
3\mid N.
\]

This contradicts \(\gcd(X,N)=1\).

So this triple is impossible.

---

## Case \((d_1,d_2,d_3)=(-1,-2,2)\)

Then

\[
F_1=-X^2,\qquad F_2=-2Y^2,\qquad F_3=2Z^2.
\]

The first difference gives

\[
-X^2+2Y^2=N^2,
\]

so

\[
X^2=2Y^2-N^2.
\]

The difference \(F_3-F_2=4N^2\) gives

\[
2Z^2+2Y^2=4N^2,
\]

so

\[
Z^2+Y^2=2N^2.
\]

Thus

\[
Z^2=2N^2-Y^2.
\]

Now

\[
Z^2,\quad N^2,\quad Y^2,\quad X^2
\]

are four squares in arithmetic progression. Let

\[
\Delta=Y^2-N^2.
\]

Then

\[
Z^2=N^2-\Delta,
\]

\[
Y^2=N^2+\Delta,
\]

\[
X^2=2Y^2-N^2=N^2+2\Delta.
\]

So the four squares are

\[
Z^2,\quad N^2,\quad Y^2,\quad X^2
\]

with common difference \(\Delta\). By Lemma A,

\[
\Delta=0.
\]

Hence

\[
Y^2=N^2.
\]

Using

\[
F_2=A-2N^2=-2Y^2,
\]

we get

\[
A-2N^2=-2N^2,
\]

so

\[
A=0.
\]

Therefore

\[
u=0.
\]

So this case gives \(u=0\).

---

## Case \((d_1,d_2,d_3)=(-3,-1,3)\)

Then

\[
F_1=-3X^2,\qquad F_2=-Y^2,\qquad F_3=3Z^2.
\]

The difference \(F_3-F_1=3N^2\) gives

\[
3Z^2+3X^2=3N^2,
\]

so

\[
Z^2+X^2=N^2.
\]

Also, from \(F_3-F_2=4N^2\),

\[
3Z^2+Y^2=4N^2.
\]

Using \(N^2=Z^2+X^2\), this becomes

\[
3Z^2+Y^2=4Z^2+4X^2,
\]

hence

\[
Y^2=Z^2+4X^2.
\]

Thus

\[
N^2=Z^2+X^2,\qquad Y^2=Z^2+4X^2.
\]

Apply Lemma B with

\[
A=Z,\qquad D=X,\qquad B=N,\qquad C=Y.
\]

Lemma B gives

\[
ZX=0.
\]

If \(X=0\), then

\[
F_1=-3X^2=0,
\]

so

\[
u=1.
\]

If \(Z=0\), then

\[
F_3=3Z^2=0,
\]

so

\[
u=-2.
\]

So this case gives only \(u=1\) or \(u=-2\).

---

## Case \((d_1,d_2,d_3)=(-3,-2,6)\)

Then

\[
F_1=-3X^2,\qquad F_2=-2Y^2,\qquad F_3=6Z^2.
\]

The first difference gives

\[
-3X^2+2Y^2=N^2.
\]

Modulo \(3\),

\[
2Y^2\equiv N^2\pmod3.
\]

Since the only square residues modulo \(3\) are \(0,1\), this forces

\[
3\mid Y,\qquad 3\mid N,
\]

contradicting \(\gcd(Y,N)=1\).

So this triple is impossible.

---

# Final conclusion

The only possible values are:

\[
u=2
\]

from \((1,1,1)\),

\[
u=4
\]

from \((3,2,6)\),

\[
u=0
\]

from \((-1,-2,2)\),

and

\[
u=1,\ -2
\]

from \((-3,-1,3)\).

Therefore every rational point satisfies

\[
u\in\{-2,0,1,2,4\}.
\]

Plugging these back into the curve gives

\[
u=-2,1,2 \Rightarrow w=0,
\]

\[
u=0 \Rightarrow w=\pm2,
\]

\[
u=4 \Rightarrow w=\pm6.
\]

So the rational affine points are exactly

\[
(-2,0),\ (1,0),\ (2,0),\ (0,\pm2),\ (4,\pm6).
\]

For Lean, the clean modular/descent dependency graph is:

```text
denominator_square
  → integer factors F₁,F₂,F₃
  → squarefree support d₁ ∈ ±{1,3}, d₂ ∈ ±{1,2}, d₃ ∈ ±{1,2,3,6}
  → 8 squareclass triples
  → mod 8 / mod 3 eliminate 4 triples
  → no_sq_at_0_1_4_with_sq_step eliminates/pins (1,1,1), (-3,-1,3)
  → no_four_sq_AP pins (-1,-2,2), (3,2,6)
  → u ∈ {-2,0,1,2,4}
```
