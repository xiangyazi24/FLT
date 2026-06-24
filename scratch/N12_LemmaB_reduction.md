The requested bridge to `not_fermat_42` is **not a valid one-step reduction**. The hidden flaw is that Lemma B does **not** reduce to

\[
a^4+b^4=c^2.
\]

It reduces to the different quartic

\[
X^4+14X^2Y^2+Y^4=Z^2,
\]

or equivalently, in the other parity case,

\[
X^4-X^2Y^2+Y^4=Z^2.
\]

Those are not cosmetic variants of Fermat \(4\). They are the same genus-one obstruction as the full-\(2\)-torsion curve. So if Lemma B is being used to prove the rational points of

\[
w^2=(u-1)(u-2)(u+2),
\]

then Lemma B is essentially **not an elementary side lemma**; it is a disguised form of the same rank-zero calculation.

Here is the exact Lean-shaped algebra.

---

## 1. Start from Lemma B

Assume

\[
B^2=A^2+D^2,
\qquad
C^2=A^2+4D^2,
\qquad
A\ne0,
\qquad
D\ne0.
\]

Use the ordinary integer Pythagorean parametrization of the first equation. Up to swapping the two legs, there are integers \(k,r,s\) such that either

\[
A=k(r^2-s^2),\qquad D=2krs,\qquad B=k(r^2+s^2),
\]

or

\[
A=2krs,\qquad D=k(r^2-s^2),\qquad B=k(r^2+s^2).
\]

Signs can be absorbed into \(k,r,s\). For a Lean formalization, this is the only parametrization lemma you need at this stage.

---

# Case 1: \(A=k(r^2-s^2),\ D=2krs\)

Substitute into

\[
C^2=A^2+4D^2.
\]

Then

\[
\begin{aligned}
C^2
&=k^2(r^2-s^2)^2+4(2krs)^2\\
&=k^2\bigl((r^2-s^2)^2+16r^2s^2\bigr)\\
&=k^2(r^4+14r^2s^2+s^4).
\end{aligned}
\]

Since \(A,D\ne0\), \(k\ne0\). Also \(k^2\mid C^2\), hence \(k\mid C\). Write

\[
C=kZ.
\]

Then

\[
Z^2=r^4+14r^2s^2+s^4.
\]

Moreover,

\[
D=2krs\ne0
\]

implies

\[
r\ne0,\qquad s\ne0,
\]

and

\[
A=k(r^2-s^2)\ne0
\]

implies

\[
r^2\ne s^2.
\]

So the nontrivial Lemma B counterexample gives a nontrivial solution of

\[
Z^2=r^4+14r^2s^2+s^4,
\qquad
rs(r^2-s^2)\ne0.
\]

This is **not** an instance of `not_fermat_42`.

The missing theorem would be:

```lean
theorem not_ljunggren_14
    {x y z : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2) :
    x ^ 4 + 14 * x ^ 2 * y ^ 2 + y ^ 4 ≠ z ^ 2
```

Then Case 1 closes immediately.

---

# Case 2: \(A=2krs,\ D=k(r^2-s^2)\)

Substitute into the second equation:

\[
\begin{aligned}
C^2
&=(2krs)^2+4k^2(r^2-s^2)^2\\
&=4k^2\bigl(r^2s^2+(r^2-s^2)^2\bigr)\\
&=4k^2(r^4-r^2s^2+s^4).
\end{aligned}
\]

Since \(A,D\ne0\), \(k\ne0\). Hence \(2k\mid C\). Write

\[
C=2kH.
\]

Then

\[
H^2=r^4-r^2s^2+s^4.
\]

This still is not Fermat \(4\). But it converts exactly to the \(+14\) quartic by the identity

\[
(r+s)^4+14(r+s)^2(r-s)^2+(r-s)^4
=
16(r^4-r^2s^2+s^4).
\]

Therefore, setting

\[
X=r+s,\qquad Y=r-s,\qquad Z=4H,
\]

we get

\[
Z^2=X^4+14X^2Y^2+Y^4.
\]

The nonzero conditions also transfer:

\[
X=0 \iff r=-s \implies r^2-s^2=0 \implies D=0,
\]

contradiction.

\[
Y=0 \iff r=s \implies r^2-s^2=0 \implies D=0,
\]

contradiction.

And

\[
X^2=Y^2
\]

means

\[
(r+s)^2=(r-s)^2,
\]

so

\[
4rs=0.
\]

But

\[
A=2krs\ne0,
\]

contradiction. Hence

\[
X\ne0,\qquad Y\ne0,\qquad X^2\ne Y^2.
\]

So Case 2 also reduces to the same missing theorem `not_ljunggren_14`.

---

## 2. The reverse reduction: Lemma B is equivalent to the \(+14\) quartic

The obstruction is not merely that the proof is incomplete. The \(+14\) quartic is essentially equivalent to Lemma B.

Given integers \(X,Y,Z\) with

\[
Z^2=X^4+14X^2Y^2+Y^4,
\]

define

\[
A=X^2-Y^2,
\qquad
D=2XY,
\qquad
B=X^2+Y^2,
\qquad
C=Z.
\]

Then

\[
B^2=A^2+D^2
\]

because

\[
(X^2+Y^2)^2=(X^2-Y^2)^2+(2XY)^2.
\]

Also

\[
\begin{aligned}
A^2+4D^2
&=(X^2-Y^2)^2+4(2XY)^2\\
&=X^4-2X^2Y^2+Y^4+16X^2Y^2\\
&=X^4+14X^2Y^2+Y^4\\
&=Z^2\\
&=C^2.
\end{aligned}
\]

If

\[
X\ne0,\qquad Y\ne0,\qquad X^2\ne Y^2,
\]

then

\[
A\ne0,\qquad D\ne0,
\]

so

\[
AD\ne0.
\]

Thus a nontrivial solution of the \(+14\) quartic gives a counterexample to Lemma B.

So the correct equivalence is:

\[
\boxed{
\text{Lemma B}
\quad\Longleftrightarrow\quad
\text{no nontrivial integer solution of }
Z^2=X^4+14X^2Y^2+Y^4.
}
\]

This is the exact algebraic landing point.

---

## 3. Why `not_fermat_42` does not apply directly

Mathlib’s theorem

```lean
not_fermat_42 :
  ∀ {a b c : ℤ}, a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2
```

rules out

\[
a^4+b^4=c^2.
\]

But the actual expression produced from Lemma B is

\[
r^4+14r^2s^2+s^4=Z^2.
\]

The cross term \(14r^2s^2\) is not removable by `ring`, parity, or gcd bookkeeping. Treating this as if it were \(r^4+s^4=Z^2\) is the fatal mistake.

In the second parity branch, the expression is

\[
r^4-r^2s^2+s^4=H^2,
\]

which converts to the \(+14\) quartic by

\[
(r+s)^4+14(r+s)^2(r-s)^2+(r-s)^4
=
16(r^4-r^2s^2+s^4),
\]

not to Fermat \(4\).

So the direct construction requested,

\[
a=a(A,B,C,D),\quad b=b(A,B,C,D),\quad c=c(A,B,C,D)
\]

with

\[
a^4+b^4=c^2,
\qquad
a,b\ne0,
\]

is not the natural descent output. The natural output is the Ljunggren/Pocklington quartic above.

---

## 4. Lean-translatable replacement theorem

The right helper theorem is this:

```lean
theorem not_ljunggren_14
    {x y z : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2) :
    x ^ 4 + 14 * x ^ 2 * y ^ 2 + y ^ 4 ≠ z ^ 2
```

Then Lemma B is straightforward.

Lean-shaped proof skeleton:

```lean
theorem lemmaB_from_ljunggren
    (A B C D : ℤ)
    (hB : B ^ 2 = A ^ 2 + D ^ 2)
    (hC : C ^ 2 = A ^ 2 + 4 * D ^ 2) :
    A * D = 0 := by
  by_contra hAD
  have hA : A ≠ 0 := by
    intro h
    apply hAD
    rw [h]
    ring
  have hD : D ≠ 0 := by
    intro h
    apply hAD
    rw [h]
    ring

  -- Use integer Pythagorean parametrization of hB.
  -- Obtain either:
  --   A = k*(r^2-s^2), D = 2*k*r*s
  -- or:
  --   A = 2*k*r*s, D = k*(r^2-s^2).

  -- Case 1:
  --   C^2 = k^2 * (r^4 + 14*r^2*s^2 + s^4)
  --   write C = k*Z.
  --   apply not_ljunggren_14 r s Z.

  -- Case 2:
  --   C^2 = 4*k^2 * (r^4 - r^2*s^2 + s^4)
  --   write C = 2*k*H.
  --   set X = r+s, Y = r-s, Z = 4*H.
  --   use:
  --     X^4 + 14*X^2*Y^2 + Y^4 = Z^2
  --   apply not_ljunggren_14 X Y Z.
```

The key `ring` identities are:

```lean
-- Case 1
(k * (r^2 - s^2))^2 + 4 * (2*k*r*s)^2
  = k^2 * (r^4 + 14*r^2*s^2 + s^4)

-- Case 2
(2*k*r*s)^2 + 4 * (k * (r^2 - s^2))^2
  = 4*k^2 * (r^4 - r^2*s^2 + s^4)

-- Conversion of the minus-cross quartic
(r+s)^4 + 14*(r+s)^2*(r-s)^2 + (r-s)^4
  = 16*(r^4 - r^2*s^2 + s^4)
```

Those are all direct `ring`.

---

## 5. Bottom line

The requested bridge to Mathlib’s `not_fermat_42` is missing a real theorem.

The correct reduction is:

\[
\text{Lemma B}
\to
Z^2=X^4+14X^2Y^2+Y^4,
\]

not

\[
Z^2=X^4+Y^4.
\]

Moreover, the reverse construction

\[
A=X^2-Y^2,\quad D=2XY,\quad B=X^2+Y^2,\quad C=Z
\]

shows that this quartic is equivalent to Lemma B itself.

So for the full-\(2\)-torsion formalization, you need either:

\[
\boxed{\text{a new formal proof of } \texttt{not_ljunggren_14}}
\]

or a different descent package for the curve. `not_fermat_42` alone does not provide the claimed explicit polynomial witness.
