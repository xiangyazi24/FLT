# Q1910 (dm2): Kubert-style \(N=12\), \(N=14\), and the square-obstruction curves

## Executive answer

For \(N=12\), yes, there is a direct analogue of your \(N=10\) polynomial pair:

\[
A_{12}(t)=2(3t^8+24t^6+6t^4-1),
\]

\[
B_{12}(t)=(t^2-1)^6(1+3t^2)^2.
\]

The factorization is:

\[
A_{12}(t)^2-4B_{12}(t)
=256t^6(t^2+1)^3(3t^2-1).
\]

For \(N=14\), the request as stated has a trap: there is **no single genus-zero one-variable polynomial pair**

\[
A_{14}(t),B_{14}(t)\in \mathbb Q[t]
\]

analogous to \(N=10\) and \(N=12\).  The modular curve \(X_1(14)\) has genus \(1\), not genus \(0\), and \(X_1(2,14)\) has genus \(4\).  So a one-parameter Kubert family over \(\mathbb Q(t)\) would be a nonconstant map \(\mathbb P^1\to X_1(14)\), which is impossible in characteristic zero.

What you *can* write explicitly is the order-14 family over the coordinate ring of \(X_1(14)\).  Let

\[
z^2=1-2u+u^2+4u^3.
\]

Then the \(x^3+Ax^2+Bx\) model is:

\[
\begin{aligned}
A_{14}(u,z)=&-2(1-4u+2u^2+10u^3-18u^4-10u^6+2u^7+u^8)\\
&+4u^2(1-4u-2u^3+u^4)z,
\end{aligned}
\]

\[
\begin{aligned}
B_{14}(u,z)=&(1-u)^7(1+u)^3\\
&\cdot\Big((1+u)(1-5u+6u^2+6u^3-23u^4-u^5)\\
&\qquad\qquad-4u^2(1-4u-u^2)z\Big).
\end{aligned}
\]

Modulo the relation \(z^2=1-2u+u^2+4u^3\), the discriminant obstruction factor is:

\[
\begin{aligned}
A_{14}(u,z)^2-4B_{14}(u,z)
=128u^7\Big(& (u^4+5u^3-19u^2+7u-2)z\\
&-9u^5+12u^4+26u^3-20u^2+7u\Big).
\end{aligned}
\]

Changing the sign of \(z\) gives the conjugate family.

## Answers to the specific obstruction-curve questions

### \(N=12\)

Your proposed curve

\[
w^2=u^3-u^2-4u+4
\]

is correct as a Weierstrass model for the \(N=12\) square obstruction.

From

\[
A_{12}(t)^2-4B_{12}(t)=256t^6(t^2+1)^3(3t^2-1),
\]

remove the obvious square

\[
(16t^3(t^2+1))^2.
\]

The remaining square condition is

\[
q^2=(t^2+1)(3t^2-1).
\]

Set

\[
u=3t^2+1,\qquad w=3tq.
\]

Then

\[
w^2=u^3-u^2-4u+4.
\]

So the \(N=12\) obstruction curve is exactly the curve you wrote, up to this explicit birational change of variables.

### \(N=14\)

The proposed curve

\[
w^2=u^3+u^2-2u
\]

is **not** the direct analogue of the \(N=10\) or \(N=12\) discriminant-square obstruction coming from a genus-zero Kubert polynomial pair \(A_{14}(t),B_{14}(t)\), because such a pair does not exist.

The actual order-14 base curve \(X_1(14)\) is genus \(1\).  A common model is the Tate/Rabarison model

\[
w^2+uw+w=u^3-u,
\]

equivalently after completing the square,

\[
z^2=4u^3+u^2-2u+1.
\]

The full \(2\)-torsion plus \(14\)-torsion modular curve is \(X_1(2,14)\), and it is genus \(4\).  One explicit bidegree-\((3,3)\) model is

\[
(u^3+u^2-2u-1)v(v+1)+(v^3+v^2-2v-1)u(u+1)=0.
\]

Thus the elliptic curve \(w^2=u^3+u^2-2u\) may be a useful auxiliary curve in some quotient or quartic calculation, but it is not the full \(N=14\) square-obstruction curve in the same sense as \(N=10\) and \(N=12\).

## Which quartic is which?

The quartic

\[
s^4+d^2s^2-d^4=t^2
\]

corresponds to \(N=10\), not \(N=12\) and not \(N=14\).

Indeed, for \(d\neq0\), set

\[
U=\frac{s^2}{d^2},\qquad W=\frac{st}{d^3}.
\]

Then

\[
t^2=s^4+d^2s^2-d^4
\]

is equivalent to

\[
W^2=U^3+U^2-U,
\]

which is exactly your \(N=10\) obstruction curve.

The analogous quartic for the cubic

\[
W^2=U^3+U^2-2U
\]

would instead be

\[
s^4+d^2s^2-2d^4=t^2.
\]

For \(N=12\), the square condition is better kept as

\[
q^2=(t^2+1)(3t^2-1),
\]

with

\[
u=3t^2+1,\qquad w=3tq,
\]

which gives

\[
w^2=u^3-u^2-4u+4.
\]

## Ring-verification snippets

These are deliberately written as elementary polynomial identities.

```lean
import Mathlib

namespace KubertParamCheck

def A12 (t : ℤ) : ℤ :=
  2 * (3 * t ^ 8 + 24 * t ^ 6 + 6 * t ^ 4 - 1)

def B12 (t : ℤ) : ℤ :=
  (t ^ 2 - 1) ^ 6 * (1 + 3 * t ^ 2) ^ 2

example (t : ℤ) :
    A12 t ^ 2 - 4 * B12 t =
      256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) := by
  unfold A12 B12
  ring

example (t q : ℤ)
    (hq : q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1)) :
    (3 * t * q) ^ 2 =
      (3 * t ^ 2 + 1) ^ 3 -
      (3 * t ^ 2 + 1) ^ 2 -
      4 * (3 * t ^ 2 + 1) + 4 := by
  rw [show (3 * t * q) ^ 2 = 9 * t ^ 2 * q ^ 2 by ring]
  rw [hq]
  ring

/-- Order-14 coordinate-ring version. -/
def A14 (u z : ℤ) : ℤ :=
  -2 * (1 - 4 * u + 2 * u ^ 2 + 10 * u ^ 3 - 18 * u ^ 4 -
      10 * u ^ 6 + 2 * u ^ 7 + u ^ 8) +
    4 * u ^ 2 * (1 - 4 * u - 2 * u ^ 3 + u ^ 4) * z

def B14 (u z : ℤ) : ℤ :=
  (1 - u) ^ 7 * (1 + u) ^ 3 *
    ((1 + u) * (1 - 5 * u + 6 * u ^ 2 + 6 * u ^ 3 -
        23 * u ^ 4 - u ^ 5) -
      4 * u ^ 2 * (1 - 4 * u - u ^ 2) * z)

def D14red (u z : ℤ) : ℤ :=
  128 * u ^ 7 *
    ((u ^ 4 + 5 * u ^ 3 - 19 * u ^ 2 + 7 * u - 2) * z -
      9 * u ^ 5 + 12 * u ^ 4 + 26 * u ^ 3 -
      20 * u ^ 2 + 7 * u)

example (u z : ℤ)
    (hz : z ^ 2 = 1 - 2 * u + u ^ 2 + 4 * u ^ 3) :
    A14 u z ^ 2 - 4 * B14 u z = D14red u z := by
  have hdiff :
      A14 u z ^ 2 - 4 * B14 u z - D14red u z =
        16 * u ^ 4 * (u ^ 4 - 2 * u ^ 3 - 4 * u + 1) ^ 2 *
          (z ^ 2 - (1 - 2 * u + u ^ 2 + 4 * u ^ 3)) := by
    unfold A14 B14 D14red
    ring
  have hzero : z ^ 2 - (1 - 2 * u + u ^ 2 + 4 * u ^ 3) = 0 := by
    rw [hz]
    ring
  have hmain : A14 u z ^ 2 - 4 * B14 u z - D14red u z = 0 := by
    rw [hdiff, hzero]
    ring
  exact sub_eq_zero.mp hmain

/-- The quartic with coefficient `-d^4` is the N=10 obstruction. -/
example (s d T : ℤ)
    (hT : T ^ 2 = s ^ 4 + d ^ 2 * s ^ 2 - d ^ 4) :
    (s * T) ^ 2 = s ^ 2 * (s ^ 4 + d ^ 2 * s ^ 2 - d ^ 4) := by
  rw [hT]
  ring

/-- The coefficient `-2*d^4` gives the cubic `U^3 + U^2 - 2U` after scaling. -/
example (s d T : ℤ)
    (hT : T ^ 2 = s ^ 4 + d ^ 2 * s ^ 2 - 2 * d ^ 4) :
    (s * T) ^ 2 = s ^ 2 * (s ^ 4 + d ^ 2 * s ^ 2 - 2 * d ^ 4) := by
  rw [hT]
  ring

end KubertParamCheck
```

## Bottom line

Use:

```text
N=10:  A10^2 - 4 B10 = 256 t^5 (t^2+t-1)
       obstruction: W^2 = U^3 + U^2 - U
       quartic: s^4 + d^2 s^2 - d^4 = t^2

N=12:  A12^2 - 4 B12 = 256 t^6 (t^2+1)^3 (3t^2-1)
       obstruction: W^2 = U^3 - U^2 - 4U + 4
       quartic form: q^2 = (t^2+1)(3t^2-1), with U=3t^2+1, W=3tq

N=14:  no genus-zero A14(t),B14(t) pair exists.
       use the X1(14) coordinate-ring pair A14(u,z), B14(u,z), z^2=1-2u+u^2+4u^3.
       full X1(2,14) is genus 4, not the elliptic curve W^2=U^3+U^2-2U.
```
