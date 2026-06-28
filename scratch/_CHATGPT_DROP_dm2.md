# Q1913 (dm2): N=14 Kubert normal form

There is an important difference from N=10 and N=12.  For N=14 there is no one-parameter rational polynomial pair A_14(t), B_14(t) over Q analogous to the N=10 family.  The parameter curve for a point of order 14 is genus one.  The clean normal form uses two parameters u and v satisfying one relation.

Use the relation

```text
R14(u,v) = (u - 1)^2*v^2
           + 2*u*(u^2 + 4*u - 1)*v
           + u^2*(u^2 - 6*u - 3)
         = 0.
```

Then the N=14 curve can be written as

```text
E14(u,v): y^2 = x^3 + A14(u,v)*x^2 + B14(u,v)*x,
```

with

```text
A14(u,v) = 3*u^2 + 2*u^3*v + v^2 - 2
B14(u,v) = (u^2 - 1)^3*(v^2 - 1).
```

The discriminant of the remaining quadratic factor is the simple ring identity

```text
A14(u,v)^2 - 4*B14(u,v)
  = (u + v)^3*(4*u^3 - 3*u + v).
```

Therefore the extra full 2-torsion condition is that this is a square.  Away from u+v=0, this reduces to

```text
W^2 = (u + v)*(4*u^3 - 3*u + v),
```

together with R14(u,v)=0.  Thus the full-2-and-order-14 obstruction is

```text
R14(u,v) = 0,
W^2 = (u + v)*(4*u^3 - 3*u + v).
```

The order-14 relation itself may be solved by writing

```text
v = u*(1 - 4*u - u^2 +/- 2*z)/(u - 1)^2,
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

So the basic order-14 obstruction curve is

```text
C14: z^2 = 1 - 2*u + u^2 + 4*u^3.
```

Equivalently, with X=u and Y=2*z,

```text
Y^2 = 4*X^3 + X^2 - 2*X + 1.
```

This is the curve usually used to obstruct rational order-14 torsion over Q.

For the one-parameter-plus-square-root version, set z^2 = 1 - 2*u + u^2 + 4*u^3.  After substituting the plus sign for v and using the normalization of the normal-form calculation, the coefficients are

```text
A14(u,z)
  = -2*(1 - 4*u + 2*u^2 + 10*u^3 - 18*u^4 - 10*u^6 + 2*u^7 + u^8)
    + 4*u^2*(1 - 4*u - 2*u^3 + u^4)*z.
```

Expanded:

```text
A14(u,z)
  = -2*u^8 - 4*u^7 + 20*u^6 + 36*u^4 - 20*u^3 - 4*u^2 + 8*u - 2
    + (4*u^6 - 8*u^5 - 16*u^3 + 4*u^2)*z.
```

And

```text
B14(u,z)
  = (1 - u)^7*(1 + u)^3*
    ((1 + u)*(1 - 5*u + 6*u^2 + 6*u^3 - 23*u^4 - u^5)
      - 4*u^2*(1 - 4*u - u^2)*z).
```

Expanded:

```text
B14(u,z)
  = u^16 + 20*u^15 - 76*u^14 + 276*u^12 - 228*u^11
    - 340*u^10 + 504*u^9 + 86*u^8 - 436*u^7 + 140*u^6
    + 144*u^5 - 108*u^4 + 4*u^3 + 20*u^2 - 8*u + 1
    + (-4*u^14 + 56*u^12 - 96*u^11 - 60*u^10 + 256*u^9
       - 112*u^8 - 192*u^7 + 196*u^6 - 72*u^4 + 32*u^3
       - 4*u^2)*z.
```

Under z^2 = 1 - 2*u + u^2 + 4*u^3, this discriminant reduces to

```text
A14(u,z)^2 - 4*B14(u,z)
  = 128*u^7*((u^4 + 5*u^3 - 19*u^2 + 7*u - 2)*z
      - 9*u^5 + 12*u^4 + 26*u^3 - 20*u^2 + 7*u).
```

For Lean, use the u,v identity first.  It is directly verifiable by ring:

```lean
import Mathlib.Tactic

noncomputable section

namespace Kubert14

def A14 (u v : Q) : Q :=
  3*u^2 + 2*u^3*v + v^2 - 2

def B14 (u v : Q) : Q :=
  (u^2 - 1)^3 * (v^2 - 1)

example (u v : Q) :
    A14 u v ^ 2 - 4 * B14 u v
      = (u + v)^3 * (4*u^3 - 3*u + v) := by
  unfold A14 B14
  ring

end Kubert14
```

Summary:

```text
A14(u,v) = 3*u^2 + 2*u^3*v + v^2 - 2
B14(u,v) = (u^2 - 1)^3*(v^2 - 1)
A14^2 - 4*B14 = (u + v)^3*(4*u^3 - 3*u + v)
R14(u,v) = 0
C14: z^2 = 1 - 2*u + u^2 + 4*u^3
full-2 obstruction: W^2 = (u + v)*(4*u^3 - 3*u + v), with R14(u,v)=0.
```
