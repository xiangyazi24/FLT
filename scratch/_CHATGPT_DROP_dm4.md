# Q1258 (dm4): Kubert `C_10`, full rational 2-torsion, and the obstruction curve

## Executive answer

There is **not** a separate nondegenerate Kubert family over `Q` for torsion containing

```text
Z/2Z × Z/10Z.
```

The right route is:

```text
cyclic C_10 Kubert/Tate normal form
  + require the remaining two 2-torsion points to be rational
  = square condition
  = rational point on C : w^2 = u^3 + u^2 - u.
```

The obstruction curve has only the rational points

```text
O, (0,0), (1,1), (1,-1), (-1,1), (-1,-1),
```

and the finite `u`-values are exactly

```text
u ∈ {-1, 0, 1}.
```

Those are precisely degenerate/singular parameter values for the elliptic-curve family.  Hence the assumed nondegenerate `Z/2Z × Z/10Z` torsion cannot occur over `Q`.

I will use `t` for the normalized Kubert parameter.  This `t` is the same affine coordinate as the `u` in the obstruction curve `w^2 = u^3 + u^2 - u`; equivalently, set `u = t`.

If `τ` is Kubert's raw table parameter, then

```text
t = 2τ - 1,        τ = (t + 1)/2.
```

## 1. Kubert table entry: cyclic order `10`

Kubert's Tate normal form is

```text
E(b,c) : y^2 + (1 - c)xy - b y = x^3 - b x^2,
P = (0,0).
```

For the cyclic order-`10` entry, put

```text
δ = τ - (τ - 1)^2 = -τ^2 + 3τ - 1,
d = τ^2 / δ,
c = τ(d - 1),
b = c d.
```

Equivalently,

```text
c = τ(τ - 1)(2τ - 1) / (-τ^2 + 3τ - 1),
b = τ^3(τ - 1)(2τ - 1) / (-τ^2 + 3τ - 1)^2.
```

Then `P = (0,0)` has exact order `10`, away from the usual singular/degenerate parameter values.

In the normalized parameter

```text
t = 2τ - 1,
g(t) = t^2 - 4t - 1,
```

this Tate normal form is

```text
d = -(t + 1)^2 / g(t),
c = -t(t^2 - 1) / g(t),
b = t(t - 1)(t + 1)^3 / g(t)^2.
```

This is the cleanest answer to the literal “Kubert table entry” question.  It parameterizes curves with a rational point of order `10`, i.e. cyclic `C_10` torsion at least.  To force `Z/2Z × Z/10Z`, we add an independent rational point of order `2`, which is the square condition below.

## 2. Short Weierstrass coefficients in the normalized parameter

After moving `5P` to `(0,0)` and transforming to the split-2-torsion-friendly model, the cyclic `10` family is isomorphic to

```text
E_t : y^2 = x^3 + A(t)x^2 + B(t)x,
```

with long Weierstrass coefficients

```text
[a1, a2, a3, a4, a6] = [0, A(t), 0, B(t), 0],
```

where

```text
F(t) = 1 + 2t - 5t^2 - 5t^4 - 2t^5 + t^6,
A(t) = -2F(t),
B(t) = (t^2 - 1)^5(t^2 - 4t - 1).
```

So explicitly:

```text
A(t) = -2(1 + 2t - 5t^2 - 5t^4 - 2t^5 + t^6),
B(t) = (t^2 - 1)^5(t^2 - 4t - 1).
```

In this model,

```text
T = (0,0)
```

is the rational point of order `2`; it is `5P` under the isomorphism from the Tate normal form.

The other two geometric 2-torsion points are the roots of

```text
x^2 + A(t)x + B(t) = 0.
```

Thus an independent rational order-`2` point exists exactly when

```text
A(t)^2 - 4B(t)
```

is a rational square.

## 3. Discriminant and nonsingularity

The quadratic-factor discriminant is

```text
A(t)^2 - 4B(t) = 256 t^5(t^2 + t - 1).
```

The Weierstrass discriminant of

```text
y^2 = x^3 + A(t)x^2 + B(t)x
```

is

```text
Δ(t) = 16 B(t)^2(A(t)^2 - 4B(t))
     = 4096 t^5(t^2 + t - 1)(t^2 - 1)^10(t^2 - 4t - 1)^2.
```

So, as a polynomial identity, nonsingularity requires

```text
t ≠ 0,
t^2 + t - 1 ≠ 0,
t^2 - 1 ≠ 0,
t^2 - 4t - 1 ≠ 0.
```

Over `Q`, the quadratics `t^2 + t - 1` and `t^2 - 4t - 1` have no rational roots.  Therefore for rational `t`, the only finite rational singular parameter values are

```text
t = -1, 0, 1.
```

## 4. The obstruction curve

Suppose `E_t` has full rational `2`-torsion.  Then there is `s ∈ Q` with

```text
s^2 = A(t)^2 - 4B(t) = 256 t^5(t^2 + t - 1).
```

For a nonsingular curve, `t ≠ 0`, so we may divide by the square `(16t^2)^2`.  Set

```text
w = s / (16t^2).
```

Then

```text
w^2 = t(t^2 + t - 1) = t^3 + t^2 - t.
```

Thus the existence of an independent rational order-`2` point gives a rational point on

```text
C : w^2 = t^3 + t^2 - t.
```

Conversely, if `(t,w) ∈ C(Q)` and `t` is nondegenerate, then

```text
s = 16t^2w
```

is a rational square root of `A(t)^2 - 4B(t)`, and the two extra rational 2-torsion points are

```text
Q_+ = (F(t) + 8t^2w, 0),
Q_- = (F(t) - 8t^2w, 0),
```

because

```text
x = (-A(t) ± s)/2 = F(t) ± 8t^2w.
```

So the full-2-torsion obstruction is **exactly** the elliptic curve

```text
C : w^2 = t^3 + t^2 - t.
```

If the coordinate is named `u` instead of `t`, this is the user's curve

```text
w^2 = u^3 + u^2 - u.
```

## 5. Degenerate values and rational points on the obstruction curve

The obstruction curve is

```text
C : w^2 = u^3 + u^2 - u.
```

Its rational points are

```text
C(Q) = {O, (0,0), (1,1), (1,-1), (-1,1), (-1,-1)}.
```

The finite affine `u`-values are therefore

```text
u = -1, 0, 1.
```

These give singular curves in the `E_t` family:

### `u = -1`

```text
B(-1) = 0,
Δ(-1) = 0.
```

The cubic has a repeated root.

### `u = 0`

```text
A(0) = -2,
B(0) = 1,
E_0 : y^2 = x^3 - 2x^2 + x = x(x - 1)^2,
Δ(0) = 0.
```

### `u = 1`

```text
B(1) = 0,
Δ(1) = 0.
```

The point at infinity `O ∈ C(Q)` is the compactified boundary/cusp of the parameter curve, not a finite nondegenerate parameter.

Therefore there is no rational nondegenerate `t` for which `E_t` has an independent rational point of order `2`.  This proves the desired obstruction to `Z/2Z × Z/10Z` over `Q`, modulo the standard Kubert parametrization and the rational-point computation on `C`.

## Sage verification code

Run this with Sage.  It checks the Kubert normal form, the short-model identities, the discriminant factorization, and the rational points on the obstruction curve.

```python
from sage.all import *


def F_value(t):
    return 1 + 2*t - 5*t**2 - 5*t**4 - 2*t**5 + t**6


def A_value(t):
    return -2 * F_value(t)


def B_value(t):
    return (t**2 - 1)**5 * (t**2 - 4*t - 1)


def Delta_value(t):
    return 4096 * t**5 * (t**2 + t - 1) * (t**2 - 1)**10 * (t**2 - 4*t - 1)**2


def check_symbolic_identities():
    R = PolynomialRing(QQ, "t")
    t = R.gen()

    F = F_value(t)
    A = A_value(t)
    B = B_value(t)

    quad_disc = A**2 - 4*B
    expected_quad_disc = 256 * t**5 * (t**2 + t - 1)
    assert quad_disc == expected_quad_disc

    Delta = 16 * B**2 * quad_disc
    expected_Delta = Delta_value(t)
    assert Delta == expected_Delta

    print("symbolic identities verified")
    print("A(t)^2 - 4B(t) =", factor(quad_disc))
    print("Delta(t) =", factor(Delta))


def check_tate_order_10_over_function_field():
    R = PolynomialRing(QQ, "t")
    K = FractionField(R)
    t = K.gen()

    # Normalized parameter t = 2*tau - 1.
    tau = (t + 1) / K(2)
    delta = tau - (tau - 1)**2
    d = tau**2 / delta
    c = tau * (d - 1)
    b = c * d

    E = EllipticCurve(K, [1 - c, -b, -b, 0, 0])
    P = E([K(0), K(0)])
    O = E(0)

    assert 10*P == O
    assert 5*P != O

    print("Tate normal form verified generically: P=(0,0) has order 10")


def check_short_model_at_sample_parameters():
    # These are cyclic C_10 examples, not full Z/2 x Z/10 examples.
    # Full Z/2 x Z/10 would require a nondegenerate rational point on the obstruction curve,
    # and the later check proves there is none over Q.
    for t0 in [QQ(2), QQ(3), QQ(-2)]:
        A = A_value(t0)
        B = B_value(t0)
        E = EllipticCurve(QQ, [0, A, 0, B, 0])
        assert E.discriminant() == Delta_value(t0)
        assert E.torsion_subgroup().order() == 10
        print("t =", t0, "E =", E, "torsion =", E.torsion_subgroup())


def extra_two_torsion_x_coordinates(t0, w0):
    """
    Given a rational point (t0,w0) on w^2 = t^3 + t^2 - t,
    return the x-coordinates of the two extra 2-torsion points on E_t.

    For Q over Q, this function will only see degenerate finite t0-values,
    because the obstruction curve has no nondegenerate rational points.
    """
    t0 = QQ(t0)
    w0 = QQ(w0)
    assert w0**2 == t0**3 + t0**2 - t0
    F = F_value(t0)
    return (F + 8*t0**2*w0, F - 8*t0**2*w0)


def check_obstruction_curve_rational_points():
    # C : w^2 = u^3 + u^2 - u.
    C = EllipticCurve(QQ, [0, 1, 0, -1, 0])

    O = C(0)
    expected = {
        O,
        C([0, 0]),
        C([1, 1]),
        C([1, -1]),
        C([-1, 1]),
        C([-1, -1]),
    }

    assert C.rank() == 0
    pts = set(C.torsion_points())
    assert pts == expected

    finite_u_values = sorted({P[0] for P in pts if P != O})
    assert finite_u_values == [QQ(-1), QQ(0), QQ(1)]

    for P in pts:
        if P == O:
            continue
        u = P[0]
        assert Delta_value(u) == 0

    print("obstruction curve:", C)
    print("rank:", C.rank())
    print("torsion subgroup:", C.torsion_subgroup())
    print("C(Q):", sorted(pts, key=str))
    print("finite u-values:", finite_u_values)
    print("all finite rational obstruction points are degenerate parameters")


def main():
    check_symbolic_identities()
    check_tate_order_10_over_function_field()
    check_short_model_at_sample_parameters()
    check_obstruction_curve_rational_points()


if __name__ == "__main__":
    main()
```

## Lean formalization target

The core algebraic pieces to isolate are small polynomial identities over `Q`.

```lean
-- Schematic only: names/types should be adapted to the FLT repository.

def F (t : ℚ) : ℚ :=
  1 + 2*t - 5*t^2 - 5*t^4 - 2*t^5 + t^6

def A (t : ℚ) : ℚ := -2 * F t

def B (t : ℚ) : ℚ := (t^2 - 1)^5 * (t^2 - 4*t - 1)

lemma quad_disc_identity (t : ℚ) :
    A t ^ 2 - 4 * B t = 256 * t^5 * (t^2 + t - 1) := by
  ring

lemma discr_identity (t : ℚ) :
    16 * (B t)^2 * (A t ^ 2 - 4 * B t)
      = 4096 * t^5 * (t^2 + t - 1) * (t^2 - 1)^10 * (t^2 - 4*t - 1)^2 := by
  rw [quad_disc_identity]
  ring
```

Then the torsion obstruction can be expressed as:

```text
Assume E/Q has P of order 10 and Q of order 2 independent.
Kubert gives a rational t with E ≅ E_t and Δ(t) ≠ 0.
Independence of Q gives full rational 2-torsion, so ∃s, s^2 = A(t)^2 - 4B(t).
Since Δ(t) ≠ 0, t ≠ 0.
Set w = s / (16t^2).
Then w^2 = t^3 + t^2 - t.
But C(Q) = {O, (0,0), (1,±1), (-1,±1)}.
Thus t ∈ {-1,0,1}, contradicting Δ(t) ≠ 0.
```

So the hard imported/certified facts are:

```text
1. Kubert C_10 normal form covers every rational point of exact order 10.
2. The transformed short model has coefficients A(t), B(t) above.
3. The obstruction curve C : w^2 = u^3 + u^2 - u has exactly the six rational points listed.
```

Everything else is polynomial algebra and simple rational arithmetic.
