# Q1912 (dm1): Kubert N=12 coefficients and obstruction

This is the cyclic order-12 Kubert family in the form

```text
E_12(t): y^2 = x^3 + A_12(t) x^2 + B_12(t) x.
```

Requiring an additional independent rational 2-torsion point, i.e. the full `Z/2 x Z/12` situation, means that the quadratic factor `x^2 + A_12(t) x + B_12(t)` splits over `Q`.  Equivalently, `A_12(t)^2 - 4 B_12(t)` must be a rational square.

## Coefficients

The normalized coefficients are:

```text
A_12(t) = 2*(3*t^8 + 24*t^6 + 6*t^4 - 1)
        = 6*t^8 + 48*t^6 + 12*t^4 - 2.
```

```text
B_12(t) = (t^2 - 1)^6*(1 + 3*t^2)^2
        = 9*t^16 - 48*t^14 + 100*t^12 - 96*t^10
          + 30*t^8 + 16*t^6 - 12*t^4 + 1.
```

The usual nonsingular exclusions are `t = 0, +/-1`: at `t = +/-1`, `B_12(t)=0`; at `t=0`, the remaining quadratic has double root.

## Factored discriminant

The remaining quadratic discriminant factors as:

```text
A_12(t)^2 - 4*B_12(t)
  = 256*t^6*(t^2 + 1)^3*(3*t^2 - 1).
```

Expanded:

```text
A_12(t)^2 - 4*B_12(t)
  = 768*t^14 + 2048*t^12 + 1536*t^10 - 256*t^6.
```

A compact verification is to put `z = t^2`.  Then

```text
A_12(t)/2 = F(z) = 3*z^4 + 24*z^3 + 6*z^2 - 1,
B_12(t)   = G(z)^2,
G(z)      = (z - 1)^3*(1 + 3*z)
          = 3*z^4 - 8*z^3 + 6*z^2 - 1.
```

Hence

```text
F(z) - G(z) = 32*z^3,
F(z) + G(z) = 2*(z + 1)^3*(3*z - 1),
```

so

```text
A_12(t)^2 - 4*B_12(t)
  = 4*(F(z)^2 - G(z)^2)
  = 256*z^3*(z + 1)^3*(3*z - 1)
  = 256*t^6*(t^2 + 1)^3*(3*t^2 - 1).
```

## Obstruction curve

Since

```text
256*t^6*(t^2 + 1)^2 = (16*t^3*(t^2 + 1))^2,
```

for nonsingular `t != 0`, the square condition reduces to

```text
W^2 = (t^2 + 1)*(3*t^2 - 1) = 3*t^4 + 2*t^2 - 1.
```

So the direct N=12 obstruction is the quartic

```text
C_12: W^2 = (t^2 + 1)*(3*t^2 - 1).
```

A convenient Weierstrass model for this genus-one quartic is

```text
E_12_obs: Y^2 = X^3 - X^2 + X.
```

One reduction is: set

```text
r = (t - 1)/(t + 1),
S = W*(1 - r)^2/2.
```

Then

```text
S^2 = r^4 + 4*r^3 + 2*r^2 + 4*r + 1.
```

For this reciprocal quartic, the standard quartic-to-Weierstrass substitution gives

```text
Y0^2 = (X0 + 2)*(X0^2 + 12),
```

and the scaling

```text
X = (X0 + 2)/4,
Y = Y0/8
```

turns it into

```text
Y^2 = X^3 - X^2 + X.
```

Thus, in the same role as the N=10 curve `w^2 = u^3 + u^2 - u`, the N=12 full-2-torsion obstruction may be taken as either

```text
W^2 = (t^2 + 1)*(3*t^2 - 1)
```

or, in Weierstrass form,

```text
Y^2 = X^3 - X^2 + X.
```

Reference: this is the `Z/12Z` Weierstrass family stated as Theorem 5 in Halbeisen, Hungerbuehler, Voznyy, and Zargar, `A geometric approach to elliptic curves with torsion groups Z/10Z, Z/12Z, Z/14Z, and Z/16Z`, arXiv:2106.06861.  The same section records Kubert's original Tate normal-form parameters and the transformation to `y^2 = x^3 + a*x^2 + b*x`.
