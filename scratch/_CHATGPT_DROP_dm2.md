# Q377 / dm2 — CAS check: tangent multiplier `3` at a `3`-torsion point

Curve:

```text
E : y^2 = x^3 + 1
```

over `K = ℂ` numerically.  This is the short Weierstrass curve with `A = 0`, `B = 1`, discriminant `-432 ≠ 0`.

## Important correction before the CAS test

For a short Weierstrass curve

```text
y^2 = x^3 + A x + B,
```

the standard third division polynomial is

```text
ψ₃ = 3x^4 + 6A x^2 + 12B x - A^2.
```

Thus for `A = 0`, `B = 1`,

```text
ψ₃ = 3x^4 + 12x,
```

not `3x^4 + 12x - 1`.

The typed polynomial `3x^4 + 12x - 1` does **not** cut out the `3`-torsion on this curve.  For example, its small real root is

```text
x ≈ 0.08332128397766737,
```

but for the actual `ψ₃ = 3x^4 + 12x` this gives

```text
3x^4 + 12x ≈ 1,
```

so the point is not `3`-torsion.  A Jacobian computation at that root has nonzero constant `Z` for `[3]P`, so it is not a perturbation of `O`.

There is also a sign issue in the proposed tangent slope.  For a dual deformation

```text
Pε = (x₀ + ε, y₀ + ε s)
```

to remain on `E` modulo `ε²`, the first-order curve equation is

```text
2 y₀ s = 3 x₀^2,
```

so the tangent slope is

```text
s = 3 x₀^2 / (2 y₀),
```

not the negative of this.  The negative slope is not tangent unless `x₀ = 0`.

## Numerical `3`-torsion point

Use the nonzero numerical root of the corrected `ψ₃`:

```text
x₀ = -∛4 ≈ -1.5874010519681994747517056392723082603914933278999.
```

Then

```text
y₀ = sqrt(x₀^3 + 1) = i sqrt(3)
   ≈ 1.7320508075688772935274463415058723669428052538104 i.
```

This point satisfies `ψ₃(x₀) = 0`, hence is a nonzero `3`-torsion point over `ℂ`.

The tangent deformation with `dx = 1` is

```text
Pε = (x₀ + ε, y₀ + ε s),
s  = 3 x₀^2 / (2 y₀)
   ≈ -2.1822472719434428071201452283796177626517466774806 i.
```

The input invariant-differential coefficient is

```text
input = dx / (2 y₀) = 1 / (2 y₀)
      ≈ -0.28867513459481288225457439025097872782380087563506 i.
```

## Jacobian formulas used

The computation uses Jacobian coordinates

```text
x = X / Z^2,
y = Y / Z^3,
```

so the projective/local parameter at `O` is

```text
t = -X Z / Y.
```

The CAS used standard short-Weierstrass `A = 0` Jacobian doubling and generic addition formulas over dual numbers `a + bε`, `ε² = 0`.

## CAS output

With

```text
Qε = [2]Pε,
Rε = [3]Pε = Qε + Pε,
```

the Jacobian addition formula gives, numerically,

```text
Rε.X = 82944
       - 522514.45781240179889225758305042686154849468744103 ε,

Rε.Y = -23887872
       + 225726245.77495757712145527587778440418894970497453 ε,

Rε.Z = -249.41531628991833026795227317684562083976395654869 i · ε.
```

The constant term is

```text
R₀ = [82944 : -23887872 : 0]
   = [288^2 : -288^3 : 0],
```

which is a valid Jacobian-coordinate representative of `O`.

The raw `Z` coefficient therefore satisfies

```text
Zcoeff / input = 864 = 288 · 3.
```

The extra factor `288` is exactly the Jacobian-coordinate unit coming from the chosen representative of `O`.  Since

```text
-X₀ / Y₀ = -82944 / (-23887872) = 1 / 288,
```

the local parameter coefficient is

```text
coeffε(t(Rε)) = coeffε(-Rε.X · Rε.Z / Rε.Y)
              = (1/288) · Zcoeff
              ≈ -0.86602540378443864676372317075293618347140262690515 i.
```

Hence

```text
coeffε(t([3]Pε)) / input
  = (-0.86602540378443864676372317075293618347140262690515 i)
    / (-0.28867513459481288225457439025097872782380087563506 i)
  = 3.0000000000000000000000000000000000000000000000000.
```

So the CAS verification succeeds:

```text
coeffε(t([3]Pε)) = 3 · coeffε(input tangent).
```

Equivalently, at the raw Jacobian `Z` level,

```text
Zcoeff = 288 · 3 · input,
```

and the explicit unit `1/288` in `t = -XZ/Y` removes the coordinate scaling.

## Complete Python/mpmath script

```python
import mpmath as mp
mp.mp.dps = 50

class D:
    """Dual number a + b eps, eps^2 = 0."""
    __slots__ = ("a", "b")
    def __init__(self, a, b=0):
        self.a = mp.mpc(a)
        self.b = mp.mpc(b)
    def __add__(self, other):
        other = toD(other)
        return D(self.a + other.a, self.b + other.b)
    __radd__ = __add__
    def __sub__(self, other):
        other = toD(other)
        return D(self.a - other.a, self.b - other.b)
    def __rsub__(self, other):
        other = toD(other)
        return D(other.a - self.a, other.b - self.b)
    def __neg__(self):
        return D(-self.a, -self.b)
    def __mul__(self, other):
        other = toD(other)
        return D(self.a * other.a, self.a * other.b + self.b * other.a)
    __rmul__ = __mul__
    def inv(self):
        return D(1 / self.a, -self.b / (self.a * self.a))
    def __truediv__(self, other):
        other = toD(other)
        return self * other.inv()
    def __rtruediv__(self, other):
        other = toD(other)
        return other * self.inv()
    def __pow__(self, n):
        assert isinstance(n, int)
        if n == 0:
            return D(1, 0)
        if n < 0:
            return self.inv() ** (-n)
        out = D(1, 0)
        base = self
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

def toD(x):
    return x if isinstance(x, D) else D(x, 0)

def dbl(P):
    # Jacobian doubling for y^2 = x^3 + 1, so A = 0.
    X1, Y1, Z1 = map(toD, P)
    XX = X1 * X1
    YY = Y1 * Y1
    YYYY = YY * YY
    S = 2 * ((X1 + YY) * (X1 + YY) - XX - YYYY)
    M = 3 * XX
    T = M * M - 2 * S
    X3 = T
    Y3 = M * (S - T) - 8 * YYYY
    Z3 = (Y1 + Z1) * (Y1 + Z1) - YY - Z1 * Z1
    return (X3, Y3, Z3)

def add(P, Q):
    # Standard Jacobian addition formula.
    X1, Y1, Z1 = map(toD, P)
    X2, Y2, Z2 = map(toD, Q)
    Z1Z1 = Z1 * Z1
    Z2Z2 = Z2 * Z2
    U1 = X1 * Z2Z2
    U2 = X2 * Z1Z1
    S1 = Y1 * Z2 * Z2Z2
    S2 = Y2 * Z1 * Z1Z1
    H = U2 - U1
    I = (2 * H) * (2 * H)
    J = H * I
    r = 2 * (S2 - S1)
    V = U1 * I
    X3 = r * r - J - 2 * V
    Y3 = r * (V - X3) - 2 * S1 * J
    Z3 = ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) * H
    return (X3, Y3, Z3)

# Correct division polynomial for y^2 = x^3 + 1:
# ψ3 = 3*x^4 + 12*x = 3*x*(x^3 + 4).
x0 = -mp.power(4, mp.mpf(1) / 3)
y0 = mp.sqrt(x0**3 + 1)       # i*sqrt(3)
s = 3 * x0**2 / (2 * y0)      # tangent slope, dx = 1
input_coeff = 1 / (2 * y0)

P = (D(x0, 1), D(y0, s), D(1, 0))
Q = dbl(P)
R = add(Q, P)                  # [3]Pε

X0, Y0, Z0 = R[0].a, R[1].a, R[2].a
Zcoeff = R[2].b
unit = -X0 / Y0
Tcoeff = unit * Zcoeff

print("x0        =", x0)
print("y0        =", y0)
print("s         =", s)
print("input     =", input_coeff)
print("R.X       =", R[0].a, "+ eps *", R[0].b)
print("R.Y       =", R[1].a, "+ eps *", R[1].b)
print("R.Z       =", R[2].a, "+ eps *", R[2].b)
print("Z/input   =", Zcoeff / input_coeff)
print("unit      =", unit)
print("tcoeff    =", Tcoeff)
print("t/input   =", Tcoeff / input_coeff)

# Sanity check for the typed but incorrect polynomial 3*x^4 + 12*x - 1.
roots_bad = mp.polyroots([3, 0, 0, 12, -1])
r_bad = roots_bad[1]
print("bad root  =", r_bad)
print("actual ψ3 at bad root =", 3 * r_bad**4 + 12 * r_bad)
```

The final lines print

```text
Z/input = 864.0
unit    = 0.0034722222222222222222222222222222222222222222222222
        = 1/288
t/input = 3.0
```

## Negative-slope sanity check

If one uses the sign from the prompt,

```text
s = -3x₀^2/(2y₀),
```

then the first-order curve equation fails:

```text
2y₀s - 3x₀² ≠ 0.
```

For the same nonzero torsion point above, the CAS gives a meaningless local-parameter ratio `-21` rather than `3`, exactly because the deformation is not tangent to the curve.
