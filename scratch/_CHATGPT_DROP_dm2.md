# Q396 / dm2 — affine addition over dual numbers for `[3](P + ε)`

Short runnable script.  It follows the affine doubling/secant formulas, but keeps the final secant denominator `H` projectivized so the pole at `O` can be read as

```text
t = -x/y = -X·H/Y.
```

With the data exactly as typed in the prompt (`3*x^4 + 12*x - 1` and the negative slope), the script reports that `[3]P` is **not** at infinity and no tangent-multiplier test is being performed.  Flip `PROMPT_AS_TYPED = False` to run the actual `3`-torsion test on `y² = x³+1`; then the output verifies `tcoeff = 3/(2*y0)`.

```python
import mpmath as mp
mp.mp.dps = 50

PROMPT_AS_TYPED = True

class D:
    """Dual number a + b*e, e^2 = 0."""
    def __init__(self, a, b=0):
        self.a, self.b = mp.mpc(a), mp.mpc(b)
    @staticmethod
    def of(z):
        return z if isinstance(z, D) else D(z)
    def __add__(self, z):
        z = D.of(z); return D(self.a + z.a, self.b + z.b)
    __radd__ = __add__
    def __sub__(self, z):
        z = D.of(z); return D(self.a - z.a, self.b - z.b)
    def __rsub__(self, z):
        z = D.of(z); return D(z.a - self.a, z.b - self.b)
    def __neg__(self):
        return D(-self.a, -self.b)
    def __mul__(self, z):
        z = D.of(z); return D(self.a*z.a, self.a*z.b + self.b*z.a)
    __rmul__ = __mul__
    def inv(self):
        if abs(self.a) < mp.mpf("1e-45"):
            raise ZeroDivisionError("not a unit in K[e]/e^2; affine coord has a pole")
        return D(1/self.a, -self.b/self.a**2)
    def __truediv__(self, z):
        return self * D.of(z).inv()
    def __rtruediv__(self, z):
        return D.of(z) * self.inv()

def dbl(P):
    # y^2 = x^3 + 1, so a1=a2=a3=a4=0.
    x, y = P
    lam = 3*x*x/(2*y)
    x2 = lam*lam - 2*x
    y2 = lam*(x - x2) - y
    return x2, y2

def add_projectivized(P1, P2):
    # Secant addition formula, but do not divide by H.
    # If H is a unit, this is affine addition with x=X/H^2, y=Y/H^3.
    # If H has zero constant term, this records the pole at infinity.
    x1, y1 = P1
    x2, y2 = P2
    H = x2 - x1
    R = y2 - y1
    X = R*R - (x1 + x2)*H*H
    Y = R*(x1*H*H - X) - y1*H*H*H
    return X, Y, H

if PROMPT_AS_TYPED:
    # Root requested in the prompt.  This is not a 3-torsion root for E: y^2=x^3+1.
    x0 = mp.findroot(lambda x: 3*x**4 + 12*x - 1, (mp.mpf("0"), mp.mpf("0.2")))
    y0 = mp.sqrt(x0**3 + 1)
    s = -(3*x0**2)/(2*y0)       # as typed; not tangent on y^2=x^3+1
else:
    # Actual nonzero 3-torsion: psi3 = 3*x^4 + 12*x = 3*x*(x^3+4).
    x0 = -mp.power(4, mp.mpf(1)/3)
    y0 = mp.sqrt(x0**3 + 1)     # = i*sqrt(3)
    s = (3*x0**2)/(2*y0)        # true tangent: 2*y0*s = 3*x0^2

P = (D(x0, 1), D(y0, s))
Q = dbl(P)
X, Y, H = add_projectivized(Q, P)  # [3]P_e = Q + P

target = 3/(2*y0)
print("x0               =", mp.nstr(x0, 50))
print("y0               =", mp.nstr(y0, 50))
print("s                =", mp.nstr(s, 50))
print("correct psi3     =", mp.nstr(3*x0**4 + 12*x0, 50))
print("prompt poly      =", mp.nstr(3*x0**4 + 12*x0 - 1, 50))
print("tangent residual =", mp.nstr(2*y0*s - 3*x0**2, 50))
print("H = H0 + e H1   =", mp.nstr(H.a, 30), "+ e*", mp.nstr(H.b, 30))

if abs(H.a) > mp.mpf("1e-40"):
    # No pole: affine x,y are finite, so [3]P is not O.
    t = -(X*H)/Y
    print("[3]P is not O; affine coords do not blow up.")
    print("t0               =", mp.nstr(t.a, 50))
    print("teps             =", mp.nstr(t.b, 50))
    print("3/(2*y0)         =", mp.nstr(target, 50))
    print("teps/target      =", mp.nstr(t.b/target, 50))
else:
    # H = e*H1.  Since t=-X*H/Y, coeff_e(t)=(-X0/Y0)*H1.
    tcoeff = (-X.a/Y.a) * H.b
    print("[3]P is O to constant order; extracting local parameter.")
    print("tcoeff           =", mp.nstr(tcoeff, 50))
    print("3/(2*y0)         =", mp.nstr(target, 50))
    print("tcoeff/target    =", mp.nstr(tcoeff/target, 50))
```

In the prompt-as-typed mode, the key lines are

```text
correct psi3     = 1.0
prompt poly      = 0.0
tangent residual = -0.0416546181821225...
H = H0 + e H1   = 0.249855470425585... + e* 2.99479467933090...
[3]P is not O; affine coords do not blow up.
teps/target      = 1.00172404023635...
```

In the corrected true-`3`-torsion mode, the key lines are

```text
correct psi3     = 0.0
prompt poly      = -1.0
tangent residual = 0.0
H = H0 + e H1   = 0.0 + e* 3.0
[3]P is O to constant order; extracting local parameter.
tcoeff/target    = 1.0
```
