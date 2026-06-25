# Q383 / dm2 — simple CAS script for tangent multiplier `3`

Short runnable script.  It keeps the final addition in projectivized form because, at true `3`-torsion, the affine denominator `x(P) - x([2]P)` has zero constant term and is not invertible in `K[ε]/(ε²)`.

One important correction is encoded as the default: for `E : y² = x³ + 1`, the standard third division polynomial is `ψ₃ = 3*x^4 + 12*x`, not `3*x^4 + 12*x - 1`.  Set `PROMPT_DATA = True` to run the polynomial/sign exactly as typed; it prints that `[3]P` is not `O`, so there is no tangent-multiplier-at-`O` test.

```python
# q383.py
import mpmath as mp
mp.mp.dps = 50

PROMPT_DATA = False  # True uses x root of 3*x^4 + 12*x - 1 and negative slope; it fails.

class D:
    """Dual number a + b*e with e^2 = 0."""
    def __init__(self, a, b=0):
        self.a, self.b = mp.mpc(a), mp.mpc(b)
    def __add__(self, o):
        o = D.of(o); return D(self.a + o.a, self.b + o.b)
    __radd__ = __add__
    def __sub__(self, o):
        o = D.of(o); return D(self.a - o.a, self.b - o.b)
    def __rsub__(self, o):
        o = D.of(o); return D(o.a - self.a, o.b - self.b)
    def __neg__(self):
        return D(-self.a, -self.b)
    def __mul__(self, o):
        o = D.of(o); return D(self.a * o.a, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__
    def inv(self):
        return D(1 / self.a, -self.b / self.a**2)
    def __truediv__(self, o):
        return self * D.of(o).inv()
    def __rtruediv__(self, o):
        return D.of(o) * self.inv()
    @staticmethod
    def of(o):
        return o if isinstance(o, D) else D(o)

def dbl_aff(P):
    # Affine doubling on y^2 = x^3 + 1.
    x, y = P
    lam = 3 * x * x / (2 * y)
    x2 = lam * lam - 2 * x
    y2 = lam * (x - x2) - y
    return x2, y2

def add_aff_projectivized(P, Q):
    # Same affine addition formula, but without dividing by H = x2 - x1.
    # It returns Jacobian coords X,Y,Z with x = X/Z^2 and y = Y/Z^3.
    x1, y1 = P
    x2, y2 = Q
    H = x2 - x1
    R = y2 - y1
    X = R * R - (x1 + x2) * H * H
    Y = R * (x1 * H * H - X) - y1 * H * H * H
    Z = H
    return X, Y, Z

if PROMPT_DATA:
    # As typed in the prompt.  This is not actual 3-torsion on y^2=x^3+1.
    x0 = mp.findroot(lambda x: 3*x**4 + 12*x - 1, (mp.mpf("0"), mp.mpf("0.2")))
    y0 = mp.sqrt(x0**3 + 1)
    s = -(3 * x0**2) / (2 * y0)
else:
    # Correct 3-torsion: root of ψ3 = 3*x^4 + 12*x = 3*x*(x^3+4).
    x0 = -mp.power(4, mp.mpf(1) / 3)
    y0 = mp.sqrt(x0**3 + 1)      # = i*sqrt(3)
    s = (3 * x0**2) / (2 * y0)   # tangent condition: 2*y0*s = 3*x0^2

P = (D(x0, 1), D(y0, s))
Q = dbl_aff(P)                   # [2]Pε, affine is OK here
X, Y, Z = add_aff_projectivized(Q, P)  # [3]Pε in Jacobian coords

input_coeff = 1 / (2 * y0)
print("x0       =", mp.nstr(x0, 50))
print("y0       =", mp.nstr(y0, 50))
print("s        =", mp.nstr(s, 50))
print("Z0       =", mp.nstr(Z.a, 30))
print("Zeps     =", mp.nstr(Z.b, 30))

if abs(Z.a) > mp.mpf("1e-40"):
    print("[3]P is not O; no local-parameter multiplier test at O.")
else:
    # Local parameter at O in Jacobian coords: t = -X*Z/Y.
    # Since Z0 = 0, coeff_e(t) = (-X0/Y0) * coeff_e(Z).
    tcoeff = (-X.a / Y.a) * Z.b
    ratio = tcoeff / input_coeff
    print("input    =", mp.nstr(input_coeff, 50))
    print("tcoeff   =", mp.nstr(tcoeff, 50))
    print("t/input  =", mp.nstr(ratio, 50))
    assert abs(ratio - 3) < mp.mpf("1e-40")
```

Expected output in the default corrected mode ends with

```text
Z0       = 0.0
Zeps     = 3.0
input    = (0.0 - 0.28867513459481288225457439025097872782380087563506j)
tcoeff   = (0.0 - 0.86602540378443864676372317075293618347140262690519j)
t/input  = (3.0 + 0.0j)
```
