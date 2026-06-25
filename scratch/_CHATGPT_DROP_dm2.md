# Q433 / dm2 — CAS: compute `u(t)=w(t)/t³` to `O(t¹⁰)`

We start from

```text
w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³.
```

Writing `w = t³u`, the equation becomes an ordinary power-series recursion:

```text
u = 1 + a₁tu + a₂t²u + a₃t³u² + a₄t⁴u² + a₆t⁶u³.
```

Thus `u(0)=1`, so `u` is a unit power series.

## Result

Modulo `t¹⁰`, i.e. keeping terms through `t⁹`,

```text
u(t) = 1
+ a₁ t
+ (a₁² + a₂)t²
+ (a₁³ + 2a₁a₂ + a₃)t³
+ (a₁⁴ + 3a₁²a₂ + 3a₁a₃ + a₂² + a₄)t⁴
+ (a₁⁵ + 4a₁³a₂ + 6a₁²a₃ + 3a₁a₂² + 3a₁a₄ + 3a₂a₃)t⁵
+ (a₁⁶ + 5a₁⁴a₂ + 10a₁³a₃ + 6a₁²a₂² + 6a₁²a₄
   + 12a₁a₂a₃ + a₂³ + 3a₂a₄ + 2a₃² + a₆)t⁶
+ (a₁⁷ + 6a₁⁵a₂ + 15a₁⁴a₃ + 10a₁³a₂² + 10a₁³a₄
   + 30a₁²a₂a₃ + 4a₁a₂³ + 12a₁a₂a₄ + 10a₁a₃²
   + 4a₁a₆ + 6a₂²a₃ + 4a₃a₄)t⁷
+ (a₁⁸ + 7a₁⁶a₂ + 21a₁⁵a₃ + 15a₁⁴a₂² + 15a₁⁴a₄
   + 60a₁³a₂a₃ + 10a₁²a₂³ + 30a₁²a₂a₄ + 30a₁²a₃²
   + 10a₁²a₆ + 30a₁a₂²a₃ + 20a₁a₃a₄ + a₂⁴
   + 6a₂²a₄ + 10a₂a₃² + 4a₂a₆ + 2a₄²)t⁸
+ (a₁⁹ + 8a₁⁷a₂ + 28a₁⁶a₃ + 21a₁⁵a₂² + 21a₁⁵a₄
   + 105a₁⁴a₂a₃ + 20a₁³a₂³ + 60a₁³a₂a₄ + 70a₁³a₃²
   + 20a₁³a₆ + 90a₁²a₂²a₃ + 60a₁²a₃a₄ + 5a₁a₂⁴
   + 30a₁a₂²a₄ + 60a₁a₂a₃² + 20a₁a₂a₆ + 10a₁a₄²
   + 10a₂³a₃ + 20a₂a₃a₄ + 5a₃³ + 5a₃a₆)t⁹
+ O(t¹⁰).
```

The same script also computes the first homogeneous pieces of the formal group law.  With `T₁=rU`, `T₂=rV`, the coefficient of `r^d` is the degree-`d` homogeneous part.  It prints

```text
degree 1: U + V
degree 2: -U*V*a1
degree 3: -U*V*a2*(U + V)
```

So

```text
F(T₁,T₂) = T₁ + T₂ - a₁T₁T₂ - a₂T₁T₂(T₁+T₂) + O(total degree 4),
```

and in particular

```text
F(T₁,T₂) = T₁ + T₂ + O(total degree ≥ 2),
```

with degree-2 term

```text
-a₁T₁T₂.
```

## Runnable SymPy script

```python
import sympy as sp

t, r, U, V = sp.symbols("t r U V")
a1, a2, a3, a4, a6 = sp.symbols("a1 a2 a3 a4 a6")

# ---------- u(t)=w(t)/t^3 mod t^10 ----------
# After w=t^3*u, the defining equation becomes
# u = 1 + a1*t*u + a2*t^2*u + a3*t^3*u^2 + a4*t^4*u^2 + a6*t^6*u^3.
N = 10

def padd(p, q):
    return [sp.expand(p[i] + q[i]) for i in range(N)]

def shift(c, k, p):
    out = [0]*N
    for i in range(N-k):
        out[i+k] = sp.expand(c*p[i])
    return out

def pmul(p, q):
    out = [0]*N
    for i in range(N):
        for j in range(N-i):
            out[i+j] += p[i]*q[j]
    return [sp.expand(x) for x in out]

u = [0]*N
for _ in range(N+2):
    u2, u3 = pmul(u, u), pmul(pmul(u, u), u)
    new = [0]*N
    new[0] = 1
    for term in [shift(a1,1,u), shift(a2,2,u), shift(a3,3,u2),
                 shift(a4,4,u2), shift(a6,6,u3)]:
        new = padd(new, term)
    if new == u:
        break
    u = new

u_expr = sum(u[i]*t**i for i in range(N))
print("u(t) mod t^10 =")
print(sp.collect(u_expr, t))
print("u(0) =", u[0])

# ---------- formal group check through total degree 3 ----------
# Substitute t1=r*U, t2=r*V and do Laurent arithmetic in r.
# Coeff r^d is the homogeneous degree-d part in (T1,T2).

MAX, MIN = 5, -10

class LS:
    def __init__(self, d=None):
        self.d = {}
        if d:
            for k, v in d.items():
                if MIN <= k <= MAX and v != 0:
                    self.d[int(k)] = sp.cancel(v)
    @staticmethod
    def mon(k, c=1):
        return LS({k: c})
    def __add__(self, other):
        other = toLS(other)
        d = dict(self.d)
        for k, v in other.d.items():
            d[k] = d.get(k, 0) + v
        return LS({k: sp.cancel(v) for k, v in d.items() if v != 0})
    __radd__ = __add__
    def __neg__(self):
        return LS({k: -v for k, v in self.d.items()})
    def __sub__(self, other):
        return self + (-toLS(other))
    def __rsub__(self, other):
        return toLS(other) + (-self)
    def __mul__(self, other):
        other = toLS(other)
        d = {}
        for i, ai in self.d.items():
            for j, bj in other.d.items():
                k = i+j
                if MIN <= k <= MAX:
                    d[k] = d.get(k, 0) + ai*bj
        return LS({k: sp.cancel(v) for k, v in d.items() if v != 0})
    __rmul__ = __mul__
    def inv(self):
        e = min(self.d)
        a0 = self.d[e]
        b = {-e: 1/a0}
        for n in range(1, MAX + e + 1):
            b[-e+n] = -sum(self.d.get(e+i, 0)*b.get(-e+n-i, 0)
                            for i in range(1, n+1))/a0
        return LS({k: sp.cancel(v) for k, v in b.items()})
    def __truediv__(self, other):
        return self * toLS(other).inv()
    def __rtruediv__(self, other):
        return toLS(other) * self.inv()
    def coeff(self, k):
        return sp.factor(sp.cancel(self.d.get(k, 0)))

def toLS(x):
    return x if isinstance(x, LS) else LS({0: x})

T1, T2 = LS.mon(1, U), LS.mon(1, V)

def u_at(T):
    out, p = LS(), LS.mon(0, 1)
    for ci in u:
        out = out + ci*p
        p = p*T
    return out

w1, w2 = T1*T1*T1*u_at(T1), T2*T2*T2*u_at(T2)
x1, x2 = T1/w1, T2/w2
y1, y2 = -1/w1, -1/w2

lam = (y2-y1)/(x2-x1)
nu  = (y1*x2-y2*x1)/(x2-x1)
x3  = lam*lam + a1*lam - a2 - x1 - x2
y3  = -(lam+a1)*x3 - nu - a3
F   = -x3/y3

print("\nFormal group homogeneous pieces:")
print("degree 1:", F.coeff(1))
print("degree 2:", F.coeff(2))
print("degree 3:", F.coeff(3))
print("\nSo F(T1,T2) = T1 + T2 - a1*T1*T2 + O(total degree 3).")
```
