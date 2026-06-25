# Q388 / dm2 — CAS computation of the Weierstrass formal group to degree 3

Curve:

```text
y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆.
```

Use the standard formal parameter

```text
t = -x/y,   w = -1/y,
```

so that

```text
x(t) = t / w(t),   y(t) = -1 / w(t).
```

Substituting into the Weierstrass equation gives

```text
w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³.
```

## Series for `w`, `x`, and `y`

Solving iteratively gives

```text
w(t) = t³
     + a₁ t⁴
     + (a₁² + a₂) t⁵
     + (a₁³ + 2a₁a₂ + a₃) t⁶
     + (a₁⁴ + 3a₁²a₂ + 3a₁a₃ + a₂² + a₄) t⁷
     + O(t⁸).
```

Thus

```text
x(t) = t⁻² - a₁t⁻¹ - a₂ - a₃t - (a₁a₃ + a₄)t² + O(t³),

y(t) = -t⁻³ + a₁t⁻² + a₂t⁻¹ + a₃ + (a₁a₃ + a₄)t + O(t²).
```

## Addition formula used

For two affine points `Pᵢ = (xᵢ,yᵢ)`, write

```text
λ = (y₂ - y₁)/(x₂ - x₁),
ν = (y₁x₂ - y₂x₁)/(x₂ - x₁).
```

The sum is

```text
x₃ = λ² + a₁λ - a₂ - x₁ - x₂,
y₃ = -(λ + a₁)x₃ - ν - a₃.
```

Then

```text
F(T₁,T₂) = -x₃/y₃.
```

## Result

The degree-3 truncation is

```text
F(T₁,T₂)
  = T₁ + T₂
    - a₁ T₁T₂
    - a₂(T₁²T₂ + T₁T₂²)
    + O(total degree 4).
```

Equivalently,

```text
degree 1:  T₁ + T₂
degree 2: -a₁ T₁T₂
degree 3: -a₂ T₁T₂(T₁ + T₂).
```

So the linear coefficients of the formal group law are both `1`, as expected.

## Runnable SymPy script

```python
import sympy as sp

t, r, U, V = sp.symbols('t r U V')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')

# 1. Solve w = t^3 + a1*t*w + a2*t^2*w + a3*w^2 + a4*t*w^2 + a6*w^3.
N = 8                       # computes through t^7, i.e. O(t^8)
c = sp.symbols(f'c0:{N}')
w_unknown = sum(c[i] * t**i for i in range(N))
eq = w_unknown - (t**3 + a1*t*w_unknown + a2*t**2*w_unknown
                  + a3*w_unknown**2 + a4*t*w_unknown**2 + a6*w_unknown**3)
sol = {c[0]: 0, c[1]: 0, c[2]: 0}
for k in range(3, N):
    sol[c[k]] = sp.solve(sp.Eq(sp.expand(eq.subs(sol)).coeff(t, k), 0), c[k])[0]
w = sp.expand(w_unknown.subs(sol))
print('w(t) =', w, '+ O(t^8)')

# 2. Laurent expansions.
x = sp.series(t / w, t, 0, 3).removeO()
y = sp.series(-1 / w, t, 0, 2).removeO()
print('x(t) =', sp.collect(sp.expand(x), t), '+ O(t^3)')
print('y(t) =', sp.collect(sp.expand(y), t), '+ O(t^2)')

# 3. Affine addition formula, expanded by scaling t1=r*U, t2=r*V.
#    lambda=(y2-y1)/(x2-x1), nu=(y1*x2-y2*x1)/(x2-x1),
#    x3=lambda^2+a1*lambda-a2-x1-x2, y3=-(lambda+a1)*x3-nu-a3.
#    Using x=t/w, y=-1/w gives
#      lambda=(w2-w1)/(t2*w1-t1*w2), nu=(t1-t2)/(t2*w1-t1*w2).
S, P = U + V, U * V
b2 = a1**2 + a2
B0 = U**2 + U*V + V**2
B1 = U**3 + U**2*V + U*V**2 + V**3
B2 = U**4 + U**3*V + U**2*V**2 + U*V**3 + V**4

# lambda = r^-1*l + m + r*n + O(r^2)
Q = (B0 + a1*r*B1 + b2*r**2*B2) / (S + a1*r*B0 + b2*r**2*B1)
Q = sp.series(Q, r, 0, 3).removeO()
l = sp.factor(sp.cancel(-Q.coeff(r, 0) / P))
m = sp.factor(sp.cancel(-Q.coeff(r, 1) / P))
n = sp.factor(sp.cancel(-Q.coeff(r, 2) / P))

# x(ti)=r^-2/U_i^2 - a1*r^-1/U_i - a2 + O(r).
A = sp.cancel(l**2 - (1/U**2 + 1/V**2))
B = sp.cancel(2*l*m + a1*l + a1*(1/U + 1/V))
C = sp.cancel(m**2 + 2*l*n + a1*m + a2)

# nu = r^-3*N0 + r^-2*N1 + r^-1*N2 + O(1)
N0 = 1/(P*S)
N1 = -a1*B0/(P*S**2)
N2 = (a1**2*B0**2/S**3 - b2*B1/S**2)/P

# y3 = r^-3*D0 + r^-2*D1 + r^-1*D2 + O(1)
D0 = sp.cancel(-(l*A) - N0)
D1 = sp.cancel(-(l*B + (m+a1)*A) - N1)
D2 = sp.cancel(-(l*C + (m+a1)*B + n*A) - N2)

# F=-x3/y3 = r*f1 + r^2*f2 + r^3*f3 + O(r^4).
f1 = sp.factor(sp.cancel(-A/D0))
f2 = sp.factor(sp.cancel(-(B/D0 - A*D1/D0**2)))
f3 = sp.factor(sp.cancel(-(C/D0 - B*D1/D0**2 + A*(D1**2/D0**3 - D2/D0**2))))
print('degree 1 =', f1)
print('degree 2 =', f2)
print('degree 3 =', f3)
print('F(T1,T2) = T1 + T2 - a1*T1*T2 - a2*T1*T2*(T1+T2) + O(deg 4)')
```

Expected output ends with

```text
degree 1 = U + V
degree 2 = -U*V*a1
degree 3 = -U*V*a2*(U + V)
F(T1,T2) = T1 + T2 - a1*T1*T2 - a2*T1*T2*(T1+T2) + O(deg 4)
```
