## Q990 exact result

- SymPy version: `1.14.0`
- reduced denominator scale for standard Y: `1`
- reduced denominator scale for negAddY: `1`
- raw/reduced standard-numerator multiplier: `4`
- primitive standard numerator terms: `382`
- compact coefficient expanded terms: `239`
- compact coefficient degree in Z: `3`
- compact coefficient SHA-256: `57ca58009baee7b8c8cbbec2373bf38d0f86cd17045d175755314de2c1ce19a5`
- `N_std = CY*(z-F0)` verified exactly
- `N_neg = (-CY)*(z-F0)` verified exactly
- `N_neg = (-CY)*hcurve1 + (-CY)*htors` verified exactly

## Q971 differentiated relation

`(DX*delta(CX)-CX*delta(DX))/e` is polynomial.
The exact correction is `d*t*p^2*V^2`, so
`CY = (DX*delta(CX)-CX*delta(DX))/e - d*t*p^2*V^2`.
- correction expanded terms: `210`
- correction SHA-256: `f95af1cc8482b3fc21f2a0a6b3fe5fec7d1b88a5c8be6b0da93e1d6abfcf8442`

## Exact factorization over QQ[x1,A,r,Z]

- content: `-1`
- nonconstant factor count: `2`
- factor 1: exponent `1`, terms `2`, SHA-256 `94736faeda9a073173865b0c8db591daf4a821eaf7ecc8e0b1f8f4871e8ec172`
  - `A + 3*r**2`
- factor 2: exponent `1`, terms `186`, SHA-256 `5cfbc90941e807838532d6914848729c4100174edc5122535b2c989479fd1bb2`
- gcd(CY, Q971_CX): `A + 3*r**2`

## Compact definitions

```text
z  = y1^2
t  = 3*r^2 + A
d  = x1-r
e  = d^2-t
u  = 3*x1^2+A
m  = x1*d+t
p  = 3*m^2+(A-5*t)*d^2
h  = 2*x1+r
F0 = x1^3+A*x1-r^3-A*r
k  = 2*t-d*h
S  = u^2*k-12*t*(x1+r)*(z+F0)
V  = u^2-4*h*z
pd = 6*m*(x1+d)+2*(A-5*t)*d
Sd = 12*x1*u*k-u^2*(h+2*d)-12*t*((z+F0)+2*(x1+r)*u)
Vd = 12*x1*u-8*z-4*h*u
CX = d*h*p^2+e^2*S
CXd = (h+2*d)*p^2+2*d*h*p*pd+4*d*e*S+e^2*Sd
Dbar = e*V*(z+d*u)+d*z*(4*d*V+e*Vd)
CY = d*z*e*V*CXd-CX*Dbar-d*t*p^2*V^2
```

For the requested `LHS-RHS` using Mathlib `negAddY`:

```text
c1 = c2 = -CY
```
