# Q400 / dm2 — CAS certificate for `n = 5` separability

Goal: compute the resultant certificate for the degree-12 polynomial `preΨ'_5 = preΨ_5` for a general Weierstrass curve, using the `b`-invariants.

Curve:

```text
y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆.
```

Use

```text
b₂ = a₁² + 4a₂,
b₄ = 2a₄ + a₁a₃,
b₆ = a₃² + 4a₆,
4b₈ = b₂b₆ - b₄²,
Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆.
```

The relation `4b₈ = b₂b₆ - b₄²` is essential for the clean power-of-`Δ` resultant.  If `b₂,b₄,b₆,b₈` are treated as algebraically independent, the resultant is not just a scalar times `Δ^22`.

## `preΨ₅`

For odd `n = 5`, `preΨ'_5 = preΨ_5`, and the leading coefficient is `5`.

Using

```text
ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈,
ψ₂² = 4X³ + b₂X² + 2b₄X + b₆,
ψ₄/ψ₂ = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X²
        + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²),
ψ₅ = (ψ₂²)²(ψ₄/ψ₂) - ψ₃³,
```

one gets

```text
preΨ₅ =
  5X¹²
+ 5b₂X¹¹
+ (b₂² + 31b₄)X¹⁰
+ (10b₂b₄ + 95b₆)X⁹
+ (38b₂b₆ + 7b₄² + 133b₈)X⁸
+ (3b₂²b₆ - 3b₂b₄² + 78b₂b₈ + 30b₄b₆)X⁷
+ (15b₂²b₈ - 8b₂b₄b₆ - 7b₄³ + 122b₄b₈ - 15b₆²)X⁶
+ (b₂³b₈ - b₂²b₄b₆ + 46b₂b₄b₈ - 14b₂b₆² - 37b₄²b₆ + 26b₆b₈)X⁵
+ (5b₂²b₄b₈ - b₂²b₆² - 4b₂b₄²b₆ + 10b₂b₆b₈
   + 29b₄²b₈ - 60b₄b₆² - 9b₈²)X⁴
+ (2b₂²b₆b₈ + 8b₂b₄²b₈ - 6b₂b₄b₆² - 3b₂b₈²
   - 4b₄³b₆ - 6b₄b₆b₈ - 25b₆³)X³
+ (6b₂b₄b₆b₈ - 2b₂b₆³ + 4b₄³b₈ - 8b₄²b₆²
   - 9b₄b₈² - 17b₆²b₈)X²
+ (b₂b₆²b₈ + 4b₄²b₆b₈ - 5b₄b₆³ - 9b₆b₈²)X
+ (b₄b₆²b₈ - b₆⁴ - b₈³).
```

## Resultant

After imposing `4b₈ = b₂b₆ - b₄²`, the certificate is

```text
Res_X(preΨ₅, d(preΨ₅)/dX) = 5¹² · Δ²².
```

So the exponent is

```text
k = 22.
```

Weighted-degree check: `X,b₂,b₄,b₆,b₈` have weights `2,2,4,6,8`; roots have weight `2`; `preΨ₅` has degree `12`; hence the resultant weight is

```text
4 * binom(12,2) = 264 = 22 * 12 = weight(Δ²²).
```

The scalar is found from the exact specialization `y² = x³ + 1`, where

```text
b₂ = 0, b₄ = 0, b₆ = 4, b₈ = 0, Δ = -432,
preΨ₅ = 5X¹² + 380X⁹ - 240X⁶ - 1600X³ - 256,
Res(preΨ₅, preΨ₅') = 2⁸⁸ · 3⁶⁶ · 5¹² = 5¹² · (-432)²².
```

## Bezout cofactors

The general Bezout cofactors in `Q(b₂,b₄,b₆,b₈)[X]` are not included here.  In SymPy they are not tractable for the requested `≤ 500`-term cutoff; the useful small certificate for Lean is the resultant identity above.  If a later Lean step truly needs explicit cofactors, compute them in a specialized quotient or use a resultant/Bézout theorem rather than trying to inline the universal cofactors.

## Runnable SymPy script

This script computes `preΨ₅`, its derivative, verifies the exact specialization, and checks several exact samples after imposing `b_relation`.

```python
import sympy as sp

X = sp.symbols("X")
b2, b4, b6, b8 = sp.symbols("b2 b4 b6 b8")

Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
b8_rel = (b2*b6 - b4**2) / 4

psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
psi2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
psi4_over_psi2 = (
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)

prepsi5 = sp.expand(psi2_sq**2 * psi4_over_psi2 - psi3**3)
dprepsi5 = sp.diff(prepsi5, X)

print("deg prepsi5 =", sp.degree(prepsi5, X))
print("LC prepsi5  =", sp.LC(prepsi5, X))
print("prepsi5     =", sp.collect(prepsi5, X))
print("dprepsi5    =", sp.collect(dprepsi5, X))

# Exact one-variable specialization y^2 = x^3 + 1.
spec = {b2: 0, b4: 0, b6: 4, b8: 0}
f_spec = sp.expand(prepsi5.subs(spec))
R_spec = sp.resultant(f_spec, sp.diff(f_spec, X), X)
Delta_spec = sp.expand(Delta.subs(spec))

print("\nSpecialization y^2=x^3+1")
print("f_spec       =", f_spec)
print("Delta_spec   =", Delta_spec)
print("factor Res   =", sp.factorint(int(R_spec)))
print("factor RHS   =", sp.factorint(int(5**12 * Delta_spec**22)))
assert R_spec == 5**12 * Delta_spec**22

# Check more exact samples satisfying 4*b8=b2*b6-b4^2.
def check_sample(B2, B4, B6):
    B8 = sp.Rational(B2*B6 - B4**2, 4)
    sub = {b2: sp.Rational(B2), b4: sp.Rational(B4), b6: sp.Rational(B6), b8: B8}
    f = sp.expand(prepsi5.subs(sub))
    R = sp.resultant(f, sp.diff(f, X), X)
    D = sp.expand(Delta.subs(sub))
    ok = sp.simplify(R - 5**12 * D**22) == 0
    print("sample", (B2, B4, B6, B8), "Delta=", D, "ok=", ok)
    assert ok

for vals in [(1, 2, 3), (1, -1, 2), (3, 5, 7), (2, -3, 11)]:
    check_sample(*vals)

print("\nRESULTANT CERTIFICATE:")
print("Res_X(prepsi5, dprepsi5/dX) = 5^12 * Delta^22, modulo 4*b8=b2*b6-b4^2")

# Optional / usually too large:
# To try universal Bezout coefficients, uncomment this block.  It is off by default
# because the universal cofactors are not small enough for the <=500-term goal.
#
# K = sp.QQ.frac_field(b2, b4, b6, b8)
# fK = sp.Poly(prepsi5, X, domain=K)
# gK = sp.Poly(dprepsi5, X, domain=K)
# S, T, H = sp.gcdex(fK, gK)
# print("gcdex H =", H)
# print("deg S, deg T =", S.degree(), T.degree())
# print("terms S, T =", len(S.terms()), len(T.terms()))
```

Expected final line:

```text
Res_X(prepsi5, dprepsi5/dX) = 5^12 * Delta^22, modulo 4*b8=b2*b6-b4^2
```
