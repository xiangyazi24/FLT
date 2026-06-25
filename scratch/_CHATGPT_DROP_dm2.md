# Q512 (dm2): CAS factorization of `formalAddX = (t₁-t₂)^3 Q`

## Executive result

With the formal parameter specialization

```text
P(t) = [t, -1, w(t)]
```

the Mathlib projective `addX` formula **does** have the expected cube factor:

```text
Projective.addX(P(t₁), P(t₂)) = (t₁ - t₂)^3 Q(t₁,t₂).
```

This is false for independent `Z`-variables, as in Q498, but becomes true after substituting `Zᵢ = w(tᵢ)`.

All truncations below are by **total degree** in `(t₁,t₂)` after substitution.

---

## 1. Short Weierstrass case

For

```text
y² = x³ + A x + B
```

the projective equation with `P(t)=[t,-1,w(t)]` gives

```text
w = t³ + A t w² + B w³.
```

Solving recursively through degree `12` gives

```text
w(t) = t³ + A t⁷ + B t⁹ + 2 A² t¹¹ + O(t¹³).
```

There is no `t¹²` term.

After substituting

```text
P₁ = [t₁, -1, w(t₁)],
P₂ = [t₂, -1, w(t₂)]
```

into Mathlib's `Projective.addX`, the truncation through total degree `12` factors as

```text
[addX(P₁,P₂)]_{≤12}
  = -(t₁-t₂)³ (t₁+t₂)
      * ( 1
          + A (t₁⁴ + t₁²t₂² + t₂⁴)
          + B (t₁⁶ - 2t₁³t₂³ + t₂⁶)
          + 2A² (t₁⁸ + t₁⁶t₂² + t₁⁴t₂⁴ + t₁²t₂⁶ + t₂⁸) ).
```

Equivalently, the quotient through total degree `9` is

```text
Q_short(t₁,t₂) = [addX/(t₁-t₂)³]_{≤9}
  = -(t₁+t₂)
      * ( 1
          + A (t₁⁴ + t₁²t₂² + t₂⁴)
          + B (t₁⁶ - 2t₁³t₂³ + t₂⁶)
          + 2A² (t₁⁸ + t₁⁶t₂² + t₁⁴t₂⁴ + t₁²t₂⁶ + t₂⁸) ).
```

Expanded lowest-degree terms:

```text
Q_short
  = -(t₁+t₂)
    - A(t₁⁵ + t₁⁴t₂ + t₁³t₂² + t₁²t₂³ + t₁t₂⁴ + t₂⁵)
    - B(t₁⁷ + t₁⁶t₂ - 2t₁⁴t₂³ - 2t₁³t₂⁴ + t₁t₂⁶ + t₂⁷)
    - 2A²(t₁⁹ + t₁⁸t₂ + t₁⁷t₂² + t₁⁶t₂³ + t₁⁵t₂⁴
           + t₁⁴t₂⁵ + t₁³t₂⁶ + t₁²t₂⁷ + t₁t₂⁸ + t₂⁹)
    + O_tot(10).
```

The CAS division by `(t₁-t₂)^3` has remainder `0` through this truncation.

---

## 2. General Weierstrass case

For the general projective Weierstrass equation

```text
Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³
```

with `P(t)=[t,-1,w(t)]`, the formal equation is

```text
w = t³ + a₁ t w + a₂ t² w + a₃ w² + a₄ t w² + a₆ w³.
```

Solving recursively through degree `8` gives

```text
w(t)
  = t³
    + a₁ t⁴
    + (a₁² + a₂) t⁵
    + (a₁³ + 2a₁a₂ + a₃) t⁶
    + (a₁⁴ + 3a₁²a₂ + a₂² + 3a₁a₃ + a₄) t⁷
    + (a₁⁵ + 4a₁³a₂ + 3a₁a₂² + 6a₁²a₃ + 3a₂a₃ + 3a₁a₄) t⁸
    + O(t⁹).
```

Let

```text
D  := t₁ - t₂,
Hₙ := Σ_{i=0}^n t₁^{n-i} t₂^i.
```

Then the truncation of `Projective.addX(P(t₁),P(t₂))` through total degree `8` satisfies

```text
[addX(P(t₁),P(t₂))]_{≤8} = D³ * Q_general,≤5.
```

The quotient through total degree `5` is

```text
Q_general,≤5
  = -H₁
    - a₁ H₂
    - (a₁² + a₂) H₃
    - (a₁³ + 2a₁a₂) H₄
    - a₃ (t₁⁴ + 2t₁³t₂ + 3t₁²t₂² + 2t₁t₂³ + t₂⁴)
    - (a₁⁴ + 3a₁²a₂ + a₂² + a₄) H₅
    - a₁a₃ (3t₁⁵ + 5t₁⁴t₂ + 7t₁³t₂² + 7t₁²t₂³ + 5t₁t₂⁴ + 3t₂⁵)
    + O_tot(6).
```

Expanded by total degree:

```text
Q_general,≤5
  = -(t₁+t₂)
    - a₁(t₁²+t₁t₂+t₂²)
    - (a₁²+a₂)(t₁³+t₁²t₂+t₁t₂²+t₂³)

    - (a₁³+2a₁a₂+a₃)(t₁⁴+t₂⁴)
    - (a₁³+2a₁a₂+2a₃)(t₁³t₂+t₁t₂³)
    - (a₁³+2a₁a₂+3a₃)t₁²t₂²

    - (a₁⁴+3a₁²a₂+3a₁a₃+a₂²+a₄)(t₁⁵+t₂⁵)
    - (a₁⁴+3a₁²a₂+5a₁a₃+a₂²+a₄)(t₁⁴t₂+t₁t₂⁴)
    - (a₁⁴+3a₁²a₂+7a₁a₃+a₂²+a₄)(t₁³t₂²+t₁²t₂³)
    + O_tot(6).
```

Again, the CAS division by `(t₁-t₂)^3` has remainder `0` through this truncation.

---

## Reproduction script

```python
import sympy as sp

t,t1,t2 = sp.symbols('t t1 t2')
a1,a2,a3,a4,a6,A,B = sp.symbols('a1 a2 a3 a4 a6 A B')
D = t1 - t2

def truncate_univar(expr, var, N):
    expr = sp.expand(expr)
    return sp.expand(sum(expr.coeff(var,n)*var**n for n in range(N+1)))

def truncate_total(expr, vars, N):
    poly = sp.Poly(sp.expand(expr), *vars, domain='EX')
    out = 0
    for monom, coeff in poly.terms():
        if sum(monom) <= N:
            term = coeff
            for v,e in zip(vars, monom):
                term *= v**e
            out += term
    return sp.expand(out)

def series_w(N, coeffs):
    A1,A2,A3,A4,A6 = coeffs
    cs = {n: sp.Symbol(f'c{n}') for n in range(3,N+1)}
    w = sum(cs[n]*t**n for n in range(3,N+1))
    rhs = t**3 + A1*t*w + A2*t**2*w + A3*w**2 + A4*t*w**2 + A6*w**3
    eq = sp.expand(w-rhs)
    subd = {}
    for n in range(3,N+1):
        coeff_n = sp.expand(eq.subs(subd)).coeff(t,n)
        subd[cs[n]] = sp.solve(sp.Eq(coeff_n,0), cs[n])[0]
    return truncate_univar(w.subs(subd), t, N)

def addX(Px,Py,Pz,Qx,Qy,Qz, coeffs):
    A1,A2,A3,A4,A6 = coeffs
    return sp.expand(
      -Px*Qy**2*Pz + Qx*Py**2*Qz - 2*Px*Py*Qy*Qz + 2*Qx*Py*Qy*Pz
      - A1*Px**2*Qy*Qz + A1*Qx**2*Py*Pz + A2*Px**2*Qx*Qz
      - A2*Px*Qx**2*Pz - A3*Px*Py*Qz**2 + A3*Qx*Qy*Pz**2
      - 2*A3*Px*Qy*Pz*Qz + 2*A3*Qx*Py*Pz*Qz
      + A4*Px**2*Qz**2 - A4*Qx**2*Pz**2 + 3*A6*Px*Pz*Qz**2
      - 3*A6*Qx*Pz**2*Qz)

# Short case
w_short = series_w(12, (0,0,0,A,B))
addX_short = addX(t1,-1,w_short.subs(t,t1), t2,-1,w_short.subs(t,t2), (0,0,0,A,B))
addX_short_tr = truncate_total(addX_short, (t1,t2), 12)
q_short, r_short = sp.div(sp.Poly(addX_short_tr, t1, domain='EX'), sp.Poly(D**3, t1, domain='EX'))
print('w_short =', w_short)
print('short remainder =', sp.expand(r_short.as_expr()))
print('Q_short =', sp.factor(q_short.as_expr()))

# General case
w_gen = series_w(8, (a1,a2,a3,a4,a6))
addX_gen = addX(t1,-1,w_gen.subs(t,t1), t2,-1,w_gen.subs(t,t2), (a1,a2,a3,a4,a6))
addX_gen_tr = truncate_total(addX_gen, (t1,t2), 8)
q_gen, r_gen = sp.div(sp.Poly(addX_gen_tr, t1, domain='EX'), sp.Poly(D**3, t1, domain='EX'))
print('w_gen =', w_gen)
print('general remainder =', sp.expand(r_gen.as_expr()))
print('Q_general_to_degree5 =', truncate_total(q_gen.as_expr(), (t1,t2), 5))
```

---

## Lean implication

The right Lean theorem is not the independent-`Z` pure polynomial statement from Q498.  The right certificate is the specialized one:

```lean
formalAddX W = (X₀ - X₁)^3 * formalAddXQuot W
```

where `formalAddX` has already substituted

```lean
P i = ![X i, -1, formalW_i]
```

and `formalW_i` is the one-variable formal solution evaluated at coordinate `i`.

For the general Weierstrass case, the quotient begins exactly as `Q_general,≤5` above.  That quotient data is a useful target for debugging a Lean `ring`/certificate proof: if the implementation's first quotient terms disagree with the displayed terms, the mismatch is in the formal `w(t)` normalization or in the sign convention for `P(t)=[t,-1,w(t)]`.
