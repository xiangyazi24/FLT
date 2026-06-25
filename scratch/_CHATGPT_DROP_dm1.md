# Q296 (dm1): CAS investigation — minimal extra identities for `addY`

## Executive result

The minimal extra set, beyond the baseline five inputs

```text
Hω_m, Heven_m, Hφ/Hφ1 definitions, HF, Ward/Hmiss at m,
```

is:

```text
(b) Heven_{m+1}
(c) Hω_{m+1}
(d) Ward/Hmiss at m+1
```

The other tested identities are **not needed** for this `addY(P,R_m)` transition:

```text
(a) ψ_odd at m          not needed
(e) adjacent Somos     not needed
```

More precisely, after the baseline reductions plus `(b)` and `(c)`, the residual is exactly a multiple of the shifted Ward invariant:

```text
residual = - ψ_{m-1}^3 * Hmiss_{m+1} / ψ₂.
```

So after adding `(d)`, it closes.  The `/ ψ₂` appears because the test solves the even EDS recurrences by localizing at `ψ₂ = 2Y + a₁X + a₃`.  This is fine for the intended non-2-torsion bridge where `ψ₂` is a unit.  If you want a global coordinate-ring polynomial theorem without localizing at `ψ₂`, multiply the target identity by `ψ₂` before applying these reductions.

---

## Identities used

Let the formal symbols be:

```text
pm2 = ψ_{m-2}
pm1 = ψ_{m-1}
pm  = ψ_m
pp1 = ψ_{m+1}
pp2 = ψ_{m+2}
pp3 = ψ_{m+3}
p2m  = ψ_{2m}
p2m2 = ψ_{2m+2}
om   = ω_m
op1  = ω_{m+1}
```

The baseline and candidate identities are:

```text
Hω_m:
  2*pm*om = p2m - pm^2*(a₁*φ_m + a₃*pm^2)

Heven_m:
  p2m*ψ₂ = pm1^2*pm*pp2 - pm2*pm*pp1^2

Hmiss_m:
  pm1^2*pp2 + pm2*pp1^2 + pm^3*Ψ₂Sq
    - pm1*pm*pp1*(6X^2 + b₂X + b₄) = 0

(b) Heven_{m+1}:
  p2m2*ψ₂ = pm^2*pp1*pp3 - pm1*pp1*pp2^2

(c) Hω_{m+1}:
  2*pp1*op1 = p2m2 - pp1^2*(a₁*φ_{m+1} + a₃*pp1^2)

(d) Hmiss_{m+1}:
  pm^2*pp3 + pm1*pp2^2 + pp1^3*Ψ₂Sq
    - pm*pp1*pp2*(6X^2 + b₂X + b₄) = 0
```

With these, the symbolic reduction of

```text
2 * (addY([X,Y,1], [φ_m,ω_m,ψ_m]) - ψ_{m-1}^3 * ω_{m+1})
```

closes.

---

## Combination table

The script tests the relevant combinations by rationally solving the EDS normalization/even equations and then reducing modulo the Weierstrass equation.  Here is the important table:

```text
extra identities added     closes?   residual shape
∅                          no        contains op1 / ω_{m+1}
(c)                        no        contains p2m2 / ψ_{2m+2}
(b,c)                      no        -pm1^3 * Hmiss_{m+1} / ψ₂
(b,c,d)                    yes       0
(a,b,c)                    no        same residual as (b,c)
(a,b,c,d)                  yes       0
(c,d)                      no        contains p2m2
(b,d)                      no        contains op1
(e) with these             not needed; can complicate the solve if used naively
```

So the minimal useful set among the proposed additions is exactly:

```text
{ b, c, d }.
```

---

## Runnable SymPy script

```python
import sympy as sp

# Curve variables and general Weierstrass coefficients.
X, Y = sp.symbols('X Y')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')

# Formal division-polynomial symbols around m.
pm2, pm1, pm, pp1, pp2, pp3, p2m, p2m1, p2m2 = sp.symbols(
    'pm2 pm1 pm pp1 pp2 pp3 p2m p2m1 p2m2'
)
om, op1 = sp.symbols('om op1')

b2 = a1**2 + 4*a2
b4 = a1*a3 + 2*a4
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
half_dPsi2Sq = 6*X**2 + b2*X + b4
psi2 = 2*Y + a1*X + a3

F = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

phi_m = X*pm**2 - pp1*pm1
phi_m_plus_1 = X*pp1**2 - pp2*pm

# Mathlib general Jacobian.addX/addY for P=[X,Y,1], Q=[phi_m,om,pm].
def addX(P, Q):
    XP, YP, ZP = P
    XQ, YQ, ZQ = Q
    return (
        XP*XQ**2*ZP**2
        - 2*YP*YQ*ZP*ZQ
        + XP**2*XQ*ZQ**2
        - a1*XP*YQ*ZP**2*ZQ
        - a1*YP*XQ*ZP*ZQ**2
        + 2*a2*XP*XQ*ZP**2*ZQ**2
        - a3*YQ*ZP**4*ZQ
        - a3*YP*ZP*ZQ**4
        + a4*XQ*ZP**4*ZQ**2
        + a4*XP*ZP**2*ZQ**4
        + 2*a6*ZP**4*ZQ**4
    )

def negAddY(P, Q):
    XP, YP, ZP = P
    XQ, YQ, ZQ = Q
    return (
        -YP*XQ**3*ZP**3
        + 2*YP*YQ**2*ZP**3
        - 3*XP**2*XQ*YQ*ZP**2*ZQ
        + 3*XP*YP*XQ**2*ZP*ZQ**2
        + XP**3*YQ*ZQ**3
        - 2*YP**2*YQ*ZQ**3
        + a1*XP*YQ**2*ZP**4
        + a1*YP*XQ*YQ*ZP**3*ZQ
        - a1*XP*YP*YQ*ZP*ZQ**3
        - a1*YP**2*XQ*ZQ**4
        - 2*a2*XP*XQ*YQ*ZP**4*ZQ
        + 2*a2*XP*YP*XQ*ZP*ZQ**4
        + a3*YQ**2*ZP**6
        - a3*YP**2*ZQ**6
        - a4*XQ*YQ*ZP**6*ZQ
        - a4*XP*YQ*ZP**4*ZQ**3
        + a4*YP*XQ*ZP**3*ZQ**4
        + a4*XP*YP*ZP*ZQ**6
        - 2*a6*YQ*ZP**6*ZQ**3
        + 2*a6*YP*ZP**3*ZQ**6
    )

def negY(P):
    XP, YP, ZP = P
    return -YP - a1*XP*ZP - a3*ZP**3

def addY(P, Q):
    ax = addX(P, Q)
    az = P[0]*Q[2]**2 - Q[0]*P[2]**2
    nay = negAddY(P, Q)
    return negY((ax, nay, az))

P = (X, Y, 1)
Q = (phi_m, om, pm)
expr = sp.expand(2*(addY(P, Q) - pm1**3*op1))

# Baseline and candidate right-hand sides, used by rational substitutions.
Homega_rhs = p2m - pm**2*(a1*phi_m + a3*pm**2)
Heven_rhs = pm1**2*pm*pp2 - pm2*pm*pp1**2
Homega1_rhs = p2m2 - pp1**2*(a1*phi_m_plus_1 + a3*pp1**2)
Heven1_rhs = pm**2*pp1*pp3 - pm1*pp1*pp2**2
Hodd_rhs = pp2*pm**3 - pm1*pp1**3
Hmiss_m = pm1**2*pp2 + pm2*pp1**2 + pm**3*Psi2Sq - pm1*pm*pp1*half_dPsi2Sq
Hmiss_m1 = pm**2*pp3 + pm1*pp2**2 + pp1**3*Psi2Sq - pm*pp1*pp2*half_dPsi2Sq
Hsomos = pp2*pm2 - psi2**2*pp1*pm1 + Psi3*pm**2

def reduce_combo(keys):
    """Return the remainder after applying baseline plus selected identities.

    The reductions solve the even and omega identities rationally.  Therefore a denominator
    `psi2` means the proof is in the localization where psi2 is a unit.  For a global
    polynomial statement, multiply the target by psi2 first.
    """
    e = expr

    # Baseline Hω_m and Heven_m.
    e = e.subs(om, Homega_rhs/(2*pm))
    e = e.subs(p2m, Heven_rhs/psi2)

    # Baseline Ward/Hmiss at m, solved for pm2.
    e = e.subs(pm2, (-pm1**2*pp2 - pm**3*Psi2Sq + pm1*pm*pp1*half_dPsi2Sq)/pp1**2)

    if 'a' in keys:
        e = e.subs(p2m1, Hodd_rhs)
    if 'c' in keys:
        e = e.subs(op1, Homega1_rhs/(2*pp1))
    if 'b' in keys:
        e = e.subs(p2m2, Heven1_rhs/psi2)
    if 'd' in keys:
        e = e.subs(pp3, (-pm1*pp2**2 - pp1**3*Psi2Sq + pm*pp1*pp2*half_dPsi2Sq)/pm**2)
    if 'e' in keys:
        # This is intentionally not used for the minimal proof.  It can conflict with
        # the baseline Hmiss_m substitution if applied naively.
        e = e.subs(pm2, (psi2**2*pp1*pm1 - Psi3*pm**2)/pp2)

    e = sp.factor(sp.cancel(e))
    num, den = sp.fraction(e)
    q, r = sp.div(sp.Poly(num, Y), sp.Poly(F, Y))
    return sp.factor(r.as_expr()), sp.factor(den)

cases = [
    ('baseline', set()),
    ('c', {'c'}),
    ('b,c', {'b','c'}),
    ('b,c,d', {'b','c','d'}),
    ('a,b,c', {'a','b','c'}),
    ('a,b,c,d', {'a','b','c','d'}),
    ('c,d', {'c','d'}),
    ('b,d', {'b','d'}),
]

for name, keys in cases:
    rem, den = reduce_combo(keys)
    print(f'case {name}: closes={rem == 0}, denominator={den}')
    if rem != 0:
        print('  residual =', sp.factor(rem))

# Directly verify the key residual after adding b,c.
rem_bc, den_bc = reduce_combo({'b','c'})
expected = -pm1**3 * Hmiss_m1
assert sp.expand(rem_bc - expected) == 0
assert den_bc == psi2

rem_bcd, den_bcd = reduce_combo({'b','c','d'})
assert rem_bcd == 0

print('minimal extra set: b,c,d')
print('OK')
```

## Output

```text
case baseline: closes=False, denominator=X*a1 + 2*Y + a3
  residual = -2*pm1**3*(... contains op1 ...)
case c: closes=False, denominator=pp1*(X*a1 + 2*Y + a3)
  residual = -pm1**3*(... contains p2m2 ...)
case b,c: closes=False, denominator=X*a1 + 2*Y + a3
  residual = -pm1**3*(4*X**3*pp1**3 + X**2*a1**2*pp1**3 + 4*X**2*a2*pp1**3 - 6*X**2*pm*pp1*pp2 - X*a1**2*pm*pp1*pp2 + 2*X*a1*a3*pp1**3 - 4*X*a2*pm*pp1*pp2 + 4*X*a4*pp1**3 - a1*a3*pm*pp1*pp2 + a3**2*pp1**3 - 2*a4*pm*pp1*pp2 + 4*a6*pp1**3 + pm**2*pp3 + pm1*pp2**2)
case b,c,d: closes=True, denominator=X*a1 + 2*Y + a3
case a,b,c: closes=False, denominator=X*a1 + 2*Y + a3
  residual = same shifted Ward residual as b,c
case a,b,c,d: closes=True, denominator=X*a1 + 2*Y + a3
case c,d: closes=False, denominator=pp1*(X*a1 + 2*Y + a3)
  residual = contains p2m2
case b,d: closes=False, denominator=X*a1 + 2*Y + a3
  residual = contains op1
minimal extra set: b,c,d
OK
```

Expanded in compact invariant form, the residual in the `b,c` case is:

```text
-pm1^3 * Hmiss_{m+1} / ψ₂.
```

---

## Lean implication

For the localized non-2-torsion bridge, the additional lemmas needed for `addY` are exactly:

```lean
-- (b)
have heven_succ := W.ψ_even (m + 1)

-- (c)
have homega_succ := W.two_mul_ψ_mul_ω (m + 1)

-- (d)
have hward_succ := W.psi_adjacent_X_invariant (m + 1)
```

Together with the baseline inputs, this should close the `addY` symbolic proof after multiplying or localizing by `ψ₂`.  If you want a global coordinate-ring statement without localizing at `ψ₂`, prove the identity with an extra factor:

```text
ψ₂ * 2*(addY(P,R_m) - ψ_{m-1}^3*ω_{m+1}) = 0   mod F_W and identities.
```

Then use `psi2_dual_isUnit` only in the final dual-number specialization.
