# Q354 (dm1): `addY` 8-input linear-combination coefficients — obstruction

## Executive result

The requested polynomial coefficients

```text
2*(addY(P,R_m) - ψ_{m-1}^3*ω_{m+1})
  = d₁*Hω_m + d₂*Heven_m + d₃*Hmiss_m + d₄*Hφ_m + d₅*HF
    + d₆*Heven_{m+1} + d₇*Hω_{m+1} + d₈*Hmiss_{m+1}
```

**do not exist in the raw polynomial ring** with only those eight residual identities.

This is not a CAS timeout; it is a structural obstruction.

Two coefficient-obstructions are immediate:

1. `addY(P,R_m)` contains an `ω_m^2` term.  The coefficient of `ω_m^2` in the left-hand side is
   ```text
   -2*ψ₂ = -2*(2Y + a₁X + a₃).
   ```
   The only input identity containing `ω_m` is
   ```text
   Hω_m = 2*ψ_m*ω_m - (...).
   ```
   Therefore any polynomial linear combination would need the coefficient of `ω_m` in `d₁` to be
   ```text
   -ψ₂ / ψ_m,
   ```
   which is not a polynomial.

2. The left-hand side contains `ω_{m+1}` with coefficient
   ```text
   -2*ψ_{m-1}^3.
   ```
   The only input identity containing `ω_{m+1}` is
   ```text
   Hω_{m+1} = 2*ψ_{m+1}*ω_{m+1} - (...).
   ```
   Therefore
   ```text
   d₇ = -ψ_{m-1}^3 / ψ_{m+1}
   ```
   in any coefficient list using only `Hω_{m+1}` to eliminate `ω_{m+1}`.  Again, this is not a polynomial.

So the 8-input `linear_combination` requested here can exist only after localizing/dividing by division-polynomial factors, or after replacing the inputs by stronger identities that determine `ω_m` and `ω_{m+1}` directly.

This also corrects the interpretation of Q296: the CAS reduction there was a **localized** reduction. It used divisions by `ψ_m`, `ψ_{m+1}`, and `ψ₂`; it was not a raw polynomial-ring linear combination.

---

## What happens in the localized calculation?

If one unfolds

```text
φ_m = X*ψ_m^2 - ψ_{m+1}*ψ_{m-1}
```

and performs the same reductions as in Q296, one possible localized reduction gives:

```text
d₇ = -ψ_{m-1}^3 / ψ_{m+1}
d₆ = -ψ_{m-1}^3 / (ψ_{m+1}*ψ₂)
d₈ = -ψ_{m-1}^3 / ψ₂
```

and after all eight residual identities are used, the remaining curve-equation term is

```text
(4*ψ_{m-1}^2*(ψ_m^3*ψ_{m+2} - ψ_{m-1}*ψ_{m+1}^3) / ψ₂) * HF.
```

Thus, with the `Ψ₂Sq` version of `Hmiss`, `d₅` is **not** zero in this localized proof.  It is

```text
d₅ = 4*ψ_{m-1}^2*(ψ_m^3*ψ_{m+2} - ψ_{m-1}*ψ_{m+1}^3) / ψ₂.
```

This is compatible with Q296’s observation that the final residual is zero only after reducing modulo `HF` while working in the localization at `ψ₂`.

---

## Why this matters for Lean

A Lean proof by

```lean
linear_combination
  d₁*hω_m + d₂*heven_m + d₃*hmiss_m + d₄*hφ_m + d₅*hF
    + d₆*heven_succ + d₇*hω_succ + d₈*hmiss_succ
```

with polynomial `dᵢ : K[X][Y]` cannot close the raw `addY` theorem.  The obstruction is visible just by comparing the `ω_m^2` and `ω_{m+1}` coefficients.

To get a polynomial proof, you need at least one of the following changes:

### Option A: use the actual definition of `ω`, not only its normalization

For the characteristic-zero prototype, if

```lean
ω_m := (ψTwoMulQuot_m - ψ_m*(a₁φ_m+a₃ψ_m²)) / 2
```

is unfolded directly, then `ω_m` is no longer an independent symbol and the `ω_m^2` obstruction disappears.  This is likely the cleanest route for the `addY` component.

### Option B: add the projective representative equation for `R_m`

The Jacobian/projective equation for

```text
R_m = [φ_m : ω_m : ψ_m]
```

contains `ω_m^2`:

```text
ω_m^2 + a₁*φ_m*ω_m*ψ_m + a₃*ω_m*ψ_m^3
  = φ_m^3 + a₂*φ_m^2*ψ_m^2 + a₄*φ_m*ψ_m^4 + a₆*ψ_m^6.
```

This can eliminate the `ω_m^2` term without dividing by `ψ_m`.  This is the natural missing identity if you want a raw polynomial-ring proof of `addY` using symbolic `ω_m`.

### Option C: prove only a localized/multiplied theorem

You can prove a localized identity after inverting `ψ₂`, `ψ_m`, and `ψ_{m+1}`.  This is **not** suitable at an `n`-torsion root where `ψ_m = 0`.  Multiplying by `ψ_m` would erase the first-order information you need.  Inverting `ψ₂` and `ψ_{m+1}` is acceptable in the non-2-torsion/no-adjacent context, but inverting `ψ_m` is not.

So for the bridge proof, Option C is risky unless the multiplication/inversion factors are carefully restricted to known units.

---

## Runnable SymPy obstruction script

The script below verifies the obstruction and prints the localized coefficients that appear in the Q296-style reduction.

```python
import sympy as sp

X, Y = sp.symbols('X Y')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')
pm2, pm1, pm, pp1, pp2, pp3, p2m, p2m2 = sp.symbols('pm2 pm1 pm pp1 pp2 pp3 p2m p2m2')
om, op1, ph = sp.symbols('om op1 ph')

b2 = a1**2 + 4*a2
b4 = a1*a3 + 2*a4
b6 = a3**2 + 4*a6
Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
halfd = 6*X**2 + b2*X + b4
psi2 = 2*Y + a1*X + a3
F = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

phi1 = X*pp1**2 - pp2*pm

P = (X, Y, 1)
Q = (ph, om, pm)

def addX(P,Q):
    XP,YP,ZP=P; XQ,YQ,ZQ=Q
    return (XP*XQ**2*ZP**2 - 2*YP*YQ*ZP*ZQ + XP**2*XQ*ZQ**2
            - a1*XP*YQ*ZP**2*ZQ - a1*YP*XQ*ZP*ZQ**2
            + 2*a2*XP*XQ*ZP**2*ZQ**2
            - a3*YQ*ZP**4*ZQ - a3*YP*ZP*ZQ**4
            + a4*XQ*ZP**4*ZQ**2 + a4*XP*ZP**2*ZQ**4 + 2*a6*ZP**4*ZQ**4)

def negAddY(P,Q):
    XP,YP,ZP=P; XQ,YQ,ZQ=Q
    return (-YP*XQ**3*ZP**3 + 2*YP*YQ**2*ZP**3 - 3*XP**2*XQ*YQ*ZP**2*ZQ
            + 3*XP*YP*XQ**2*ZP*ZQ**2 + XP**3*YQ*ZQ**3 - 2*YP**2*YQ*ZQ**3
            + a1*XP*YQ**2*ZP**4 + a1*YP*XQ*YQ*ZP**3*ZQ
            - a1*XP*YP*YQ*ZP*ZQ**3 - a1*YP**2*XQ*ZQ**4
            - 2*a2*XP*XQ*YQ*ZP**4*ZQ + 2*a2*XP*YP*XQ*ZP*ZQ**4
            + a3*YQ**2*ZP**6 - a3*YP**2*ZQ**6
            - a4*XQ*YQ*ZP**6*ZQ - a4*XP*YQ*ZP**4*ZQ**3
            + a4*YP*XQ*ZP**3*ZQ**4 + a4*XP*YP*ZP*ZQ**6
            - 2*a6*YQ*ZP**6*ZQ**3 + 2*a6*YP*ZP**3*ZQ**6)

def negY(P):
    XP,YP,ZP=P
    return -YP - a1*XP*ZP - a3*ZP**3

def addY(P,Q):
    ax = addX(P,Q)
    az = P[0]*Q[2]**2 - Q[0]*P[2]**2
    nay = negAddY(P,Q)
    return negY((ax,nay,az))

LHS = sp.expand(2*(addY(P,Q) - pm1**3*op1))

print('coefficient of omega_m^2 in LHS =', sp.factor(sp.Poly(LHS, om).coeff_monomial(om**2)))
print('coefficient of omega_m in Homega_m =', 2*pm)
print('therefore coeff_omega(d1) would have to be', sp.factor(-psi2/pm))
print()
print('coefficient of omega_{m+1} in LHS =', sp.factor(sp.Poly(LHS, op1).coeff_monomial(op1)))
print('coefficient of omega_{m+1} in Homega_{m+1} =', 2*pp1)
print('therefore d7 would have to be', sp.factor(-pm1**3/pp1))

# Now reproduce the localized Q296-style reduction after unfolding phi_m.
Hphi = ph - (X*pm**2 - pp1*pm1)
Homega = 2*pm*om - (p2m - pm**2*(a1*ph + a3*pm**2))
Heven = p2m*psi2 - (pm1**2*pm*pp2 - pm2*pm*pp1**2)
Hmiss = pm1**2*pp2 + pm2*pp1**2 + pm**3*Psi2Sq - pm1*pm*pp1*halfd
Homega1 = 2*pp1*op1 - (p2m2 - pp1**2*(a1*phi1 + a3*pp1**2))
Heven1 = p2m2*psi2 - (pm**2*pp1*pp3 - pm1*pp1*pp2**2)
Hmiss1 = pm**2*pp3 + pm1*pp2**2 + pp1**3*Psi2Sq - pm*pp1*pp2*halfd

E = sp.expand(LHS.subs(ph, X*pm**2 - pp1*pm1))
E = E.subs(om, (p2m - pm**2*(a1*(X*pm**2-pp1*pm1)+a3*pm**2))/(2*pm))
E = E.subs(p2m, (pm1**2*pm*pp2 - pm2*pm*pp1**2)/psi2)
E = E.subs(pm2, (-pm1**2*pp2 - pm**3*Psi2Sq + pm1*pm*pp1*halfd)/pp1**2)
E = E.subs(op1, (p2m2 - pp1**2*(a1*phi1+a3*pp1**2))/(2*pp1))
E = E.subs(p2m2, (pm**2*pp1*pp3 - pm1*pp1*pp2**2)/psi2)
E = E.subs(pp3, (-pm1*pp2**2 - pp1**3*Psi2Sq + pm*pp1*pp2*halfd)/pm**2)
E = sp.factor(sp.cancel(E))
num, den = sp.fraction(E)
q, r = sp.div(sp.Poly(num, Y), sp.Poly(F, Y))
assert r.as_expr() == 0

print()
print('localized residual after all eight identities =')
print(E)
print('denominator =', sp.factor(den))
print('HF coefficient in this localized proof =', sp.factor(q.as_expr()/den))
print('OK')
```

## Output

```text
coefficient of omega_m^2 in LHS = -2*(X*a1 + 2*Y + a3)
coefficient of omega_m in Homega_m = 2*pm
therefore coeff_omega(d1) would have to be -(X*a1 + 2*Y + a3)/pm

coefficient of omega_{m+1} in LHS = -2*pm1**3
coefficient of omega_{m+1} in Homega_{m+1} = 2*pp1
therefore d7 would have to be -pm1**3/pp1

localized residual after all eight identities =
4*pm1**2*(pm**3*pp2 - pm1*pp1**3)*(-X**3 - X**2*a2 + X*Y*a1 - X*a4 + Y**2 + Y*a3 - a6)/(X*a1 + 2*Y + a3)
denominator = X*a1 + 2*Y + a3
HF coefficient in this localized proof = 4*pm1**2*(pm**3*pp2 - pm1*pp1**3)/(X*a1 + 2*Y + a3)
OK
```

## Lean implication

Do not spend time trying to make an 8-input polynomial `linear_combination` for raw `addY`; it cannot exist with only those inputs.

For the Lean proof of `addY`, the minimal fix is one of:

1. **Unfold the definition of `ω_m` and `ω_{m+1}`** from `ψTwoMulQuot` / complement sequences, instead of using only the normalization identities.
2. **Add the projective equation for `R_m=[φ_m:ω_m:ψ_m]`**, which contains `ω_m^2` and can eliminate the quadratic `ω_m` term without dividing by `ψ_m`.
3. Work in a localized theorem that explicitly inverts the required factors, but this is dangerous for the torsion-root bridge because `ψ_m=0` at the root.

The most robust general projective-formula path is therefore:

```text
addX: normalization + Heven + Hmiss is enough.
addY: also needs either the actual ω definition or the projective representative equation; normalization alone is insufficient.
```
