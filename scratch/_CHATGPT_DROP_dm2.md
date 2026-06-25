# Q282 (dm2): CAS investigation — is the `addX` identity an EDS-formal consequence?

Question: for the short Weierstrass curve

```text
Y² = X³ + A X + B,
```

treat the values

```text
ψ_{m-2}, ψ_{m-1}, ψ_m, ψ_{m+1}, ψ_{m+2}
```

as formal symbols satisfying the relevant local EDS relation, together with the curve equation and the definitions of `φ_m` and `ω_m`.  Does

```text
addX([X,Y,1], [φ_m,ω_m,ψ_m]) - ψ_{m-1}² φ_{m+1}
```

reduce to zero formally?

## Result

**No, not from the local EDS product recurrence alone.**

After substituting the formal definitions of `φ_m`, `φ_{m+1}`, and `ω_m`, and reducing by the curve equation plus the relevant EDS recurrence

```text
ψ_{m+2} ψ_{m-2} = ψ_{m+1} ψ_{m-1} ψ_2² - ψ_3 ψ_m²,
```

the target does **not** reduce to zero.

The residual is

```text
ψ_m/2 * I_m
```

where the missing extra identity is

```text
I_m = ψ_{m+2} ψ_{m-1}² + ψ_{m-2} ψ_{m+1}²
      - 2(3X² + A) ψ_m ψ_{m-1} ψ_{m+1}
      + 4Y² ψ_m³.
```

This identity `I_m = 0` is true for the actual short-Weierstrass division polynomials; the script verifies it for `m=2,3,4`.  But it is **not** a consequence of the local EDS product recurrence tested by the Groebner reduction.  It is an additional x-coordinate/addition identity, essentially the missing formal content behind the `addX` theorem.

So the induction step is not clean if the only inductive algebra available is the EDS recurrence.  You need to carry/prove this extra identity, or prove the coordinate-ring `addX` identity directly.

## Complete runnable SymPy script

```python
import sympy as sp

# Curve variables and coefficients.
X, Y, A, B = sp.symbols('X Y A B')
S = X**3 + A*X + B
FW = Y**2 - S

# Formal local EDS symbols around m.
pm2, pm1, pm, pp1, pp2, om = sp.symbols(
    'psi_m_minus_2 psi_m_minus_1 psi_m psi_m_plus_1 psi_m_plus_2 omega_m'
)

psi2 = 2*Y
psi3 = 3*X**4 + 6*A*X**2 + 12*B*X - A**2

# Formal definitions.
phi_m = X*pm**2 - pp1*pm1
phi_mp1 = X*pp1**2 - pp2*pm

# Mathlib short-Weierstrass Jacobian.addX for P=[X,Y,1], Q=[phi_m, omega_m, psi_m].
addX = sp.expand(
    X*phi_m**2
    - 2*Y*om*pm
    + X**2*phi_m*pm**2
    + A*phi_m*pm**2
    + A*X*pm**4
    + 2*B*pm**4
)

target = sp.expand(addX - pm1**2 * phi_mp1)

# Relations allowed in the formal test.
curve_rel = FW
omega_rel = sp.expand(4*Y*om - (pp2*pm1**2 - pm2*pp1**2))
eds_n2_rel = sp.expand(pp2*pm2 - (pp1*pm1*psi2**2 - psi3*pm**2))

vars_order = [om, pp2, pm2, pp1, pm1, pm, Y, X, A, B]
G = sp.groebner([curve_rel, omega_rel, eds_n2_rel], *vars_order, order='lex', domain=sp.QQ)
formal_remainder = sp.factor(G.reduce(target)[1])

print('formal_reduction_zero =', formal_remainder == 0)
print('formal_remainder =')
print(formal_remainder)
print()

# A concrete counterexample satisfying the allowed relations but not the target.
# A=0,B=1 gives nonsingular curve Y^2=X^3+1; (X,Y)=(0,1) lies on it.
# At X=0, psi3=0, so the EDS n=2 relation becomes pp2*pm2 = 4Y^2*pp1*pm1.
subs_counterexample = {
    A: 0,
    B: 1,
    X: 0,
    Y: 1,
    pm: 1,
    pm1: 1,
    pp1: 1,
    pm2: 1,
    pp2: 4,
    om: sp.Rational(3, 4),
}
print('counterexample_curve_rel =', sp.expand(curve_rel.subs(subs_counterexample)))
print('counterexample_omega_rel =', sp.expand(omega_rel.subs(subs_counterexample)))
print('counterexample_eds_n2_rel =', sp.expand(eds_n2_rel.subs(subs_counterexample)))
print('counterexample_target =', sp.expand(target.subs(subs_counterexample)))
print()

# The missing identity exposed by the formal reduction.
I_m = sp.expand(
    pp2*pm1**2 + pm2*pp1**2
    - 2*(3*X**2 + A)*pm*pm1*pp1
    + psi2**2 * pm**3
)
print('missing_identity_I_m =')
print(I_m)
print()

G_with_I = sp.groebner([curve_rel, omega_rel, I_m], *vars_order, order='lex', domain=sp.QQ)
print('target_reduces_zero_with_I_m =', G_with_I.reduce(target)[1] == 0)

# Verify that I_m holds for actual short-Weierstrass division polynomials in small cases.
def rem_curve(poly):
    return sp.expand(sp.rem(sp.Poly(sp.expand(poly), Y), sp.Poly(FW, Y)).as_expr())


def exact_div(num, den):
    q, r = sp.div(sp.expand(num), sp.expand(den), Y, X, A, B, domain=sp.QQ)
    assert sp.expand(r) == 0
    return sp.expand(q)

psi = {
    0: sp.Integer(0),
    1: sp.Integer(1),
    2: 2*Y,
    3: psi3,
}
pre4 = (
    X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2
    - 4*A*B*X - 8*B**2 - A**3
)
psi[4] = 4*Y*pre4

for n in range(5, 8):
    if n % 2:
        r = (n - 1) // 2
        psi[n] = rem_curve(psi[r+2]*psi[r]**3 - psi[r-1]*psi[r+1]**3)
    else:
        r = n // 2
        psi[n] = rem_curve(exact_div(
            psi[r]*(psi[r+2]*psi[r-1]**2 - psi[r-2]*psi[r+1]**2),
            2*Y,
        ))

for m in [2, 3, 4]:
    Im_actual = sp.expand(
        psi[m+2]*psi[m-1]**2 + psi[m-2]*psi[m+1]**2
        - 2*(3*X**2 + A)*psi[m]*psi[m-1]*psi[m+1]
        + (2*Y)**2 * psi[m]**3
    )
    print(f'I_m actual m={m} reduces to zero =', rem_curve(Im_actual) == 0)
```

## Output

```text
formal_reduction_zero = False
formal_remainder =
psi_m*(4*A*X*psi_m**3 - 2*A*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*B*psi_m**3 + 4*X**3*psi_m**3 - 6*X**2*psi_m*psi_m_minus_1*psi_m_plus_1 + psi_m_minus_1**2*psi_m_plus_2 + psi_m_minus_2*psi_m_plus_1**2)/2

counterexample_curve_rel = 0
counterexample_omega_rel = 0
counterexample_eds_n2_rel = 0
counterexample_target = 9/2

missing_identity_I_m =
-2*A*psi_m*psi_m_minus_1*psi_m_plus_1 + 4*Y**2*psi_m**3 - 6*X**2*psi_m*psi_m_minus_1*psi_m_plus_1 + psi_m_minus_1**2*psi_m_plus_2 + psi_m_minus_2*psi_m_plus_1**2

target_reduces_zero_with_I_m = True
I_m actual m=2 reduces to zero = True
I_m actual m=3 reduces to zero = True
I_m actual m=4 reduces to zero = True
```

## Interpretation

The `addX` identity is not just a formal consequence of the EDS product recurrence plus the curve equation and the `φ/ω` definitions.

The local EDS recurrence gives the product relation

```text
ψ_{m+2}ψ_{m-2} = 4Y² ψ_{m+1}ψ_{m-1} - ψ₃ ψ_m².
```

But the `addX` computation needs the symmetric linear relation

```text
ψ_{m+2}ψ_{m-1}² + ψ_{m-2}ψ_{m+1}²
  = 2(3X² + A)ψ_mψ_{m-1}ψ_{m+1} - 4Y²ψ_m³.
```

This relation is true for actual division polynomials, but it is extra structure beyond the product recurrence.  It is best treated as a separate coordinate/addition identity, or proved directly in the coordinate ring with a CAS cofactor certificate.
