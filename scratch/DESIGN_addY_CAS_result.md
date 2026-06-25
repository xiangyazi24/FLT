# Q289 (dm2): CAS test of the formal `addY` reduction for general `m`

Question: after substituting the formal relations

```text
HF      : F_W = 0
Hφ_m    : φ_m     = X ψ_m² - ψ_{m+1} ψ_{m-1}
Hφ_m+1  : φ_{m+1} = X ψ_{m+1}² - ψ_{m+2} ψ_m
Hω_m    : 2 ψ_m ω_m = ψ_{2m} - ψ_m²(a₁φ_m+a₃ψ_m²)
Heven_m : ψ₂ ψ_{2m} = ψ_m(ψ_{m+2}ψ_{m-1}² - ψ_{m-2}ψ_{m+1}²)
Hω_m+1  : 2 ψ_{m+1}ω_{m+1} = ψ_{2m+2} - ψ_{m+1}²(a₁φ_{m+1}+a₃ψ_{m+1}²)
Heven_m+1 : ψ₂ ψ_{2m+2} = ψ_{m+1}(ψ_{m+3}ψ_m² - ψ_{m-1}ψ_{m+2}²)
```

does

```text
2 · (addY(P,R_m) - ψ_{m-1}³ω_{m+1})
```

reduce to zero?

## Result

The CAS answer is **NO** for the stated relation set.

Even if I additionally substitute the already-proved/formal `addX` identity

```text
addX(P,R_m) = ψ_{m-1}² φ_{m+1},
```

the formal `addY` expression does **not** reduce to zero from these relations.

The script below gives a concrete counterexample over the nonsingular short curve

```text
Y² = X³ + 1
```

at the point `(X,Y)=(0,1)`.  The assigned formal ψ-symbols satisfy all listed relations, including the shifted even recurrence and the `addX` identity, but the `addY` target evaluates to `-6`, not `0`.

So the direct algebraic proof of the `addY` identity needs additional formal content beyond `HF`, `Hφ`, `Hω`, and the even EDS recurrences.  In particular, the `ω_{m+1}` definition introduces `ψ_{m+3}`; the listed relations do not determine the needed `ψ_{m+3}` contribution strongly enough.  A further division-polynomial/addition identity, or a direct coordinate-ring cofactor proof, is still needed.

## Complete runnable SymPy script

```python
import sympy as sp

# Curve variables and coefficients.
X, Y, a1, a2, a3, a4, a6 = sp.symbols('X Y a1 a2 a3 a4 a6')
FW = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6
psi2 = 2*Y + a1*X + a3

# Formal local EDS symbols.
psi_m_minus_2, psi_m_minus_1, psi_m = sp.symbols('psi_m_minus_2 psi_m_minus_1 psi_m')
psi_m_plus_1, psi_m_plus_2, psi_m_plus_3 = sp.symbols('psi_m_plus_1 psi_m_plus_2 psi_m_plus_3')
psi_2m, psi_2m_plus_2 = sp.symbols('psi_2m psi_2m_plus_2')
phi_m, phi_m_plus_1 = sp.symbols('phi_m phi_m_plus_1')
omega_m, omega_m_plus_1 = sp.symbols('omega_m omega_m_plus_1')

# General ψ3, ψ4, included only for the optional n=3 EDS relation.
b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
prepsi4 = (
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)
psi4 = psi2*prepsi4
psi_m_minus_3 = sp.symbols('psi_m_minus_3')


def jac_addZ(P, Q):
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(P0*Q2**2 - Q0*P2**2)


def jac_addX(P, Q):
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(
        P0*Q0**2*P2**2
        - 2*P1*Q1*P2*Q2
        + P0**2*Q0*Q2**2
        - a1*P0*Q1*P2**2*Q2
        - a1*P1*Q0*P2*Q2**2
        + 2*a2*P0*Q0*P2**2*Q2**2
        - a3*Q1*P2**4*Q2
        - a3*P1*P2*Q2**4
        + a4*Q0*P2**4*Q2**2
        + a4*P0*P2**2*Q2**4
        + 2*a6*P2**4*Q2**4
    )


def jac_negAddY(P, Q):
    P0, P1, P2 = P
    Q0, Q1, Q2 = Q
    return sp.expand(
        -P1*Q0**3*P2**3
        + 2*P1*Q1**2*P2**3
        - 3*P0**2*Q0*Q1*P2**2*Q2
        + 3*P0*P1*Q0**2*P2*Q2**2
        + P0**3*Q1*Q2**3
        - 2*P1**2*Q1*Q2**3
        + a1*P0*Q1**2*P2**4
        + a1*P1*Q0*Q1*P2**3*Q2
        - a1*P0*P1*Q1*P2*Q2**3
        - a1*P1**2*Q0*Q2**4
        - 2*a2*P0*Q0*Q1*P2**4*Q2
        + 2*a2*P0*P1*Q0*P2*Q2**4
        + a3*Q1**2*P2**6
        - a3*P1**2*Q2**6
        - a4*Q0*Q1*P2**6*Q2
        - a4*P0*Q1*P2**4*Q2**3
        + a4*P1*Q0*P2**3*Q2**4
        + a4*P0*P1*P2*Q2**6
        - 2*a6*Q1*P2**6*Q2**3
        + 2*a6*P1*P2**3*Q2**6
    )


def jac_addY_from_addX(P, Q, addX_expr):
    addZ = jac_addZ(P, Q)
    negAddY = jac_negAddY(P, Q)
    return sp.expand(-negAddY - a1*addX_expr*addZ - a3*addZ**3)


P = [X, Y, sp.Integer(1)]
R_m = [phi_m, omega_m, psi_m]
addX_raw = jac_addX(P, R_m)
addY_raw = jac_addY_from_addX(P, R_m, addX_raw)

# Target without using addX identity.
target_raw = sp.expand(2*(addY_raw - psi_m_minus_1**3 * omega_m_plus_1))

# Target after substituting the addX identity addX(P,R_m)=ψ_{m-1}² φ_{m+1}.
addY_using_HaddX = jac_addY_from_addX(P, R_m, psi_m_minus_1**2 * phi_m_plus_1)
target_using_HaddX = sp.expand(2*(addY_using_HaddX - psi_m_minus_1**3 * omega_m_plus_1))

# Formal relations.
Hphi_m = sp.expand(phi_m - (X*psi_m**2 - psi_m_plus_1*psi_m_minus_1))
Hphi_m_plus_1 = sp.expand(phi_m_plus_1 - (X*psi_m_plus_1**2 - psi_m_plus_2*psi_m))
Homega_m = sp.expand(
    2*psi_m*omega_m
    - (psi_2m - psi_m**2*(a1*phi_m + a3*psi_m**2))
)
Homega_m_plus_1 = sp.expand(
    2*psi_m_plus_1*omega_m_plus_1
    - (psi_2m_plus_2 - psi_m_plus_1**2*(a1*phi_m_plus_1 + a3*psi_m_plus_1**2))
)
Heven_m = sp.expand(
    psi2*psi_2m
    - psi_m*(psi_m_plus_2*psi_m_minus_1**2 - psi_m_minus_2*psi_m_plus_1**2)
)
Heven_m_plus_1 = sp.expand(
    psi2*psi_2m_plus_2
    - psi_m_plus_1*(psi_m_plus_3*psi_m**2 - psi_m_minus_1*psi_m_plus_2**2)
)

# Optional n=3 EDS relation, included to test whether adding ψ_{m+3}/ψ_{m-3} helps.
Hodd_n3 = sp.expand(
    psi_m_plus_3*psi_m_minus_3
    - (psi_m_plus_1*psi_m_minus_1*psi3**2 - psi4*psi2*psi_m**2)
)

base_relations = [FW, Hphi_m, Hphi_m_plus_1, Homega_m, Homega_m_plus_1, Heven_m, Heven_m_plus_1]
vars_order = [
    omega_m_plus_1, omega_m, phi_m_plus_1, phi_m, psi_2m_plus_2, psi_2m,
    psi_m_plus_3, psi_m_plus_2, psi_m_minus_2, psi_m_plus_1, psi_m_minus_1, psi_m,
    Y, X, a1, a2, a3, a4, a6,
]

print('building Groebner basis for base relations...')
G = sp.groebner(base_relations, *vars_order, order='lex', domain=sp.QQ)
rem_raw = sp.expand(G.reduce(target_raw)[1])
rem_HaddX = sp.expand(G.reduce(target_using_HaddX)[1])
print('raw_addY_reduces_to_zero =', rem_raw == 0)
print('raw_addY_remainder_terms =', 0 if rem_raw == 0 else len(sp.Poly(rem_raw, *vars_order).terms()))
print('after_substituting_addX_identity_reduces_to_zero =', rem_HaddX == 0)
print('after_HaddX_remainder_terms =', 0 if rem_HaddX == 0 else len(sp.Poly(rem_HaddX, *vars_order).terms()))
print()

print('building Groebner basis with optional n=3 EDS relation...')
vars_order_n3 = [
    omega_m_plus_1, omega_m, phi_m_plus_1, phi_m, psi_2m_plus_2, psi_2m,
    psi_m_plus_3, psi_m_minus_3, psi_m_plus_2, psi_m_minus_2,
    psi_m_plus_1, psi_m_minus_1, psi_m, Y, X, a1, a2, a3, a4, a6,
]
G_n3 = sp.groebner(base_relations + [Hodd_n3], *vars_order_n3, order='lex', domain=sp.QQ)
rem_HaddX_n3 = sp.expand(G_n3.reduce(target_using_HaddX)[1])
print('after_HaddX_plus_n3_EDS_reduces_to_zero =', rem_HaddX_n3 == 0)
print('after_HaddX_plus_n3_remainder_terms =',
      0 if rem_HaddX_n3 == 0 else len(sp.Poly(rem_HaddX_n3, *vars_order_n3).terms()))
print()

# Concrete counterexample satisfying all base relations, the addX identity, and the optional n=3 relation.
# Specialize to the nonsingular short curve y^2 = x^3 + 1 at (X,Y)=(0,1).
# Here ψ2=2 and ψ3=0, ψ4=-16.
subs_counterexample = {
    a1: 0, a2: 0, a3: 0, a4: 0, a6: 1,
    X: 0, Y: 1,
    psi_m: 1,
    psi_m_minus_1: 1,
    psi_m_plus_1: 1,
    psi_m_plus_2: -2,
    psi_m_minus_2: -2,
    psi_m_plus_3: 4,
    psi_m_minus_3: 8,
    psi_2m: 0,
    psi_2m_plus_2: 0,
    phi_m: -1,
    phi_m_plus_1: 2,
    omega_m: 0,
    omega_m_plus_1: 0,
}
all_rels_for_counterexample = base_relations + [sp.expand(addX_raw - psi_m_minus_1**2*phi_m_plus_1), Hodd_n3]
print('counterexample_relation_values =')
print([sp.expand(r.subs(subs_counterexample)) for r in all_rels_for_counterexample])
print('counterexample_target_after_HaddX =', sp.expand(target_using_HaddX.subs(subs_counterexample)))
print('counterexample_curve_discriminant_short = -432 (nonzero)')
```

## Output

```text
building Groebner basis for base relations...
raw_addY_reduces_to_zero = False
raw_addY_remainder_terms = 48
after_substituting_addX_identity_reduces_to_zero = False
after_HaddX_remainder_terms = 44

building Groebner basis with optional n=3 EDS relation...
after_HaddX_plus_n3_EDS_reduces_to_zero = False
after_HaddX_plus_n3_remainder_terms = 44

counterexample_relation_values =
[0, 0, 0, 0, 0, 0, 0, 0, 0]
counterexample_target_after_HaddX = -6
counterexample_curve_discriminant_short = -432 (nonzero)
```

## Interpretation

The proposed direct formal reduction does **not** close.

The counterexample is especially useful: it satisfies

```text
HF,
Hφ_m,
Hφ_{m+1},
Hω_m,
Hω_{m+1},
Heven_m,
Heven_{m+1},
addX(P,R_m)=ψ_{m-1}²φ_{m+1},
and the optional n=3 EDS relation involving ψ_{m+3}ψ_{m-3}.
```

Yet the target is `-6`.  Therefore the `addY` identity is not a formal consequence of those relations alone.  It requires additional division-polynomial content, most likely a genuine `ω`/third-coordinate addition theorem or a direct coordinate-ring cofactor proof.

Lean-facing conclusion: do not plan to finish the `addY` theorem using only these symbolic substitutions.  Either add a stronger formal identity for the `ω` sequence under addition, or generate a direct coordinate-ring certificate for the `addY` identity, analogous to the `addX` cofactor certificates.
