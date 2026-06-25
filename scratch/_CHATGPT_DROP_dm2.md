# Q392 / dm2 — CAS recipe for `addY` assembly in the coordinate ring

This is a SymPy script for the `addY` assembly calculation with formal division-polynomial symbols.  It prints the residual after each rewrite, so the output gives a Lean `calc` order.

The important convention used below is the generalized Weierstrass omega identity

```text
2 ψ_n ω_n = ψ_{2n} - a₁ φ_n ψ_n² - a₃ ψ_n⁴.
```

For the normalized addition output, set

```text
Z = X ψ_m² - φ_m = ψ_{m-1} ψ_{m+1},
U = Y ψ_m³ - ω_m,
N = Xω_m - Yφ_mψ_m.
```

Then Mathlib’s affine addition formula

```text
y(P + R_m) = -(λ + a₁)x(P + R_m) - ν - a₃
```

with

```text
λ = U/(ψ_m Z),   ν = N/(ψ_m Z)
```

gives the cleared numerator

```text
addY = -((U·addX + N·Z²)/ψ_m) - a₁·addX·Z - a₃·Z³.
```

The target is

```text
addY = ψ_{m-1}³ · ω_{m+1}.
```

## Short warning

Using exactly the shifted EDS identity as stated leaves the residual

```text
ψ₂ ψ_{m-1}² · (ψ_{m+2}ψ_m³ - ψ_{m-1}ψ_{m+1}³ - ψ_{2m+1}) / 2.
```

So the final zero also needs the standard odd EDS recurrence

```text
ψ_{2m+1} = ψ_{m+2}ψ_m³ - ψ_{m-1}ψ_{m+1}³.
```

If your Lean lemma named `eds_shifted` already packages this odd recurrence, then fold the final `Hodd` step below into that rewrite.

## Runnable script

```python
import sympy as sp

# Symbols: coefficients and affine coordinates in the coordinate ring.
X, Y = sp.symbols("X Y")
a1, a2, a3, a4, a6 = sp.symbols("a1 a2 a3 a4 a6")

# Formal division-polynomial symbols.
psi2 = sp.symbols("psi2")
pm2, pm1, p0, pp1, pp2, pp3 = sp.symbols(
    "psi_m2 psi_m1 psi_m psi_p1 psi_p2 psi_p3"
)
p2m, p2m1, p2mp2 = sp.symbols("psi_2m psi_2m1 psi_2mp2")

# Formal phi/omega/addX symbols.
phi_m, phi_p1 = sp.symbols("phi_m phi_p1")
omega_m, omega_p1 = sp.symbols("omega_m omega_p1")
addX = sp.symbols("addX")

def nf(e):
    return sp.factor(sp.cancel(sp.expand(e)))

def show(label, e):
    print("\n--", label)
    print(sp.factor(sp.cancel(e)))

# Weierstrass relation for the final coordinate-ring check.
FW = Y**2 + a1*X*Y + a3*Y - (X**3 + a2*X**2 + a4*X + a6)

def mod_FW(e):
    """Reduce numerator modulo F_W, viewed as a monic quadratic in Y."""
    num, den = sp.together(e).as_numer_denom()
    rem = sp.rem(sp.Poly(sp.expand(num), Y), sp.Poly(FW, Y)).as_expr()
    return nf(rem / den)

# Mathlib affine addition shape, normalized so the output Z is
#   Z = X*psi_m^2 - phi_m = psi_{m-1}*psi_{m+1}.
#
# Write U = Y*psi_m^3 - omega_m and
#       N = X*omega_m - Y*phi_m*psi_m.
# Then lambda = U/(psi_m*Z) and nu = N/(psi_m*Z), and
#   y(P+R_m) = -(lambda+a1)*x(P+R_m) - nu - a3.
#
# addY is the numerator after clearing Z^3:
#   addY = -((U*addX + N*Z^2)/psi_m) - a1*addX*Z - a3*Z^3.
Z = X*p0**2 - phi_m
U = Y*p0**3 - omega_m
N = X*omega_m - Y*phi_m*p0
addY = -((U*addX + N*Z**2)/p0) - a1*addX*Z - a3*Z**3

R = addY - pm1**3 * omega_p1
show("0. raw residual addY - psi_{m-1}^3*omega_{m+1}", R)

# 1. addX helper.
R = nf(R.subs(addX, pm1**2 * phi_p1))
show("1. use HaddX: addX -> psi_{m-1}^2*phi_{m+1}", R)

# 2-3. phi definitions.
R = nf(R.subs(phi_m, X*p0**2 - pp1*pm1))
show("2. use Hphi_m: phi_m -> X*psi_m^2 - psi_{m+1}*psi_{m-1}", R)

R = nf(R.subs(phi_p1, X*pp1**2 - pp2*p0))
show("3. use Hphi_{m+1}: phi_{m+1} -> X*psi_{m+1}^2 - psi_{m+2}*psi_m", R)

# 4-5. General omega identity:
#   2*psi_n*omega_n =
#     psi_{2n} - a1*phi_n*psi_n^2 - a3*psi_n^4.
omega_m_rhs = (p2m - a1*(X*p0**2 - pp1*pm1)*p0**2 - a3*p0**4) / (2*p0)
R = nf(R.subs(omega_m, omega_m_rhs))
show("4. use Homega_m", R)

omega_p1_rhs = (p2mp2 - a1*(X*pp1**2 - pp2*p0)*pp1**2 - a3*pp1**4) / (2*pp1)
R = nf(R.subs(omega_p1, omega_p1_rhs))
show("5. use Homega_{m+1}", R)

# 6-7. Even division-polynomial identities:
#   psi_{2m}*psi2 = psi_m*(psi_{m+2}*psi_{m-1}^2 - psi_{m-2}*psi_{m+1}^2)
#   psi_{2(m+1)}*psi2 = psi_{m+1}*(psi_{m+3}*psi_m^2 - psi_{m-1}*psi_{m+2}^2)
R = nf(R.subs(p2m, p0*(pp2*pm1**2 - pm2*pp1**2)/psi2))
show("6. use Heven_m", R)

R = nf(R.subs(p2mp2, pp1*(pp3*p0**2 - pm1*pp2**2)/psi2))
show("7. use Heven_{m+1}", R)

# 8. Put the occurrence of 2Y+a1X+a3 back into the formal symbol psi2.
# SymPy does not reliably do this replacement once expanded, so we regroup and verify.
odd_lhs = pp2*p0**3 - pm1*pp1**3
shifted_lhs = p0**2*pp3*pm1 - pm2*pp1**2*pp2
R_regrouped = pm1**2 * (psi2**2 * odd_lhs - shifted_lhs) / (2*psi2)
assert nf((R - R_regrouped).subs(psi2, 2*Y + a1*X + a3)) == 0
R = nf(R_regrouped)
show("8. use Hpsi2: psi2 = 2Y + a1X + a3, then regroup", R)

# 9. Shifted EDS identity from the prompt:
#   psi_m^2*psi_{m+3}*psi_{m-1}
#     - psi_{m-2}*psi_{m+1}^2*psi_{m+2}
#   = psi2^2*psi_{2m+1}
R = nf(R.subs(shifted_lhs, psi2**2 * p2m1))
show("9. use eds_shifted", R)

# The residual left by exactly the listed shifted EDS relation is now visible.
# To reach zero one also needs the standard odd EDS recurrence:
#   psi_{2m+1} = psi_{m+2}*psi_m^3 - psi_{m-1}*psi_{m+1}^3.
R = nf(R.subs(p2m1, odd_lhs))
show("10. use Hodd: psi_{2m+1} -> psi_{m+2}*psi_m^3 - psi_{m-1}*psi_{m+1}^3", R)

print("\nfinal mod F_W =", mod_FW(R))
assert mod_FW(R) == 0
```

## Lean substitution order

Use this order in the `calc` proof:

```text
1.  HaddX
2.  Hφ_m
3.  Hφ_{m+1}
4.  Hω_m
5.  Hω_{m+1}
6.  Heven_m
7.  Heven_{m+1}
8.  Hψ₂ / regroup to expose ψ₂²
9.  eds_shifted
10. Hodd, unless your eds_shifted lemma already includes the odd EDS recurrence
11. reduce modulo F_W / ring_nf
```

The final printed line is

```text
final mod F_W = 0
```
