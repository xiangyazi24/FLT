# Q317 (dm1): exact `linear_combination` coefficients for the general symbolic `addX` proof

## Result

There is one normalization issue to be explicit about.

With

```text
ψ₂ = 2Y + a₁X + a₃
Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆
HF = Y² + a₁XY + a₃Y - X³ - a₂X² - a₄X - a₆
```

we have

```text
ψ₂² = Ψ₂Sq + 4*HF.
```

So there are two equivalent coefficient lists depending on which Ward/Hmiss lemma you use.

---

## Coefficients for the Hmiss stated in the prompt, using `Ψ₂Sq`

Define

```text
Hφ = φ_m - (X*ψ_m² - ψ_{m+1}*ψ_{m-1})
Hω = 2*ψ_m*ω_m - (ψ_{2m} - ψ_m²*(a₁*φ_m + a₃*ψ_m²))
Heven = ψ_{2m}*ψ₂ - (ψ_{m-1}²*ψ_m*ψ_{m+2} - ψ_{m-2}*ψ_m*ψ_{m+1}²)
Hmiss_Ψ = ψ_{m-1}²*ψ_{m+2} + ψ_{m-2}*ψ_{m+1}²
           + ψ_m³*Ψ₂Sq
           - ψ_{m-1}*ψ_m*ψ_{m+1}*(6X² + b₂X + b₄)
```

Then

```text
2*(addX(P,R_m) - ψ_{m-1}²*φ_{m+1})
  = c₁*Hω + c₂*Heven + c₃*Hmiss_Ψ + c₄*Hφ + c₅*HF
```

with

```text
c₁ = -ψ₂
c₂ = -1
c₃ = ψ_m
c₄ = (4X² + b₂X + b₄)*ψ_m² + 2X*φ_m - 2X*ψ_{m-1}*ψ_{m+1}
c₅ = 0
```

So, **with the Hmiss exactly as written in the prompt using `Ψ₂Sq`, the HF coefficient is `0`, not `-4*ψ_m^4`.**

---

## Coefficients for the bivariate/full Hmiss using `ψ₂²`

If instead you use the bivariate Ward/Hmiss lemma

```text
Hmiss_ψ₂ = ψ_{m-1}²*ψ_{m+2} + ψ_{m-2}*ψ_{m+1}²
           + ψ_m³*ψ₂²
           - ψ_{m-1}*ψ_m*ψ_{m+1}*(6X² + b₂X + b₄)
```

then the same identity is

```text
2*(addX(P,R_m) - ψ_{m-1}²*φ_{m+1})
  = c₁*Hω + c₂*Heven + c₃*Hmiss_ψ₂ + c₄*Hφ + c₅*HF
```

with

```text
c₁ = -ψ₂
c₂ = -1
c₃ = ψ_m
c₄ = (4X² + b₂X + b₄)*ψ_m² + 2X*φ_m - 2X*ψ_{m-1}*ψ_{m+1}
c₅ = -4*ψ_m^4
```

This is the source of the `-4*ψ_m^4` cofactor: it belongs to the version of `Hmiss` with `ψ₂²`, since

```text
ψ_m*Hmiss_ψ₂ = ψ_m*Hmiss_Ψ + 4*ψ_m^4*HF.
```

---

## Lean-oriented coefficient names

Using Lean-ish names:

```lean
-- schematic
c₁ := -(ψ₂)
c₂ := -1
c₃ := ψ_m
c₄ := (4*X^2 + b₂*X + b₄) * ψ_m^2
        + 2*X*φ_m - 2*X*ψ_{m-1}*ψ_{m+1}
c₅_Ψ  := 0
c₅_ψ₂ := -4*ψ_m^4
```

Be careful about the sign convention for `Hφ`.  The coefficients above use

```text
Hφ = φ_m - (X*ψ_m² - ψ_{m+1}*ψ_{m-1}).
```

If your Lean lemma states the opposite residual

```text
X*ψ_m² - ψ_{m+1}*ψ_{m-1} - φ_m = 0,
```

then replace `c₄` by `-c₄`.

---

## Runnable SymPy verification script

```python
import sympy as sp

# Curve variables and general Weierstrass coefficients.
X, Y = sp.symbols('X Y')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')

# Formal division-polynomial symbols.
pm2, pm1, pm, pp1, pp2, p2m = sp.symbols(
    'psi_m_minus_2 psi_m_minus_1 psi_m psi_m_plus_1 psi_m_plus_2 psi_2m'
)
om, ph = sp.symbols('omega_m phi_m')

b2 = a1**2 + 4*a2
b4 = a1*a3 + 2*a4
b6 = a3**2 + 4*a6
Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
half_dPsi2Sq = 6*X**2 + b2*X + b4
psi2 = 2*Y + a1*X + a3
HF = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

# Hφ and φ_{m+1}.
Hphi = ph - (X*pm**2 - pp1*pm1)
phi_m_plus_1 = X*pp1**2 - pp2*pm

# General Weierstrass addX for P=[X,Y,1], Q=[φ_m,ω_m,ψ_m].
addX = (
    X*ph**2
    - 2*Y*om*pm
    + X**2*ph*pm**2
    - a1*X*om*pm
    - a1*Y*ph*pm**2
    + 2*a2*X*ph*pm**2
    - a3*om*pm
    - a3*Y*pm**4
    + a4*ph*pm**2
    + a4*X*pm**4
    + 2*a6*pm**4
)

LHS = sp.expand(2*(addX - pm1**2*phi_m_plus_1))

Homega = sp.expand(2*pm*om - (p2m - pm**2*(a1*ph + a3*pm**2)))
Heven = sp.expand(p2m*psi2 - (pm1**2*pm*pp2 - pm2*pm*pp1**2))
Hmiss_Psi = sp.expand(
    pm1**2*pp2 + pm2*pp1**2 + pm**3*Psi2Sq - pm1*pm*pp1*half_dPsi2Sq
)
Hmiss_psi2 = sp.expand(
    pm1**2*pp2 + pm2*pp1**2 + pm**3*psi2**2 - pm1*pm*pp1*half_dPsi2Sq
)

c1 = -psi2
c2 = -1
c3 = pm
c4 = sp.expand((4*X**2 + b2*X + b4)*pm**2 + 2*X*ph - 2*X*pm1*pp1)
c5_Psi = sp.Integer(0)
c5_psi2 = -4*pm**4

check_Psi = sp.expand(
    LHS - (c1*Homega + c2*Heven + c3*Hmiss_Psi + c4*Hphi + c5_Psi*HF)
)
check_psi2 = sp.expand(
    LHS - (c1*Homega + c2*Heven + c3*Hmiss_psi2 + c4*Hphi + c5_psi2*HF)
)

print('c1 =', c1)
print('c2 =', c2)
print('c3 =', c3)
print('c4 =', c4)
print('c5 for Hmiss_Psi =', c5_Psi)
print('c5 for Hmiss_psi2 =', c5_psi2)
print()
print('check with Hmiss_Psi == 0?', check_Psi == 0)
print('check with Hmiss_psi2 == 0?', check_psi2 == 0)
print()
print('Hmiss_psi2 - Hmiss_Psi =', sp.factor(Hmiss_psi2 - Hmiss_Psi))
print('expected difference 4*psi_m^3*HF?', sp.expand((Hmiss_psi2 - Hmiss_Psi) - 4*pm**3*HF) == 0)
print('OK')
```

## Output

```text
c1 = -X*a1 - 2*Y - a3
c2 = -1
c3 = psi_m
c4 = 4*X**2*psi_m**2 + X*a1**2*psi_m**2 + 4*X*a2*psi_m**2 + 2*X*phi_m - 2*X*psi_m_minus_1*psi_m_plus_1 + a1*a3*psi_m**2 + 2*a4*psi_m**2
c5 for Hmiss_Psi = 0
c5 for Hmiss_psi2 = -4*psi_m**4

check with Hmiss_Psi == 0? True
check with Hmiss_psi2 == 0? True

Hmiss_psi2 - Hmiss_Psi = 4*psi_m**3*(-X**3 - X**2*a2 + X*Y*a1 - X*a4 + Y**2 + Y*a3 - a6)
expected difference 4*psi_m^3*HF? True
OK
```

## Practical Lean recommendation

If the Lean `Hmiss` lemma you have is already the **univariate/reduced** version with `C W.Ψ₂Sq`, use:

```text
c₅ = 0.
```

If the Lean `Hmiss` lemma is the **bivariate/full** version with `W.ψ₂^2`, use:

```text
c₅ = -4*ψ_m^4.
```

Both are correct, and the script verifies both exact identities. The rest of the coefficients are unchanged.
