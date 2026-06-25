# Q498 (dm2): CAS check for pure polynomial `(X₀-X₁)^3` divisibility

## Executive result

The proposed **pure polynomial** identity is false.

After substituting

```text
P₁ = [t₁, -1, s₁],   P₂ = [t₂, -1, s₂]
```

Mathlib's `Projective.addX(P₁,P₂)` and `Projective.addY(P₁,P₂)` are **not** divisible by

```text
D^3 := (t₁ - t₂)^3
```

in

```text
ℚ[a₁,a₂,a₃,a₄,a₆,t₁,t₂,s₁,s₂].
```

So the sub-agent's claim, if interpreted with independent `s₁,s₂`, is wrong.  The cube factor can only appear after imposing extra structure, such as `sᵢ = w(tᵢ)` with `w` the Weierstrass formal parameter series, or an equivalent curve-equation/formal-series certificate.

---

## Minimal counterexample

Set all Weierstrass coefficients to zero and set

```text
s₁ = s₂ = 1.
```

Then the specialized formulas give

```text
addX([t₁,-1,1], [t₂,-1,1]) = -3 * (t₁ - t₂)
addY([t₁,-1,1], [t₂,-1,1]) = -3 * t₁ * t₂ * (t₁ - t₂)
```

Neither expression is divisible by `(t₁ - t₂)^3`.

This is already a counterexample even with `Z₀ = Z₁` constant.  Therefore the identity is not a consequence of just setting `Y₀ = Y₁ = -1`.

---

## SymPy check

The following script uses the current Mathlib projective formulas.  In Mathlib,

```lean
addY P Q = negY ![addX P Q, negAddY P Q, addZ P Q]
```

and

```lean
negY ![X,Y,Z] = -Y - a₁*X - a₃*Z.
```

```python
import sympy as sp

t1,t2,s1,s2 = sp.symbols('t1 t2 s1 s2')
a1,a2,a3,a4,a6 = sp.symbols('a1 a2 a3 a4 a6')

Px,Py,Pz = t1,-1,s1
Qx,Qy,Qz = t2,-1,s2
D = t1 - t2

addZ = (
    -3*Px**2*Qx*Qz + 3*Px*Qx**2*Pz + Py**2*Qz**2 - Qy**2*Pz**2
    + a1*Px*Py*Qz**2 - a1*Qx*Qy*Pz**2 - a2*Px**2*Qz**2
    + a2*Qx**2*Pz**2 + a3*Py*Pz*Qz**2 - a3*Qy*Pz**2*Qz
    - a4*Px*Pz*Qz**2 + a4*Qx*Pz**2*Qz
)

addX = (
    -Px*Qy**2*Pz + Qx*Py**2*Qz - 2*Px*Py*Qy*Qz + 2*Qx*Py*Qy*Pz
    - a1*Px**2*Qy*Qz + a1*Qx**2*Py*Pz + a2*Px**2*Qx*Qz
    - a2*Px*Qx**2*Pz - a3*Px*Py*Qz**2 + a3*Qx*Qy*Pz**2
    - 2*a3*Px*Qy*Pz*Qz + 2*a3*Qx*Py*Pz*Qz
    + a4*Px**2*Qz**2 - a4*Qx**2*Pz**2 + 3*a6*Px*Pz*Qz**2
    - 3*a6*Qx*Pz**2*Qz
)

negAddY = (
    -3*Px**2*Qx*Qy + 3*Px*Qx**2*Py - Py**2*Qy*Qz + Py*Qy**2*Pz
    + a1*Px*Qy**2*Pz - a1*Qx*Py**2*Qz - a2*Px**2*Qy*Qz
    + a2*Qx**2*Py*Pz + 2*a2*Px*Qx*Py*Qz
    - 2*a2*Px*Qx*Qy*Pz - a3*Py**2*Qz**2 + a3*Qy**2*Pz**2
    + a4*Px*Py*Qz**2 - 2*a4*Px*Qy*Pz*Qz
    + 2*a4*Qx*Py*Pz*Qz - a4*Qx*Qy*Pz**2
    + 3*a6*Py*Pz*Qz**2 - 3*a6*Qy*Pz**2*Qz
)

addY = -negAddY - a1*addX - a3*addZ

for name, expr in [('addX', addX), ('addY', addY)]:
    rem3 = sp.rem(sp.Poly(sp.expand(expr), t1), sp.Poly(D**3, t1)).as_expr()
    diag = sp.factor(sp.expand(expr).subs(t1, t2))
    print(name, 'divisible_by_D3:', sp.expand(rem3) == 0)
    print(name, 'diag:', diag)
    print(name, 'rem3 factor:', sp.factor(rem3))
    print()

simple = {a1:0, a2:0, a3:0, a4:0, a6:0, s1:1, s2:1}
print('simple addX =', sp.factor(addX.subs(simple)))
print('simple addY =', sp.factor(addY.subs(simple)))
```

Output:

```text
addX divisible_by_D3: False
addX diag: -t2*(s1 - s2)*(a1*t2 + a2*t2**2 + a3*s1 + a3*s2 + a4*s1*t2 + a4*s2*t2 + 3*a6*s1*s2 - 1)

addY divisible_by_D3: False
addY diag: (s1 - s2)*(a1**2*t2**2 + a1*a2*t2**3 + a1*a4*s1*t2**2 + a1*a4*s2*t2**2 + 3*a1*a6*s1*s2*t2 - 2*a1*t2 - a2*a3*s1*t2**2 - a2*a3*s2*t2**2 - a2*t2**2 - a3**2*s1*s2 - a3*a4*s1*s2*t2 - 3*a3*t2**3 - a4*s1*t2 - a4*s2*t2 - 3*a6*s1*s2 + 1)

simple addX = -3*(t1 - t2)
simple addY = -3*t1*t2*(t1 - t2)
```

The diagonal values also show the issue clearly: without a relation forcing `s₁ = s₂` when `t₁ = t₂`, even first-order vanishing can fail.

---

## Why the mistaken pure statement looked plausible

The identity

```lean
Projective.addXYZ_self : W.addXYZ P P = ![0,0,0]
```

only says that the formula vanishes after substituting the **same full vector** for both inputs.  It does not imply a cube factor in the polynomial ring with independent `Z` variables.

Likewise, setting `Y₀ = Y₁ = -1` is not enough.  One still needs the fact that the `Z` coordinates are the same one-variable formal series evaluated at different variables:

```text
Z₀ = w(t₁),   Z₁ = w(t₂).
```

Then

```text
Z₀ - Z₁
```

is divisible by `t₁ - t₂`, and so is

```text
t₁*Z₁ - t₂*Z₀.
```

Those extra diagonal-difference factors are exactly what the independent-variable pure polynomial test is missing.

As a sanity check, in the degenerate coefficient specialization `a₁=...=a₆=0` with the curve-compatible choice `w(t)=t^3`, SymPy gives

```text
addX([t₁,-1,t₁^3], [t₂,-1,t₂^3]) = -(t₁-t₂)^3*(t₁+t₂)
addY([t₁,-1,t₁^3], [t₂,-1,t₂^3]) =  (t₁-t₂)^3
addZ([t₁,-1,t₁^3], [t₂,-1,t₂^3]) = -(t₁-t₂)^3*(t₁+t₂)^3
```

So the cube divisibility can be true after the `Z=w(X)` specialization, but it is not a pure identity in `t₁,t₂,s₁,s₂`.

---

## Lean recommendation

Do **not** try to prove the following pure-polynomial theorem:

```lean
theorem addX_cube_dvd_pure
    (W : WeierstrassCurve.Projective R) :
    ((t₁ - t₂)^3) ∣
      W.addX ![t₁, -1, s₁] ![t₂, -1, s₂] := by
  -- false
```

and similarly do not try it for `addY`.

The correct theorem must include either:

1. direct substitution of the formal parameter series
   ```lean
   Z₀ = formalW₀,  Z₁ = formalW₁,
   ```
   followed by an explicit factor certificate; or
2. a quotient/certificate modulo the two curve equations plus diagonal-difference lemmas.

A robust target is:

```lean
noncomputable def formalAddXQuot (W : WeierstrassCurve.Projective K) : MvPowerSeries (Fin 2) K :=
  -- explicit quotient after substituting `Zᵢ = formalW(tᵢ)`
  sorry

noncomputable def formalAddYQuot (W : WeierstrassCurve.Projective K) : MvPowerSeries (Fin 2) K :=
  -- explicit quotient after substituting `Zᵢ = formalW(tᵢ)`
  sorry

theorem formalAddX_eq_D_cube_mul (W : WeierstrassCurve.Projective K) :
    formalAddX W = D^3 * formalAddXQuot W := by
  -- unfold `formalAddX`; rewrite `formalW₀ - formalW₁ = D * E`; ring/certificate
  sorry

theorem formalAddY_eq_D_cube_mul (W : WeierstrassCurve.Projective K) :
    formalAddY W = D^3 * formalAddYQuot W := by
  -- same: direct certificate after `Z=w(X)` specialization
  sorry
```

The key helper is still the diagonal quotient lemma:

```lean
formalW₀ - formalW₁ = (X₀ - X₁) * formalW_diagQuot
```

and similarly for

```lean
X₀ * formalW₁ - X₁ * formalW₀.
```

But the final cube divisibility must be proved **after** these substitutions.  The pure independent-`Z` statement is refuted by the counterexample above.
