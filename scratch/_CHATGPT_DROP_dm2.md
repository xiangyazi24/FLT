# Q522 (dm2): Mathlib API for `Projective.addX` in chord variables `U,V`

## Executive answer

Yes: Mathlib has the useful chord-variable formula for `Projective.addX`, but it is **not** a definitional/pure polynomial factorization of `addX`.  It is the cleared-denominator, curve-equation-dependent lemma

```lean
Projective.addX_eq'
```

with hypotheses

```lean
hP : W'.Equation P
hQ : W'.Equation Q
```

It rewrites

```text
addX(P,Q) * (Pz*Qz)^2
```

as a homogeneous cubic expression in the two chord variables

```text
U := Px*Qz - Qx*Pz,
V := Py*Qz - Qy*Pz.
```

Mathlib also has

```lean
Projective.addZ_eq'
```

which gives

```text
addZ(P,Q) * (Pz*Qz) = U^3.
```

There is no general `addY_eq'` with a full `U,V` expression for `addY` itself, but there is a factored lemma for `negAddY`:

```lean
Projective.negAddY_eq'
```

and since

```lean
addY P Q = negY ![addX P Q, negAddY P Q, addZ P Q]
```

one can derive the corresponding cleared-denominator cubic formula for `addY` by combining `negAddY_eq'`, `addX_eq'`, and `addZ_eq'`.

---

## What grep found

A search in the accessible `xiangyazi24/FLT` source itself did not return direct hits for `addX_eq'`/`addZ_eq'`, which suggests the file is coming from the Mathlib dependency rather than being vendored in the FLT repo.  In Mathlib's source file

```text
Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean
```

the relevant API is present.

---

## Exact formulas

Let

```text
U := P x * Q z - Q x * P z
V := P y * Q z - Q y * P z
ZPQ := P z * Q z.
```

### `addZ_eq'`

Mathlib has:

```lean
lemma addZ_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ
```

So, modulo the two curve equations,

```text
addZ * ZPQ = U^3.
```

In the field/nonzero-`Z` version, Mathlib also has

```lean
lemma addZ_eq ... :
    W.addZ P Q = (P x * Q z - Q x * P z) ^ 3 / (P z * Q z)
```

### `addX_eq'`

Mathlib has:

```lean
lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2
        - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2)
        * (P x * Q z - Q x * P z) := by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ
```

In `U,V` notation:

```text
addX * ZPQ^2
  = ( V^2 * ZPQ
      + a₁ * V * ZPQ * U
      - a₂ * ZPQ * U^2
      - Px*Qz * U^2
      - Qx*Pz * U^2 ) * U.
```

This is homogeneous of degree `3` in `(U,V)`.

### `negAddY_eq'`

Mathlib has the analogous formula for the negative `Y` coordinate:

```lean
lemma negAddY_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.negAddY P Q * (P z * Q z) ^ 2 =
      (P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2
        - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2
        - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ
```

In `U,V` notation:

```text
negAddY * ZPQ^2
  = V * ( V^2*ZPQ
          + a₁*V*ZPQ*U
          - a₂*ZPQ*U^2
          - Px*Qz*U^2
          - Qx*Pz*U^2
          - Px*Qz*U^2 )
    + Py*Qz*U^3.
```

This is again homogeneous of degree `3` in `(U,V)`.

### `addY`

Mathlib defines

```lean
def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]
```

and

```lean
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z
```

Therefore

```text
addY = -negAddY - a₁*addX - a₃*addZ.
```

Multiplying by `ZPQ^2` and using the three preceding factored lemmas gives a derived formula

```text
addY * ZPQ^2
  = -(negAddY * ZPQ^2)
    - a₁*(addX * ZPQ^2)
    - a₃*(addZ * ZPQ)*ZPQ.
```

Every term on the right is homogeneous of degree `3` in `(U,V)`.  So `addY` also has a cleared-denominator cubic-in-`U,V` expression, but Mathlib does not appear to expose this as a named general `addY_eq'` lemma.  The named `addY_of_X_eq'` is only the special `U=0` case.

---

## Degrees in `(U,V)`

The practical degree table is:

| coordinate | Mathlib API | cleared expression | degree in `(U,V)` |
|---|---|---:|---:|
| `addZ` | `addZ_eq'` | `addZ * ZPQ = U^3` | `3` |
| `addX` | `addX_eq'` | `addX * ZPQ^2 = cubic(U,V)` | `3` |
| `negAddY` | `negAddY_eq'` | `negAddY * ZPQ^2 = cubic(U,V)` | `3` |
| `addY` | derived from `addY`, `negY`, `addX_eq'`, `negAddY_eq'`, `addZ_eq'` | `addY * ZPQ^2 = cubic(U,V)` | `3` |

So, morally, the addition coordinates vanish to order `3` in the chord variables.

---

## Important Lean caveat

These lemmas prove cubic divisibility only for the **cleared** expressions:

```text
addZ * (Pz*Qz),
addX * (Pz*Qz)^2,
negAddY * (Pz*Qz)^2,
addY * (Pz*Qz)^2.
```

They do **not** automatically prove

```text
D^3 ∣ addX
D^3 ∣ addY
D^3 ∣ addZ
```

inside `MvPowerSeries`, because in the formal-parameter application

```text
Pz = w(t₁),   Qz = w(t₂),
```

and `w(t)` begins with `t^3`, so `Pz*Qz` is **not a unit**.  Thus one cannot simply cancel the `ZPQ` factors in `MvPowerSeries`.

For the formal group target, the best use of these lemmas is:

1. define
   ```text
   U = X₀*w₁ - X₁*w₀,
   V = -w₁ + w₀ = w₀ - w₁
   ```
   for `P(t)=[t,-1,w(t)]`;
2. prove `D ∣ U` and `D ∣ V`, where `D = X₀-X₁`;
3. use `addX_eq'`, `negAddY_eq'`, `addZ_eq'` to show the cleared numerators have a `D^3` factor;
4. separately prove the raw `formalAddX = D^3 * Q` / `formalAddY = D^3 * Q` certificates, or work in a localized/Laurent setting where the `w₀w₁` factor is invertible.

This explains the Q512 CAS result: the raw `formalAddX` cube factor is true after substitution, but the Mathlib factored lemmas alone give the cube factor for the cleared equations.  They are excellent for reducing the expansion size and for checking the order, but they do not by themselves solve the nonunit-cancellation problem in `MvPowerSeries`.
