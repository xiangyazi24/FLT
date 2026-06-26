# Q771 (dm1): y-coordinate numerator `ωₙ` / `Ωₙ` for multiplication-by-`n`

Checked against Mathlib rev `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, in particular

```text
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
```

## Answer

No.  At this pinned rev, the y-coordinate numerator `ωₙ` is **not implemented** in Mathlib.

The file does know about Silverman's `ωₙ` in the module documentation.  In the mathematical-background section it describes the associated sequences

```text
φₙ := Xψₙ² - ψₙ₊₁ ψₙ₋₁
ωₙ := (ψ₂ₙ / ψₙ - ψₙ * (a₁φₙ + a₃ψₙ²)) / 2
```

and explains why `ωₙ` should be a polynomial.  But this is documentation/background, not a Lean definition.  The actual “Main definitions” list ends with

```text
* `WeierstrassCurve.ψ`: the bivariate `n`-division polynomials `ψₙ`.
* `WeierstrassCurve.φ`: the bivariate polynomials `φₙ`.
* TODO: the bivariate polynomials `ωₙ`.
```

There is also a later implementation-note TODO for the definition of `ωₙ`.

So, in this rev, there is no usable declaration such as

```lean
WeierstrassCurve.ω
WeierstrassCurve.Ω
WeierstrassCurve.omega
WeierstrassCurve.Omega
```

for the y-coordinate numerator.

## Closest existing Mathlib objects

The closest implemented infrastructure is the `ψ`/`φ`/`Φ` setup for the denominator and the x-coordinate numerator.

### 1. Full bivariate division polynomials

Mathlib defines

```lean
protected noncomputable def WeierstrassCurve.ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
```

This is the bivariate `n`-division polynomial `ψₙ`.

### 2. Bivariate x-coordinate numerator

Mathlib defines

```lean
protected noncomputable def WeierstrassCurve.φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)
```

This is the bivariate `φₙ` from the standard formula

```text
x([n]P) = φₙ(P) / ψₙ(P)^2.
```

### 3. Univariate coordinate-ring representative of `φₙ`

Mathlib also defines the univariate polynomial

```lean
protected noncomputable def WeierstrassCurve.Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) *
    if Even n then 1 else W.Ψ₂Sq
```

and proves the coordinate-ring congruence

```lean
lemma WeierstrassCurve.Affine.CoordinateRing.mk_φ (n : ℤ) :
  mk W (W.φ n) = mk W (C <| W.Φ n)
```

Thus `W.Φ n` is the implemented closest analogue of a numerator polynomial, but it is the **x-coordinate numerator**, not the y-coordinate numerator.

### 4. Coordinate-ring congruences for `ψ`

Mathlib proves that the bivariate `ψₙ` agrees in the coordinate ring with the reduced/full `Ψₙ` representative:

```lean
lemma WeierstrassCurve.Affine.CoordinateRing.mk_ψ (n : ℤ) :
  mk W (W.ψ n) = mk W (W.Ψ n)
```

and that its square agrees with the univariate `ΨSqₙ` representative:

```lean
lemma WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) :
  mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)
```

Together with `mk_φ`, these are the main existing coordinate-ring facts around the division-polynomial formulas.

## Does Mathlib have the cleared y-coordinate equation involving `ωₙ`?

No, not in the requested form.

The desired identity is

```text
ωₙ² + a₁ Φₙ ωₙ ψₙ + a₃ ωₙ ψₙ³
  = Φₙ³ + a₂ Φₙ² ψₙ² + a₄ Φₙ ψₙ⁴ + a₆ ψₙ⁶.
```

Mathlib cannot currently state this as a theorem about Mathlib's `ωₙ`, because there is no `ωₙ` declaration.

What Mathlib does have is the underlying affine Weierstrass equation polynomial:

```lean
noncomputable def WeierstrassCurve.Affine.polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
    C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
```

and the affine coordinate ring

```lean
abbrev WeierstrassCurve.Affine.CoordinateRing : Type _ :=
  AdjoinRoot W.polynomial
```

with quotient map

```lean
WeierstrassCurve.Affine.CoordinateRing.mk : R[X][Y] →+* W.CoordinateRing
```

So the curve equation itself is available through the quotient by `W.polynomial`.  There are also support lemmas such as

```lean
lemma WeierstrassCurve.C_Ψ₂Sq :
  C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial

lemma WeierstrassCurve.ψ₂_sq :
  W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial

lemma WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq :
  mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
```

These are useful for replacing `ψ₂²` by the univariate `Ψ₂Sq` in the coordinate ring, and they are part of the infrastructure used to prove the `ΨSq`, `Ψ`, and `Φ` congruences.

But there is no theorem in this file, nor an apparent declaration elsewhere in Mathlib at this rev, of the form

```lean
omega_curve_relation
mk_omega
mk_Ω
mul_y_numerator_eq
```

or a cleared Weierstrass-equation identity involving `Φ`, `ψ`, and `ω`.

## Practical implication

For current Mathlib work at this rev:

* If you need the x-coordinate formula, use `W.φ n`, `W.Φ n`, and especially

  ```lean
  WeierstrassCurve.Affine.CoordinateRing.mk_φ
  ```

* If you need denominator-square reduction, use

  ```lean
  WeierstrassCurve.Affine.CoordinateRing.mk_ψ
  WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
  ```

* If you need the y-coordinate numerator, you must define it yourself, or avoid it by working directly with the affine/projective group-law formulas for the point `[n]P`.

The likely future Mathlib direction is exactly what the TODO says: add the bivariate polynomials `ωₙ`.  But because the documented formula involves both division by `ψₙ` and division by `2`, implementing it over a general `CommRing` is not just a one-line definition.  The module documentation explicitly notes that well-definedness should be proved universally and then transported by specialization.  That infrastructure is not present in the pinned file.
