# Q477 (dm2): proving `(X₀ - X₁)^3 ∣ formalAddY`

## Executive recommendation

Use **option (c)**, but in a slightly strengthened form:

> prove a generic algebraic factorization certificate for `Projective.addY` along the diagonal, then instantiate it in `MvPowerSeries (Fin 2) K` using a reusable diagonal-difference quotient lemma.

Do **not** try to get the result by cancelling `w₀w₁` from an identity involving `formalAddZ * w₀w₁`.  Algebraically that coprimality story is true, but in Lean it is the wrong battle: `MvPowerSeries` will not give you a pleasant UFD/gcd/coprime API for proving that `(X₀-X₁)` is coprime to `X₀X₁`, and the target is `formalAddY`, not `formalAddZ`.

The fastest Lean path is:

```lean
((X 0 - X 1)^3 : MvPowerSeries (Fin 2) K) ∣ formalAddY W
```

by explicitly constructing a quotient and proving

```lean
formalAddY W = (X 0 - X 1)^3 * formalAddYDiagQuot W
```

with `ring`/`ring_nf` after a small amount of diagonal normalization.

---

## Key point

The useful input is not that `w₀w₁` is coprime to `(X₀-X₁)^3`; the useful input is that the two specializations of the same one-variable series differ by `X₀-X₁`:

```lean
w₀ - w₁ = (X₀ - X₁) * w₀₁
```

for an explicit diagonal difference quotient `w₀₁`.

Once you rewrite

```lean
X₀ = X₁ + D
w₀ = w₁ + D * w₀₁
```

where

```lean
D := X₀ - X₁,
```

then the Mathlib `addY` polynomial becomes a finite polynomial expression in

```lean
D, X₁, w₁, w₀₁, a₁, a₂, a₃, a₄, a₆.
```

The desired theorem is then just a polynomial identity saying that this expression has a factor `D^3`.

This avoids all serious `MvPowerSeries` commutative algebra.

---

## Reusable helper 1: diagonal difference quotient

Add a general lemma for one-variable power series evaluated in the two variables.

Schematic API:

```lean
abbrev R (K : Type*) [Field K] := MvPowerSeries (Fin 2) K

noncomputable def X0 : R K := MvPowerSeries.X 0
noncomputable def X1 : R K := MvPowerSeries.X 1
noncomputable def D : R K := X0 - X1

noncomputable def at0 (f : PowerSeries K) : R K :=
  -- rename the one variable to `0 : Fin 2`
  MvPowerSeries.rename (fun _ : Unit => (0 : Fin 2)) f

noncomputable def at1 (f : PowerSeries K) : R K :=
  -- rename the one variable to `1 : Fin 2`
  MvPowerSeries.rename (fun _ : Unit => (1 : Fin 2)) f

noncomputable def diagDiffQuot (f : PowerSeries K) : R K :=
  -- coefficient at `X₀^i X₁^j` is `coeff f (i+j+1)`
  -- exact implementation depends on the local `PowerSeries`/`MvPowerSeries` API
  sorry

theorem at0_sub_at1_eq_D_mul_diagDiffQuot (f : PowerSeries K) :
    at0 f - at1 f = D * diagDiffQuot f := by
  ext m
  -- coefficient proof; split on `m 0` and `m 1`
  -- interior coefficients cancel, boundary coefficients give `f(X₀)-f(X₁)`
  simp [at0, at1, D, diagDiffQuot]
  omega
```

The formula behind `diagDiffQuot` is the standard identity

```text
f(X₀) - f(X₁)
  = (X₀ - X₁) * Σ_{i,j≥0} f_{i+j+1} X₀^i X₁^j.
```

This lemma is much easier than proving UFD facts about `MvPowerSeries`, and it is reusable everywhere a same-series diagonal difference appears.

For the current proof instantiate it with `f = formalW W`:

```lean
noncomputable def w0 : R K := at0 (formalW W)
noncomputable def w1 : R K := at1 (formalW W)
noncomputable def w01 : R K := diagDiffQuot (formalW W)

lemma w0_eq_w1_add_D_mul_w01 :
    w0 W = w1 W + D * w01 W := by
  have h := at0_sub_at1_eq_D_mul_diagDiffQuot (formalW W)
  -- `h : w0 - w1 = D * w01`
  rw [sub_eq_iff_eq_add] at h
  exact h
```

The proof should not need `formalU_eq` or the Weierstrass equation for `w`, unless the local definitions have hidden normalization rewrites.  The diagonal factor comes from the fact that `w₀` and `w₁` are the same series evaluated in two variables.

---

## Reusable helper 2: a pure algebra certificate for `addY`

Prove a lemma over an arbitrary commutative ring.  This keeps the hard `ring` proof away from the `MvPowerSeries` API.

The shape should be:

```lean
section AddYDiagonalCertificate

variable {A : Type*} [CommRing A]
variable (a₁ a₂ a₃ a₄ a₆ x z D dz : A)

/-- The quotient in the diagonal factorization of Mathlib's `Projective.addY`.
This should be generated once from the unfolded formula, or built by hand from the
same intermediate variables Mathlib uses in `addXYZ`. -/
def addYDiagQuotExpr : A :=
  -- explicit polynomial in `aᵢ x z D dz`
  -- obtained by polynomial division by `D^3`
  sorry

/-- Algebraic certificate: if the second point is obtained from the first by
`X ↦ X + D`, `Z ↦ Z + D*dz`, and the `Y` coordinate is unchanged, Mathlib's
addition `Y`-coordinate has a factor `D^3`. -/
lemma addY_diag_cube_certificate :
    addYExpr a₁ a₂ a₃ a₄ a₆
      (x + D) (-1) (z + D * dz)
      x       (-1) z
      = D^3 * addYDiagQuotExpr a₁ a₂ a₃ a₄ a₆ x z D dz := by
  unfold addYExpr addYDiagQuotExpr
  ring

end AddYDiagonalCertificate
```

Here `addYExpr` should be the unfolded expression of `Projective.addY` with coefficients exposed as variables.  If unfolding all of `Projective.addY` gives a large term, split the certificate along Mathlib's internal addXYZ helper variables.

The best decomposition is usually:

```lean
U := ...   -- line/slope numerator-like difference
V := ...   -- x/z denominator-like difference
```

then prove, after the diagonal rewrite,

```lean
U = D * Uq
V = D * Vq
```

and finally prove that every monomial of `addY` has total degree at least three in `U,V`, so

```lean
addY = D^3 * Q.
```

This keeps each `ring` goal small.  It also mirrors why `addXYZ(P,P)` gives the zero representative: the add formula is cubic in the basic difference quantities along the diagonal.

---

## Final instantiation in `MvPowerSeries`

After the two helpers, the actual theorem should be short.

Schematic final proof:

```lean
noncomputable def formalAddYDiagQuot (W : WeierstrassCurve K) : R K :=
  addYDiagQuotExpr
    W.a₁ W.a₂ W.a₃ W.a₄ W.a₆
    (X1 : R K)
    (w1 W)
    (D : R K)
    (w01 W)

theorem formalAddY_eq_D_cube_mul (W : WeierstrassCurve K) :
    formalAddY W = (D : R K)^3 * formalAddYDiagQuot W := by
  unfold formalAddY formalAddYDiagQuot
  -- rewrite the first point as a diagonal perturbation of the second
  have hx0 : (X0 : R K) = X1 + D := by
    simp [D, X0, X1]
    ring
  have hw0 : w0 W = w1 W + D * w01 W :=
    w0_eq_w1_add_D_mul_w01 W
  -- now the statement is exactly the pure algebra certificate
  rw [hx0, hw0]
  simpa using
    addY_diag_cube_certificate
      (A := R K)
      W.a₁ W.a₂ W.a₃ W.a₄ W.a₆
      (X1 : R K) (w1 W) (D : R K) (w01 W)

theorem D_cube_dvd_formalAddY (W : WeierstrassCurve K) :
    ((D : R K)^3) ∣ formalAddY W := by
  refine ⟨formalAddYDiagQuot W, ?_⟩
  exact formalAddY_eq_D_cube_mul W
```

The exact names will differ, but this is the proof architecture I would use.

---

## Why not use the `addZ * w₀w₁ = delta³` route?

That route asks Lean to prove something like:

```lean
IsCoprime ((X₀-X₁)^3) (w₀*w₁)
```

inside `MvPowerSeries (Fin 2) K`, then cancel a nonunit factor from a divisibility statement.  Mathematically:

```text
w₀*w₁ = X₀^3 X₁^3 u₀ u₁,
```

and `(X₀-X₁)` is coprime to `X₀X₁`, so the argument is sound.  But formalizing that requires a large amount of commutative algebra infrastructure:

- UFD or at least prime-element facts for `MvPowerSeries (Fin 2) K`;
- proof that `X₀`, `X₁`, and `X₀-X₁` have the expected prime/coprime behavior;
- transport through unit factors `u₀u₁`;
- cancellation from divisibility after multiplying by a coprime nonunit.

This is much more work than the direct factor certificate, and it proves the wrong coordinate unless you repeat a similar argument for `addY`.

So I would use the `delta` result only as a sanity check, not as the formal proof path for `formalAddY`.

---

## If the quotient is large

If `addYDiagQuotExpr` is too large to write by hand, generate it externally once from the unfolded polynomial formula:

1. introduce symbolic variables
   ```text
   a₁,a₂,a₃,a₄,a₆,x,z,D,dz;
   ```
2. substitute
   ```text
   X₀ = x + D,
   Y₀ = -1,
   Z₀ = z + D*dz,
   X₁ = x,
   Y₁ = -1,
   Z₁ = z;
   ```
3. expand Mathlib's `addY` formula;
4. divide by `D^3` in the polynomial ring;
5. paste the quotient as `addYDiagQuotExpr`;
6. verify in Lean with a single `ring` lemma over `[CommRing A]`.

That gives a certificate-style proof: no analytic derivatives, no coefficient-order API beyond the small `diagDiffQuot` lemma, and no UFD/coprimality in `MvPowerSeries`.

---

## Bottom line

Recommended route:

```text
same-series diagonal quotient lemma
        +
generic algebraic addY diagonal-cube certificate
        ⇒
formalAddY = (X₀-X₁)^3 * Q
        ⇒
(X₀-X₁)^3 ∣ formalAddY.
```

Avoid the nonunit cancellation route.  It is mathematically elegant but Lean-expensive, and it is unnecessary for the `formalAddY` divisibility theorem.
