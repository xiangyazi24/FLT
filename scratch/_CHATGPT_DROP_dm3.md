# Q227 (dm3): Can the projective formula induction avoid huge `addX`/`addY` expansions?

## Short verdict

Approach (c) is **mathematically right as a generic-point/function-field
argument**, but it is **not a direct Lean shortcut** for the exact polynomial
congruences

```text
addX(P, R_m) ≡ ψ_{m-1}² · φ_{m+1}  mod F_W
addY(P, R_m) ≡ ψ_{m-1}³ · ω_{m+1}  mod F_W.
```

The obstruction is not the group law; Mathlib has a solid Jacobian group-law
layer.  The obstruction is that the desired identities are **cleared-denominator
cone identities with a generally nonunit scalar** `ψ_{m-1}`.  Mathlib’s Jacobian
`PointClass` quotient identifies representatives only up to weighted scaling by a
**unit**.  In the coordinate ring, `ψ_{m-1}` is not a unit.  Therefore projective
uniqueness in Mathlib does not directly imply the three coordinate identities you
want.

So the answer is:

* (a) `mk_ψ`, `mk_φ`, `mk_Ψ_sq` help with the division-polynomial side, especially
  the X-coordinate identity defining `φ_n`, but they do not by themselves prove
  the `addX` formula identity.
* (b) Mathlib does have the Jacobian group-law connection to affine addition, but
  it goes through `W.add`, `addMap`, and `Point.add`, not bare `addXYZ` in all
  cases.
* (c) The conceptual argument is valid over the fraction field/generic point after
  proving several extra infrastructure lemmas.  It does not currently bypass the
  need for either a polynomial certificate or a new “cleared weighted multiple”
  theorem.

For the current project, I would not bet the induction on avoiding all polynomial
identities.  The pragmatic route is a **hybrid**: use Mathlib coordinate-ring
lemmas to normalize the division-polynomial side, then prove only the remaining
`addX/addY` congruences by generated certificates or carefully factored local
identities.

---

## What Mathlib already gives

The relevant existing Mathlib layers are real and useful.

### Coordinate-ring division-polynomial facts

Mathlib has the coordinate-ring comparison lemmas:

```lean
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
```

Their content is essentially:

```lean
mk W (W.ψ n) = mk W (W.Ψ n)
mk W (W.φ n) = mk W (Polynomial.C (W.Φ n))
mk W (W.Ψ n) ^ 2 = mk W (Polynomial.C (W.ΨSq n))
```

and Mathlib’s univariate `Φ` definition is already the expected formula

```lean
W.Φ n = X * W.ΨSq n
  - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq
```

Thus, for the X-coordinate RHS, `mk_φ` is exactly the existing theorem that says
the bivariate `φ_n = X ψ_n² - ψ_{n+1} ψ_{n-1}` agrees modulo the curve relation
with the univariate `Φ_n` package.

This is genuinely useful.  It means you should not expand the RHS from scratch.
Use `mk_φ`, `mk_ψ`, and `mk_Ψ_sq` to move between the bivariate and univariate
versions.

But these lemmas say nothing about the large Jacobian `addX` polynomial applied to
`P` and `R_m`.  The missing theorem would have to connect

```lean
mk W (some bivariate encoding of Jacobian.addX P R_m)
```

to the coordinate ring class of the x-coordinate of `P + R_m`.  Mathlib’s group
law proves this semantically over fields, but not as a universal coordinate-ring
polynomial congruence in the form needed here.

### Jacobian point and group-law facts

Mathlib’s Jacobian point files are also relevant:

```lean
#check WeierstrassCurve.Jacobian.addMap_eq
#check WeierstrassCurve.Jacobian.Point.add_point
#check WeierstrassCurve.Jacobian.Point.toAffineLift_add
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
#check WeierstrassCurve.Jacobian.map_add
```

The important facts are:

```lean
-- point-class addition is represented by `W.add P Q`
lemma WeierstrassCurve.Jacobian.addMap_eq
    (P Q : Fin 3 → R) :
    W.addMap ⟦P⟧ ⟦Q⟧ = ⟦W.add P Q⟧ := rfl

-- nonsingular Jacobian points form an additive group
lemma WeierstrassCurve.Jacobian.Point.add_point
    (P Q : W.Point) :
    (P + Q).point = W.addMap P.point Q.point := rfl

-- the Jacobian group law agrees with affine addition
lemma WeierstrassCurve.Jacobian.Point.toAffineLift_add
    [DecidableEq F] (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift

-- in fact there is an additive equivalence to affine nonsingular points
noncomputable def WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
    [DecidableEq F] : W.Point ≃+ W.toAffine.Point
```

So, yes: Mathlib has the theorem that the Jacobian group law represents the
ordinary group law on nonsingular points over a field.

However, note the exact operation:

```lean
noncomputable def WeierstrassCurve.Jacobian.add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W.dblXYZ P else W.addXYZ P Q
```

The raw `addXYZ` branch is used only when the representatives are not equivalent.
For example Mathlib has lemmas of the shape

```lean
W.add_of_not_equiv h : W.add P Q = W.addXYZ P Q
W.add_of_equiv h     : W.add P Q = W.dblXYZ P
```

and the formula file explicitly documents `addX`/`negAddY` as the coordinates for
addition of **distinct** representatives; if the representatives are equal, those
raw polynomials degenerate rather than represent doubling.

That matters for induction.  If the formal step really uses `addXYZ(P, R_m)`, you
must either prove that the generic representatives are not equivalent, or handle
the equivalence/doubling cases separately.  The group-law API itself deliberately
uses `W.add`, not raw `W.addXYZ`, to cover all cases.

---

## Why approach (c) does not directly give the polynomial identities

The tempting argument is:

```text
R_m represents [m]P.
P represents [1]P.
addXYZ(P, R_m) represents [m+1]P.
R_{m+1} represents [m+1]P.
Therefore addXYZ(P, R_m) = λ · R_{m+1}.
The Z-coordinate gives λ = ψ_{m-1}.
Therefore X and Y coordinates follow.
```

This is mathematically suggestive, but in Lean it has three serious gaps.

### 1. Mathlib projective equivalence uses units

In Jacobian coordinates Mathlib’s equivalence relation is weighted scaling by a
unit:

```lean
P ≈ Q  means  ∃ u : Rˣ, P = u • Q
```

with

```lean
u • ![X,Y,Z] = ![u^2 * X, u^3 * Y, u * Z].
```

The desired scalar is

```lean
λ = ψ_{m-1},
```

which is usually **not** a unit in the coordinate ring.  Hence the desired
identity is not an equality in the Mathlib `PointClass` quotient.  It is a
stronger “cleared denominator” identity in the affine cone.

Over the function field, every nonzero `ψ_{m-1}` is a unit, so the projective
argument can work there.  But then you still need to descend the resulting
identity back to the coordinate ring and prove that no denominator was introduced
other than the known cleared factor.  That descent is extra algebra, not currently
provided by the point-class API.

### 2. The Z-coordinate does not determine a scalar in the coordinate ring

Even if you know two triples represent the same point over a field, equality of
Z-coordinates only determines the scalar when the relevant coordinate is nonzero.
For the generic point over a function field this is usually fine after proving
nonvanishing.  In the coordinate ring, however, you cannot simply divide by
`ψ_{m+1}` or treat `ψ_{m-1}` as invertible.

The statement you need is more like:

```lean
-- Schematic, not existing Mathlib.
theorem weighted_multiple_of_same_point_and_Z
    {A : Type*} [CommRing A] [IsDomain A]
    {P Q : Fin 3 → A} {λ : A}
    (hSameOverFrac : (mapToFrac P) ≈ (mapToFrac Q))
    (hZ : P 2 = λ * Q 2)
    (hQz_ne : Q 2 ≠ 0)
    (hNoDenoms : ... ) :
    P 0 = λ^2 * Q 0 ∧ P 1 = λ^3 * Q 1 ∧ P 2 = λ * Q 2
```

Mathlib does not appear to have this cleared, nonunit-scalar uniqueness theorem.
It would be a new project lemma.

### 3. `addXYZ` versus `add`

The semantic group-law theorem is about `W.add`, which branches between doubling
and distinct-point addition.  If your polynomial formula is written with raw
`addXYZ`, the bridge theorem must also include the non-equivalence condition
needed to rewrite

```lean
W.add P R_m = W.addXYZ P R_m.
```

For a genuine universal/generic point this may be true for `m ≠ 1`, but proving it
inside Lean is itself a nontrivial division-polynomial/non-torsion fact.  It is
not supplied automatically by `Point.toAffineAddEquiv`.

---

## What approach (c) can prove if upgraded

A rigorous conceptual route would be:

1. Work over the fraction field of the affine coordinate ring of the universal
   point.
2. Construct the generic nonsingular point

   ```lean
   Pgen : (W_generic⁄K).Jacobian.Point
   ```

   where `K` is the fraction field.
3. State the induction hypothesis as an equality of Jacobian point classes over
   `K`, not as a raw coordinate-ring equality.
4. Use Mathlib’s additive group law:

   ```lean
   (R_m_as_point : W.Point) + Pgen = R_{m+1}_as_point
   ```

   or the affine equivalent through `toAffineAddEquiv`.
5. Rewrite `Point.add_point` and `addMap_eq` to identify the representative with
   `W.add P R_m`.
6. If needed, prove the `not_equiv` condition to replace `W.add` by `W.addXYZ`.
7. Use the Z-coordinate to identify the scalar in `K` as `ψ_{m-1}`.
8. Prove a descent/clearing lemma to pull the resulting equalities from `K` back
   to the coordinate ring.

Schematic Lean shape:

```lean
-- Schematic only.  This is not a currently available one-liner.
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

/-- Generic-point semantic induction over the fraction field. -/
theorem generic_projective_rep_zsmul
    (W : WeierstrassCurve k) [W.IsElliptic]
    (m : ℤ) :
    -- R_m represents m • Pgen as a Jacobian point over the function field.
    True := by
  -- Use Jacobian.Point.toAffineAddEquiv and the division-polynomial
  -- coordinate-ring theorems here.
  trivial

/-- New infrastructure that Mathlib does not currently give directly. -/
theorem cleared_weighted_coords_of_same_point_over_fraction_field
    {A : Type*} [CommRing A] [IsDomain A]
    {P Q : Fin 3 → A} {λ : A}
    (hSame : True)       -- mapped triples are equivalent over FractionRing A
    (hZ : P 2 = λ * Q 2)
    (hQz : Q 2 ≠ 0)
    (hden : True) :
    P 0 = λ ^ 2 * Q 0 ∧ P 1 = λ ^ 3 * Q 1 ∧ P 2 = λ * Q 2 := by
  -- This is the hard new descent lemma.
  -- It is not merely `Quotient.sound`, because `λ` is not a unit in `A`.
  sorry

end WeierstrassCurve
```

This route is conceptually elegant, but it is not a small patch.  It replaces one
large polynomial identity with several substantial algebraic-geometry / fraction
field / denominator-control lemmas.

---

## Recommended project strategy

For the current induction, I recommend the following hybrid plan.

### Step 1: Use Mathlib’s coordinate-ring division-polynomial lemmas aggressively

Do not expand the RHS by hand.  For X, normalize through

```lean
Affine.CoordinateRing.mk_φ
Affine.CoordinateRing.mk_ψ
Affine.CoordinateRing.mk_Ψ_sq
```

so that the RHS is recognized as the known `φ_{m+1}` / `Φ_{m+1}` coordinate.

For Y, if the project already has an `ω_n` package, prove the analogue once:

```lean
-- schematic name
Affine.CoordinateRing.mk_ω (n : ℤ) :
  mk W (W.omega n) = mk W (some bivariate y-division expression n)
```

Then use that theorem the same way.  If there is no `mk_ω` theorem yet, the Y
component will remain the harder side.

### Step 2: Prove only the `addX/addY` bridge by certificate

The residual identities should be formulated as coordinate-ring zero statements:

```lean
-- schematic
theorem mk_addX_Rm_eq
    (W : WeierstrassCurve k) (m : ℤ) :
    mk W (addX_polynomial_for P Rm
      - ψ_{m-1}^2 * φ_{m+1}) = 0 := by
  -- generated linear_combination / certificate modulo F_W
  ...

theorem mk_addY_Rm_eq
    (W : WeierstrassCurve k) (m : ℤ) :
    mk W (addY_polynomial_for P Rm
      - ψ_{m-1}^3 * ω_{m+1}) = 0 := by
  -- generated linear_combination / certificate modulo F_W
  ...
```

This still uses polynomial certificates, but the certificates should be smaller
than a blind expansion because the division-polynomial side has already been
normalized by existing Mathlib facts.

### Step 3: Consider the function-field route only as a later cleanup

The function-field proof is a good long-term theorem.  It would establish that the
large formulas are not arbitrary CAS miracles.  But it is not the fastest way to
finish the induction brick unless you already have:

```lean
FractionRing (Affine.CoordinateRing W)
injective map from coordinate ring to fraction field
nonsingularity of the generic point
nonvanishing of the relevant ψ factors in the fraction field
not-equivalence of P and R_m when replacing W.add by W.addXYZ
cleared-weighted-multiple descent back to the coordinate ring
```

Absent that infrastructure, generated congruence certificates remain the lower
risk path.

---

## Direct answers to the subquestions

### (a) Can `mk_ψ`, `mk_φ`, `mk_Ψ_sq` deduce the X component?

They can deduce the **division-polynomial identity part** of the X component:
`φ_n` agrees with `Φ_n` in the coordinate ring.  They cannot by themselves deduce
that the explicit `addX(P,R_m)` polynomial is that coordinate.  You still need an
`addX` bridge theorem or a certificate for the difference.

### (b) Does Mathlib connect `Jacobian.addXYZ` to `Affine.Point.add`?

Mathlib connects the **Jacobian group operation** to affine addition.  The main
route is:

```lean
Jacobian.add        -- branches: dblXYZ if equivalent, addXYZ otherwise
Jacobian.addMap     -- quotient-level point-class addition
Jacobian.Point.add  -- nonsingular Jacobian point addition
Jacobian.Point.toAffineLift_add
Jacobian.Point.toAffineAddEquiv
```

So yes for `W.add` / `Point.add`; be careful for bare `addXYZ`, which requires the
non-equivalence branch.

### (c) Is the uniqueness/scalar argument valid?

Valid over the fraction field, after proving nonzero denominators.  Not directly
valid in the coordinate ring or in Mathlib’s `PointClass`, because the scalar
`ψ_{m-1}` is not a unit.  Also, Z-coordinate uniqueness requires nonvanishing or a
domain/fraction-field argument.

Therefore approach (c) is a good conceptual guide, but not currently a drop-in
Lean proof that bypasses the massive identities.

---

## Bottom line

Use Mathlib’s group-law API to guide and sanity-check the formulas, but do not
expect it to replace the polynomial congruence proof without significant new
infrastructure.  The shortest path for this project is:

```text
mk_ψ/mk_φ/mk_Ψ_sq to normalize division-polynomial expressions
+ generated modulo-F_W certificates for the remaining addX/addY bridge
+ optional later function-field theorem as a conceptual refactor.
```

The reason is precise: Mathlib has uniqueness of projective representatives only
up to **unit** weighted scaling, while the induction identities are exactly about
cleared denominators with scalar `ψ_{m-1}`, a generally **nonunit** element of the
coordinate ring.
