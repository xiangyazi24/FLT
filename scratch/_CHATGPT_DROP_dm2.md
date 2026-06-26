# Q762 (dm2): invariant differential, division polynomials, and separability of `preΨ' n`

## Executive answer

Mathlib has **some** of the ingredients, but not the invariant-differential proof as a packaged theorem.

What I found in Mathlib:

* `WeierstrassCurve` and its affine/projective point group laws exist.
  In particular, Mathlib has nonsingular affine/projective point types and `AddCommGroup` instances for them over fields.
* The affine coordinate ring exists as

```lean
WeierstrassCurve.Affine.CoordinateRing W
```

with function field

```lean
WeierstrassCurve.Affine.FunctionField W
```

* Division-polynomial infrastructure exists in

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
```

It defines:

```lean
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

and proves coordinate-ring congruences such as:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

It also has map/base-change lemmas:

```lean
map_preΨ'
map_preΨ
map_ΨSq
map_Ψ
map_Φ
map_ψ
map_φ

baseChange_preΨ'
baseChange_preΨ
baseChange_ΨSq
baseChange_Ψ
baseChange_Φ
baseChange_ψ
baseChange_φ
```

But Mathlib’s division-polynomial file explicitly still has:

```lean
* TODO: the bivariate polynomials `ωₙ`.
```

So the `y`-coordinate numerator `ωₙ`/`Ωₙ` is not currently formalized there.

What I did **not** find as existing packaged Mathlib API:

1. an elliptic-curve-specific definition of the invariant differential

```text
ω = dx / (2y + a₁x + a₃)
```

2. a theorem

```text
[n]^*ω = n • ω
```

3. a theorem connecting the Mathlib division polynomials to the actual multiplication-by-`n` map in the form

```text
[n](P) = (φₙ(P) / ψₙ(P)^2, ωₙ(P) / ψₙ(P)^3)
```

or projectively

```text
[n](P) = [φₙ(P)ψₙ(P) : ωₙ(P) : ψₙ(P)^3].
```

Mathlib does have general Kähler differentials in `Mathlib.RingTheory.Kaehler.Basic`, so one does **not** need to build differentials from zero.  But the elliptic-curve-specific invariant differential and its compatibility with multiplication are not there as far as I found.

---

## Can the chain-rule proof be done without scheme theory?

Yes.  You do **not** need schemes for this proof.  You can do it as pure commutative algebra in the affine coordinate ring, its fraction field, and modules of Kähler differentials.

But it is not just a one-variable polynomial derivative proof.  The clean algebraic replacement for scheme theory is:

```lean
A := W.toAffine.CoordinateRing
L := W.toAffine.FunctionField
Ω := KaehlerDifferential K A
```

or, after moving to the function field,

```lean
ΩL := KaehlerDifferential K L
```

Then prove the relevant rational-function identities in `L` and their differential identities in `ΩL`.

The most robust version uses the projective local parameter at infinity

```text
t = -X / Y
```

rather than differentiating only the affine `x`-coordinate.  This avoids annoying characteristic `2` issues caused by the derivative of the denominator `ψₙ²`.

Projectively, the multiplication-by-`n` formula should be stated as

```text
[n](P) = [φₙ(P) ψₙ(P) : ωₙ(P) : ψₙ(P)^3].
```

Then near a nonzero `n`-torsion point where `ψₙ(P) = 0`, one has

```text
t([n]P) = - φₙ(P) ψₙ(P) / ωₙ(P).
```

At such a point, `φₙ(P)` and `ωₙ(P)` are nonzero, so differentiating gives

```text
d(t ∘ [n]) = nonzero_scalar * dψₙ.
```

On the other hand, the invariant differential identity `[n]^*ω = nω`, together with `(n : K) ≠ 0`, says that `d(t ∘ [n])` is nonzero at the point.  Therefore `dψₙ` is nonzero at the point, so the zero of `ψₙ` is simple.

Finally, away from `2`-torsion, Mathlib’s univariate `preΨ' n` is exactly the `x`-part of `ψₙ`:

```text
ψₙ = preΨₙ        if n is odd,
ψₙ = preΨₙ ψ₂    if n is even.
```

At a non-2-torsion point, `ψ₂(P) ≠ 0`, so simplicity of `ψₙ` implies simplicity of `preΨₙ(x)`.

Thus the proof can be done entirely using:

* coordinate rings,
* localizations/fraction fields,
* Kähler differentials or equivalent derivations,
* explicit rational identities for division polynomials.

No schemes are required.

---

## Minimal formalization needed

Here is the minimal stack I would build.  I would **not** start by formalizing global regular differentials on schemes.

### 1. Coordinate-ring notation

Use the existing affine coordinate ring:

```lean
namespace WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

local notation "A" => W.toAffine.CoordinateRing

noncomputable abbrev Xbar : A :=
  mk W.toAffine (Polynomial.C Polynomial.X)

noncomputable abbrev Ybar : A :=
  mk W.toAffine Polynomial.X

noncomputable abbrev dYDen : A :=
  2 * Ybar W + W.a₁ • Xbar W + algebraMap K A W.a₃

end WeierstrassCurve.Affine.CoordinateRing
```

The exact expression for `Xbar`/`Ybar` will depend on the local open namespaces and bivariate-polynomial notation, but the conceptual target is:

```text
Xbar = class of X in K[X,Y]/(F)
Ybar = class of Y in K[X,Y]/(F)
D    = 2Ybar + a₁Xbar + a₃.
```

You already get the coordinate ring and its function field from Mathlib.

### 2. A local/birational invariant differential, not a scheme differential

Define the invariant differential as an element of a localized Kähler differential module, or as a pair consisting of a denominator and a numerator:

```lean
-- conceptual shape, not exact API
noncomputable def invDifferential :
    Localization.AtPrime ... :=
  d Xbar / (2 * Ybar + C W.a₁ * Xbar + C W.a₃)
```

A more Lean-friendly first version is to avoid division in the definition and state identities after clearing denominators:

```text
D • ω = dX,
where D = 2Y + a₁X + a₃.
```

At a non-2-torsion affine point, `D(P) ≠ 0`, so this is equivalent to the usual formula.

### 3. The missing `ωₙ`/`Ωₙ` division polynomial

This is the largest missing Mathlib ingredient.  Mathlib already defines `ψ` and `φ`, and says `ωₙ` is TODO.  You need a bivariate polynomial, say:

```lean
protected noncomputable def ω (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] := ...
```

or use `Ω` to avoid collision with the invariant differential.

The required theorem is the projective coordinate theorem:

```lean
theorem nsmul_projective_eq_division_polynomials
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℤ) (P : W.toProjective.Point) :
    -- conceptual statement:
    n • P = [φₙ(P) ψₙ(P) : ωₙ(P) : ψₙ(P)^3]
```

You do not need this for all points immediately.  For separability, it is enough to prove the local consequence:

```lean
theorem nsmul_eq_zero_of_ψ_eq_zero
    (hψ : eval P (W.ψ n) = 0)
    (hω : eval P (W.ω n) ≠ 0) :
    n • P = 0
```

and the local parameter formula:

```lean
t([n]P) = - φₙ(P) * ψₙ(P) / ωₙ(P).
```

### 4. Pullback identity in a purely algebraic form

Instead of formalizing global pullback of differentials on schemes, prove the following in the function field or in a localized coordinate ring:

```text
[n]^*(ω_inv) = n • ω_inv.
```

For the separability argument, the version you actually use is even smaller:

```text
d(t ∘ [n]) is nonzero at P whenever (n : K) ≠ 0 and P is nonsingular.
```

A practical Lean target is:

```lean
theorem d_localParameter_nsmul_ne_zero
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℤ} (hn : (n : K) ≠ 0)
    {P : W.toAffine.Point}
    (hP_non2 : eval P W.ψ₂ ≠ 0) :
    -- conceptual:
    evalDifferential P (d (localParameterAtInfinity ∘ nsmulMap n)) ≠ 0
```

This theorem can be proved from `[n]^*ω = nω`, but for the first implementation it may be easier to prove it directly from the formal group law at the identity plus translation invariance.

### 5. Reduce `ψₙ` simplicity to `preΨ' n` simplicity

This is the part closest to existing Mathlib.

For odd `n`:

```text
ψₙ = C(preΨₙ),
```

so at `P = (x,y)`:

```text
dψₙ(P) = preΨₙ.derivative.eval x • dX(P).
```

For even `n`:

```text
ψₙ = C(preΨₙ) * ψ₂.
```

At a non-2-torsion point, `ψ₂(P) ≠ 0`, and if `preΨₙ(x)=0`, then

```text
dψₙ(P) = ψ₂(P) * preΨₙ.derivative.eval x • dX(P).
```

Thus:

```lean
theorem derivative_preΨ'_ne_zero_of_dψ_ne_zero
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hroot : (W.preΨ' n).eval x = 0)
    (hψ₂ : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hdψ : differential_of_ψ_at_point_ne_zero W n x y) :
    (W.preΨ' n).derivative.eval x ≠ 0 := by
  -- odd/even split using `W.Ψ_ofNat` / `W.ψ` definitions and product rule
  sorry
```

Then separability is the standard polynomial criterion over a field:

```lean
theorem separable_preΨ'
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- use `Polynomial.separable_iff` / gcd with derivative,
  -- or root criterion over splitting fields
  sorry
```

---

## Why I would not try to prove this directly from `preΨ'` recurrences

The recurrence definitions in Mathlib are excellent for degree and leading-coefficient computations.  They are much less pleasant for separability.

A recurrence-only separability proof would require a large EDS-style coprimality theory proving that common roots of `preΨₙ` and `(preΨₙ)'` cannot occur when `(n : K) ≠ 0`.  That is possible, but it essentially reproves the reducedness of the `n`-torsion subgroup in a disguised form.

The invariant-differential proof is conceptually shorter, but it requires the missing bridge between:

```text
abstract group law / multiplication-by-n
```

and

```text
explicit division-polynomial coordinates.
```

That bridge is currently the main missing formalization.

---

## Recommended implementation path

I would implement this in the following order.

### Step A: Add `ωₙ` / `Ωₙ`

Extend `DivisionPolynomial.Basic` locally with the missing y-coordinate numerator:

```lean
protected noncomputable def Ω (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] := ...
```

Prove map/base-change lemmas, matching the existing style:

```lean
@[simp] lemma map_Ω (f : R →+* S) (n : ℤ) :
    (W.map f).Ω n = (W.Ω n).map (mapRingHom f) := by
  ...

lemma baseChange_Ω ... := by
  rw [← map_Ω, map_baseChange]
```

### Step B: Prove projective coordinate formula for multiplication

Target:

```text
[n]P = [φₙψₙ : Ωₙ : ψₙ³].
```

This can be proved by induction on `n` using Mathlib’s projective `addXYZ`, `dblXYZ`, and the existing division-polynomial recurrences.  This is computational but finite and does not involve schemes.

### Step C: Define the local parameter `t = -X/Y` and prove the key differential identity

At the identity, use projective coordinates and define:

```text
t = -X/Y.
```

From the coordinate formula:

```text
t ∘ [n] = - φₙ ψₙ / Ωₙ.
```

At a point with `ψₙ(P)=0` and `Ωₙ(P)≠0`, the derivative is:

```text
d(t ∘ [n])_P = -φₙ(P)/Ωₙ(P) • dψₙ(P).
```

### Step D: Prove `[n]^*ω = nω`, or only the nonvanishing consequence

Full theorem:

```lean
theorem pullback_invariantDifferential_nsmul
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℤ) :
    pullback (nsmulMap W n) (invDifferential W)
      = n • invDifferential W := by
  ...
```

Minimal theorem for separability:

```lean
theorem d_localParameter_nsmul_ne_zero_at_torsion
    (hn : (n : K) ≠ 0) ... :
    d(t ∘ [n]) at P ≠ 0 := by
  -- follows from `[n]^*ω = nω`, or from formal group linear coefficient
  ...
```

### Step E: Convert `dψₙ ≠ 0` to `(preΨ' n).derivative x ≠ 0`

Use odd/even cases:

```text
ψₙ = preΨₙ              if n odd,
ψₙ = preΨₙ * ψ₂         if n even.
```

At non-2-torsion roots, `ψ₂(P) ≠ 0`, so `dψₙ ≠ 0` implies `d(preΨₙ(X)) ≠ 0`, hence the ordinary univariate derivative does not vanish at `x`.

---

## Bottom line

Mathlib currently has the Weierstrass curve, affine/projective group law, coordinate ring, function field, and most of the division-polynomial objects (`preΨ`, `Ψ`, `Φ`, `ψ`, `φ`).  It does **not** appear to have the invariant differential, the theorem `[n]^*ω = nω`, the missing `ωₙ` y-coordinate division polynomial, or the theorem identifying division-polynomial coordinates with multiplication-by-`n`.

The chain-rule proof can absolutely be done without schemes, but it should be done in coordinate rings/function fields with Kähler differentials, not as a bare polynomial recurrence argument.  The most robust polynomial-level route is to use the projective local parameter

```text
t = -X/Y
```

and the coordinate formula

```text
t ∘ [n] = -φₙψₙ/ωₙ.
```

Then `[n]^*ω = nω` gives nonvanishing of `d(t ∘ [n])`, which gives nonvanishing of `dψₙ`, and finally nonvanishing of `(preΨ' n).derivative` at every root away from `2`-torsion.  That proves separability of `preΨ' n` when `(n : K) ≠ 0`.
