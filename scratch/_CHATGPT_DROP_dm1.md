# Q176 (dm1): first-order jet architecture — definition review

## Executive verdict

Use the existing `TangentO` scalar API directly.  Do **not** introduce an `OJetPoint` wrapper unless you need it to carry proof data about a projective dual-number point reducing to `O`.  If `TangentO` is already morally `K` and you already have

```lean
TangentO.nsmul₁ W n 1
TangentO.nsmul₁_eq_natCast_mul
```

then that is the correct target for the first-order statement.  A wrapper

```lean
structure OJetPoint where coeff : K
```

only creates coercion/projection overhead unless it packages actual coordinates/proofs.

The sharper architecture is:

```text
input dual deformation at P
  ⟶ scalar in T_O E, computed as dx / ψ₂(P)
  ⟶ [n] sends this scalar to (n : K) * dx / ψ₂(P)
```

For your special deformation `dx = 1`, this scalar is nonzero because `ψ₂(P) = 2y + a₁x + a₃` is a unit/nonzero at a non-2-torsion point.

The critical bridge should not be phrased as “translation by `-P` produces an `OJetPoint`” unless you want a reusable dual-number group law.  Instead, phrase the bridge as the **combined differential statement**:

```text
local-parameter coefficient of [n](Pε) at O
  = (n : K) * (dx / ψ₂(P)).
```

Then the division-polynomial dual-root condition says the left-hand side is zero.  Since `(n : K) ≠ 0` and `dx / ψ₂(P) ≠ 0`, contradiction.

The precise derivative connection is not an isolated identity

```text
(preΨ'_n)'(x) = tangent([n])
```

by itself.  The correct identity passes through the **projective local parameter at `O`**:

```text
t = -X/Y,
```

and the homogeneous division-polynomial formula for `[n]`.  Schematically,

```text
t([n]Pε) = - X_n(Pε) / Y_n(Pε)
         = - Φ_n(Pε) * Ψ_n(Pε) / Ω_n(Pε),
```

so at an `n`-torsion point with `Ψ_n(P)=0` and `Ω_n(P)≠0`, the first-order coefficient is a unit multiple of `dΨ_n(Pε)`, hence a unit multiple of `(preΨ'_n)'(x) * dx` after the `ψ₂` unit is removed.  That is the exact mathematical chain.

Therefore, route (d) using the affine quotient

```text
x([n]P) = φ_n / ΨSq_n
```

is not the right chart: `x` has a pole at `O`.  The correct “bypass translation” route is possible, but it uses the **projective local parameter** and requires the missing `Ω_n`/projective division-polynomial bridge.  `mk_φ` and `mk_Ψ_sq` alone are not enough.

---

## (a) Definition check: `OJetPoint` vs `TangentO`

### Recommendation

Do not define

```lean
abbrev FormalJetAtO := K
structure OJetPoint where coeff : K
```

as a new object if `TangentO` already does the same job.  The Lean theorem you want is scalar-valued:

```lean
(n : K) * tangentCoeff = 0
```

not object-valued:

```lean
OJetPoint.nsmul = 0.
```

If your existing API proves

```lean
TangentO.nsmul₁_eq_natCast_mul W n v
```

or in the special input direction

```lean
TangentO.nsmul₁ W n 1 = (n : K)
```

then it already serves as the `OJetPoint.nsmul` theorem.

### Suggested interface

Use scalar functions, not wrappers:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The invariant-differential scalar of a tangent vector `(dx,dy)` at a finite point `(x,y)`.
For a non-2-torsion point this is well-defined because `ψ₂(P)=2y+a₁x+a₃ ≠ 0`. -/
def tangentScalarAtAffine
    (x y dx : K) : K :=
  dx / W.toAffine.polynomialY.evalEval x y

/-- For the specific deformation `x + ε`, the scalar is the inverse of `ψ₂(P)`. -/
lemma tangentScalarAtAffine_one_ne_zero
    {x y : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    tangentScalarAtAffine W x y 1 ≠ 0 := by
  unfold tangentScalarAtAffine
  exact div_ne_zero one_ne_zero hY

/-- This is the scalar theorem that replaces `OJetPoint.nsmul`. -/
lemma tangent_nsmul_scalar
    (n : ℕ) (v : K) :
    (n : K) * v = (n : K) * v := rfl

end

end WeierstrassCurve
```

In your actual code, replace `tangent_nsmul_scalar` by the existing

```lean
TangentO.nsmul₁_eq_natCast_mul
```

or make a tiny wrapper lemma around it.  The point is: the separability proof needs only the scalar value, so keep the API scalar.

### When a wrapper is justified

A wrapper is justified only if it carries extra data:

```lean
structure OJetPoint (W : WeierstrassCurve K) where
  coeff : K
  coords : ProjectiveDualPoint W
  reduces_to_O : ...
  coeff_eq_local_parameter : ...
```

That is a different object.  A bare wrapper around `K` is not worth it.

---

## (b) What is `translateToOJet` explicitly?

Mathematically, the differential of translation by `-P` identifies `T_P E` with `T_O E`.  Under the standard local parameter at `O`, this identification is measured by the invariant differential

```text
ω = dx / (2y + a₁x + a₃).
```

So for a tangent vector `(dx,dy)` at `P=(x,y)`, the translated tangent coefficient at `O` is

```text
translateToOJetCoeff(P; dx,dy) = dx / (2y + a₁x + a₃).
```

Up to a possible global sign depending on whether your local parameter is `t = -X/Y` or `t = X/Y`, this is the formula.  Choose the sign once and then make `TangentO` use the same convention.  The sign is irrelevant for nonvanishing, but it matters for exact coefficient equalities.

### Why this formula is right

Let

```text
ψ₂(P) = 2y + a₁x + a₃.
```

The tangent equation is

```text
F_X(P) * dx + F_Y(P) * dy = 0,
```

where

```text
F_Y(P) = ψ₂(P).
```

The invariant differential evaluates on the tangent vector as

```text
ω_P(dx,dy) = dx / ψ₂(P).
```

At `O`, the local parameter `t = -X/Y` satisfies

```text
ω = dt + higher-order terms,
```

so the first-order `t`-coefficient of the translated tangent is exactly `ω_P(dx,dy)`.

### Do you need both translation and `[n]`?

Conceptually yes:

```text
T_P E --dτ_{-P}--> T_O E --d[n]_O--> T_O E.
```

But in Lean you should avoid materializing both maps unless needed.  State the combined theorem:

```lean
/-- Differential of multiplication by `n` at a finite point, expressed in the invariant
local parameter at `O`. -/
theorem nsmul_tangentCoeffAtAffine
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y dx dy : K}
    (hP : W.Equation x y)
    (htan : /* tangent equation for `(dx,dy)` at `(x,y)` */ True) :
    /* local t-coefficient of `[n]` applied to the dual deformation */
      = (n : K) * (dx / W.toAffine.polynomialY.evalEval x y) := by
  -- Prove by translation-invariance of the first-order group law, or by projective formulas.
  sorry
```

This combined theorem is the one the separability proof needs.  You can later refactor it into separate `translateToOJet` and `TangentO.nsmul₁` lemmas if useful.

---

## (c) The precise chain from `(preΨ'_n)'(x)=0` to zero tangent image

Here is the exact mathematical chain.  I will write `P=(x,y)` and `Pε=(x+ε dx, y+ε dy)`.

### Step C1: dual evaluation gives root plus derivative root

Your `eval_dualNumber` gives

```text
preΨ'_n(x + ε dx)
  = preΨ'_n(x) + ε * dx * (preΨ'_n)'(x).
```

For `dx = 1`,

```text
preΨ'_n(x + ε) = 0
```

is equivalent to

```text
preΨ'_n(x) = 0
(preΨ'_n)'(x) = 0.
```

Lean shape:

```lean
lemma preΨ'_dual_root_iff_root_and_deriv
    {n : ℕ} {x dx : K} :
    aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0
      ↔ (W.preΨ' n).eval x = 0 ∧ (derivative (W.preΨ' n)).eval x = 0 := by
  -- Use `eval_dualNumber` with `dx = 1`, then ext on `TrivSqZeroExt.fst/snd`.
  sorry
```

### Step C2: reduced `preΨ'` zero equals full `Ψ_n` zero at non-2-torsion dual points

For the dual point, `ψ₂(Pε)` is a unit by your

```lean
psi2_dual_isUnit
```

Thus the reduced polynomial zero is equivalent to the full division polynomial zero:

```text
preΨ'_n(xε) = 0
  ⇔ Ψ_n(Pε) = 0.
```

For odd `n`, this is immediate.  For even `n`, `Ψ_n = preΨ'_n * ψ₂` or the corresponding reduced/full factor, and `ψ₂(Pε)` is a unit.

Lean target:

```lean
lemma Ψ_dual_eq_zero_iff_preΨ'_dual_eq_zero_of_psi2_unit
    {n : ℕ} {x y s : K}
    (hunit : IsUnit (/* ψ₂ evaluated at `(xε,yε)` */)) :
    (/* full Ψ_n evaluated at `(xε,yε)` */ = 0)
      ↔ aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0 := by
  -- Split on parity of n; for the even branch cancel the ψ₂ unit.
  sorry
```

### Step C3: projective division-polynomial formula sends `Ψ_n=0` to `O`

This is the first truly missing bridge.  You need a projective formula for multiplication by `n` over dual numbers:

```text
[n](X:Y:Z) = [X_n : Y_n : Z_n]
```

with, in affine input coordinates, the usual shape

```text
X_n = φ_n * Ψ_n,
Y_n = Ω_n,
Z_n = Ψ_n^3
```

or an equivalent homogeneous normalization.  Then `Ψ_n(Pε)=0` implies

```text
X_n(Pε)=0,
Z_n(Pε)=0,
Y_n(Pε)=Ω_n(Pε) is a unit,
```

so

```text
[n](Pε) = O
```

as a dual-number point.

Lean target:

```lean
/-- Projective division-polynomial formula over dual numbers. -/
theorem nsmul_dual_eq_O_of_Ψ_dual_eq_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y dx dy : K}
    (hPε : /* `(x+εdx,y+εdy)` lies on W over dual numbers */)
    (hNon2 : IsUnit (/* ψ₂(Pε) */))
    (hΨ : /* full Ψ_n(Pε) */ = 0) :
    /* `[n](Pε) = O` over TrivSqZeroExt K K */ := by
  -- Needs projective/homogeneous division-polynomial formula, including Ω_n.
  sorry
```

This theorem is the exact bridge between preΨ dual vanishing and zero tangent image.

### Step C4: zero image means zero local-parameter coefficient

If `[n](Pε)=O` exactly, then its first-order local parameter coefficient is zero:

```lean
lemma tangentCoeffAtO_eq_zero_of_dual_nsmul_eq_O
    (h : /* `[n](Pε)=O` */) :
    /* local t-coefficient of `[n](Pε)` */ = 0 := by
  -- by definition of the local parameter coefficient at O
  sorry
```

### Step C5: differential of `[n]` says the same coefficient is `(n : K) * dx / ψ₂(P)`

This is the first-order formal-group theorem in the scalar API:

```lean
lemma tangentCoeff_nsmul_dual
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y dx dy : K}
    (hP : W.Equation x y)
    (hPε : /* dual lift */)
    (hNon2 : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    /* local t-coefficient of `[n](Pε)` */
      = (n : K) * (dx / W.toAffine.polynomialY.evalEval x y) := by
  -- This is where your existing `TangentO.nsmul₁_eq_natCast_mul` should be used.
  -- The input tangent scalar is `dx / ψ₂(P)`.
  sorry
```

Combining C4 and C5 gives

```text
(n : K) * dx / ψ₂(P) = 0.
```

For `dx = 1`, `(n : K) ≠ 0`, and `ψ₂(P) ≠ 0`, contradiction.

### The direct identity relating derivative to tangent

If you want an explicit identity, it is this local-parameter formula, not an affine-`x` formula:

```text
localCoeff_t([n]Pε)
  = unit_n(P) * dx * (preΨ'_n)'(x)
```

where, up to normalization,

```text
unit_n(P) = - Φ_n(P) * ψ₂(P)^parity / Ω_n(P).
```

More explicitly, from projective division polynomials,

```text
t([n]Pε) = - X_n(Pε) / Y_n(Pε)
         = - Φ_n(Pε) * Ψ_n(Pε) / Ω_n(Pε).
```

At an `n`-torsion non-2-torsion point, `Ψ_n(P)=0` and `Ω_n(P)≠0`, so the first-order coefficient is

```text
coeffε(t([n]Pε))
  = - Φ_n(P) / Ω_n(P) * coeffε(Ψ_n(Pε)).
```

For odd `n`,

```text
coeffε(Ψ_n(Pε)) = dx * (preΨ'_n)'(x).
```

For even `n`, the full `Ψ_n` has an extra `ψ₂` factor, and because `ψ₂(P)` is a unit,

```text
coeffε(Ψ_n(Pε)) = ψ₂(P) * dx * (preΨ'_n)'(x)
```

up to the precise normalization in your `Ψ` definition.  Thus

```text
coeffε(t([n]Pε))
  = unit * dx * (preΨ'_n)'(x).
```

This is the precise bridge from derivative to tangent.  Proving the unit facts requires the same projective formula and the nonzero `Ω_n(P)` fact at the torsion point.

---

## (d) Can we bypass translation by differentiating `φ_n / ΨSq_n`?

Verdict: **not in affine `x`; it is the wrong coordinate and leads back to circularity.**

At a root of `Ψ_n`, `[n]P = O`, and affine `x` has a pole at `O`.  The quotient

```text
x([n]P) = φ_n(P) / ΨSq_n(P)
```

is supposed to blow up, not define a regular tangent coordinate.  Differentiating

```text
(dφ_n * ΨSq_n - φ_n * dΨSq_n) / ΨSq_n^2
```

at `ΨSq_n(P)=0` is not a valid local computation in the target tangent space.  It is trying to use an affine chart that does not contain the image point.

The correct bypass is to use the local parameter at `O`:

```text
t = -X/Y.
```

With projective division-polynomial coordinates,

```text
t([n]Pε) = -X_n(Pε)/Y_n(Pε)
```

and this is regular at `O` because `Y_n(P)` is nonzero.  This gives exactly the derivative/tangent identity above.

So there is a good bypass of an explicit `translateToOJet` object, but it is **not** the affine `φ/ΨSq` quotient.  It is the projective local-parameter calculation, and it needs `Ω_n`.

### Why `mk_φ` and `mk_Ψ_sq` are insufficient

The existing coordinate-ring facts

```lean
mk_φ
mk_Ψ_sq
```

control the affine `x`-coordinate relation.  They do not provide:

```text
Y_n = Ω_n,
projective target coordinate near O,
local parameter t = -X/Y,
unit/nonzero of Ω_n at Ψ_n=0.
```

Those are exactly the missing ingredients for the derivative/tangent bridge.

---

## Recommended definitions after this review

### Keep these scalar definitions

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The tangent scalar at a non-2-torsion affine point, using the invariant differential. -/
def tangentScalarAtAffine (x y dx : K) : K :=
  dx / W.toAffine.polynomialY.evalEval x y

lemma tangentScalarAtAffine_ne_zero_of_dx_ne_zero
    {x y dx : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hdx : dx ≠ 0) :
    tangentScalarAtAffine W x y dx ≠ 0 := by
  unfold tangentScalarAtAffine
  exact div_ne_zero hdx hY

/-- Combined first-order differential theorem.  This is the theorem to connect to
`TangentO.nsmul₁_eq_natCast_mul`. -/
theorem localCoeff_nsmul_dual_eq_natCast_mul_tangentScalar
    {n : ℕ} {x y dx dy : K}
    (hP : W.Equation x y)
    (hdual : /* dual-number lift is on W */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    /* local parameter coefficient of `[n](Pε)` at O */
      = (n : K) * tangentScalarAtAffine W x y dx := by
  -- This should be a wrapper around your existing `TangentO.nsmul₁_eq_natCast_mul`,
  -- plus the identification of the input tangent with `dx / ψ₂(P)`.
  sorry

end

end WeierstrassCurve
```

### Add this projective bridge, not a bare `OJetPoint`

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Full division polynomial vanishing over dual numbers sends the dual point to `O`
under multiplication by `n`. -/
theorem nsmul_dual_eq_O_of_preΨ'_dual_eq_zero
    {n : ℕ} {x y dx dy : K}
    (hdual : /* `(x+εdx,y+εdy)` lies on W over dual numbers */ True)
    (hYunit : IsUnit (/* ψ₂(Pε) */ (1 : TrivSqZeroExt K K)))
    (hpre : aeval (/* x+εdx */ (0 : TrivSqZeroExt K K)) (W.preΨ' n) = 0) :
    /* `[n](Pε) = O` over dual numbers */ True := by
  -- This is the critical projective/homogeneous division-polynomial formula.
  -- It requires Ω_n or an equivalent projective Y-coordinate formula.
  sorry

/-- The derivative contradiction theorem, after the bridge. -/
theorem no_dual_preΨ'_root_with_nonzero_dx
    {n : ℕ} (hn : (n : K) ≠ 0)
    {x y dx dy : K}
    (hP : W.Equation x y)
    (hdual : /* dual lift */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hdx : dx ≠ 0)
    (hpre : aeval (/* x+εdx */ (0 : TrivSqZeroExt K K)) (W.preΨ' n) = 0) :
    False := by
  have hO := nsmul_dual_eq_O_of_preΨ'_dual_eq_zero
    (W := W) (n := n) hdual (by
      -- `psi2_dual_isUnit`
      sorry) hpre
  have hlocal_zero :
      /* local coeff of `[n](Pε)` */ (0 : K) = 0 := by
    -- from `hO`
    rfl
  have hlocal_formula := localCoeff_nsmul_dual_eq_natCast_mul_tangentScalar
    (W := W) (n := n) hP hdual hY
  have htangent_ne : tangentScalarAtAffine W x y dx ≠ 0 :=
    tangentScalarAtAffine_ne_zero_of_dx_ne_zero (W := W) hY hdx
  have : (n : K) * tangentScalarAtAffine W x y dx = 0 := by
    -- combine `hlocal_zero` and `hlocal_formula`
    sorry
  exact htangent_ne ((mul_eq_zero.mp this).resolve_left hn)

end

end WeierstrassCurve
```

The placeholders are deliberately the real seams.  The definitions themselves are now minimal: no bare wrapper, no duplicate `OJetPoint.nsmul`, no affine quotient derivative.

---

## Final architecture decision

1. **Do not introduce bare `OJetPoint`.**  Use `TangentO`/`K` directly.
2. **Do not define `translateToOJet` as an object-level map yet.**  Define the scalar `dx / ψ₂(P)` and a combined differential theorem for `[n]`.
3. **The exact derivative/tangent identity is through the projective local parameter**
   ```text
   t([n]Pε) = -Φ_n(Pε) Ψ_n(Pε) / Ω_n(Pε),
   ```
   not through affine `φ_n / ΨSq_n`.
4. **The critical missing API is `Ω_n` / projective division-polynomial coordinates over dual numbers.**  That is where the bridge lives.
5. **Route (d) works only after replacing affine `x` by local parameter `t` at `O`.**  As an affine L’Hôpital calculation it is either ill-typed geometrically or circular.

This means the next design target should be the projective bridge theorem, not a new formal-jet wrapper.
