# Q262 (dm3): Fraction-field route vs local/evaluated route

## Executive answer

For the fraction-field route:

* **Yes**, Mathlib has the function field of the affine coordinate ring.  In the
  current API it is

  ```lean
  WeierstrassCurve.Affine.FunctionField W
  ```

  and it is definitionally

  ```lean
  FractionRing W.CoordinateRing
  ```

  for `W : WeierstrassCurve.Affine R`.  Since `Affine` is an abbreviation around
  Weierstrass curves, in local notation this is usually `W.toAffine.FunctionField`
  or simply `Affine.FunctionField W` depending on namespace/import context.

* **Yes**, Mathlib has `Affine.Point` and `Jacobian.Point` over any field, hence
  over that function field after base-changing the curve.  The group law exists
  there.

* **No**, Mathlib does not appear to have a theorem saying that the division
  polynomial `ψ_n` in the function field cuts out

  ```lean
  n • genericPoint = 0
  ```

  or that

  ```lean
  n • genericPoint = [φ_n : ω_n : ψ_n].
  ```

  That is essentially the projective/division-polynomial theorem you are trying
  to build.  The existing `mk_ψ`, `mk_φ`, `mk_Ψ_sq` lemmas normalize polynomial
  expressions in the coordinate ring; they do not identify those expressions with
  `nsmul` in the Jacobian group law.

For your **actual separability/local-parameter goal**, the fraction-field route is
probably not the simplest route.  A **local/evaluated coordinate-ring route** is
closer to the goal, but with one important correction: evaluation at a point is
only a zero-th order statement.  To compute a local parameter coefficient, you
need the same identities in the **local ring at the point** or in a completed
local ring, not merely their evaluated values.

For the Mazur `|T| ≤ 16` separability brick, the fastest formal path still looks
like the finite per-`n` Bezout/resultant certificates.  The local-parameter route
is mathematically good, but formalizing the required local-ring/completion
infrastructure may be larger than the finite certificates.

---

## (a) Fraction field of the coordinate ring

Mathlib defines the affine coordinate ring and its function field in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`:

```lean
namespace WeierstrassCurve
namespace Affine

/-- The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩`. -/
abbrev CoordinateRing (W : Affine R) : Type _ :=
  AdjoinRoot W.polynomial

/-- The function field `R(W) := Frac(R[W])`. -/
abbrev FunctionField (W : Affine R) : Type _ :=
  FractionRing W.CoordinateRing

end Affine
end WeierstrassCurve
```

The same file also provides an integral-domain instance:

```lean
instance [IsDomain R] : IsDomain W.CoordinateRing
```

So if your base is a field `k`, then the coordinate ring of `W.toAffine` is a
domain, and `FractionRing W.toAffine.CoordinateRing` is available as its fraction
field.

The practical local names may be one of these, depending on opened namespaces:

```lean
W.toAffine.CoordinateRing
W.toAffine.FunctionField
WeierstrassCurve.Affine.CoordinateRing W.toAffine
WeierstrassCurve.Affine.FunctionField W.toAffine
```

A useful skeleton:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k)

abbrev CoordRing : Type _ :=
  W.toAffine.CoordinateRing

abbrev FuncField : Type _ :=
  W.toAffine.FunctionField

-- Definitional target:
-- FuncField W = FractionRing (CoordRing W)

end WeierstrassCurve
```

---

## (b) Points and group law over the function field

Yes.  Mathlib has point types and group laws over any field.

The relevant APIs are:

```lean
#check WeierstrassCurve.Affine.Point
#check WeierstrassCurve.Affine.Point.instAddCommGroup

#check WeierstrassCurve.Jacobian.Point
#check WeierstrassCurve.Jacobian.Point.instAddCommGroup
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
#check WeierstrassCurve.Jacobian.Point.toAffineLift_add
```

So once you set

```lean
K := W.toAffine.FunctionField
```

and base-change the curve to `K`, you can form

```lean
(W⁄K).toAffine.Point
(W⁄K).toJacobian.Point
```

and use the group law.

What Mathlib does **not** give for free is the generic point as a named object.
You would define it yourself from the coordinate-ring classes of `X` and `Y`, then
map those classes into the fraction field.

Schematic shape:

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k)

noncomputable abbrev K : Type _ :=
  W.toAffine.FunctionField

noncomputable abbrev A : Type _ :=
  W.toAffine.CoordinateRing

-- Coordinate-ring classes of `X` and `Y`.
noncomputable def genericX_A : A W :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)

noncomputable def genericY_A : A W :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X

-- Their images in the function field.
noncomputable def genericX_K : K W :=
  algebraMap (A W) (K W) (genericX_A W)

noncomputable def genericY_K : K W :=
  algebraMap (A W) (K W) (genericY_A W)

-- Then prove the equation and nonsingularity and package as a point.
noncomputable def genericAffinePoint
    [DecidableEq (K W)] : (W⁄K W).toAffine.Point := by
  -- Expected target: `.some (genericX_K W) (genericY_K W) hNonsing`
  -- `hEquation` comes from the quotient relation defining the coordinate ring.
  -- `hNonsing` uses `[W.IsElliptic]` after base-change.
  sorry

end WeierstrassCurve
```

The exact `Polynomial.C Polynomial.X` vs `Polynomial.X` notation depends on the
`R[X][Y]` convention: `Polynomial.X` in the outer polynomial ring is the `Y`
variable, while `Polynomial.C Polynomial.X` is the embedded `X` variable.

This generic point construction is doable, but it is not already packaged as a
single Mathlib theorem.

---

## (c) Is there a theorem connecting `ψ_n` to `n • genericPoint = 0`?

I would assume **no** for planning purposes.

Mathlib has these coordinate-ring comparison lemmas:

```lean
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
```

They say that the bivariate and univariate division-polynomial packages agree
modulo the curve relation.  Conceptually:

```lean
mk W (W.ψ n) = mk W (W.Ψ n)
mk W (W.φ n) = mk W (Polynomial.C (W.Φ n))
mk W (W.Ψ n)^2 = mk W (Polynomial.C (W.ΨSq n))
```

But they do not say:

```lean
n • genericPoint = 0 ↔ ψ_n = 0
```

or

```lean
(n • genericPoint).point = ⟦![φ_n, ω_n, ψ_n]⟧.
```

Those statements are exactly the missing projective formula / division-polynomial
representability theorem.  If Mathlib already had them, the `ω_n` bridge and the
projective induction would be unnecessary.

So the fraction-field route still requires you to prove a generic-point
representability theorem.  The fraction field helps only with one issue: a
nonzero scalar like `ψ_{m-1}` becomes a unit, so Mathlib’s `PointClass` quotient
can use it as a weighted scalar.  It does not supply the `nsmul` theorem itself.

---

## (d) Is the evaluated/local route simpler for the actual separability goal?

Probably yes, but with a local-ring refinement.

Your proposed route:

```text
prove coordinate-ring identities generically;
evaluate at P = (x,y);
obtain projective representative [φ_n(P) : ω_n(P) : 0];
use φ_n(P) ≠ 0 to get ω_n(P) ≠ 0;
compute the local parameter coefficient.
```

is directionally right.  The key point is that for local parameter coefficients,
plain evaluation is not enough.  Evaluation gives only:

```text
ψ_n(P) = 0,
φ_n(P) ≠ 0,
ω_n(P) ≠ 0.
```

To compute a coefficient, you need the identity in a neighborhood of `P`, i.e. in
one of:

```text
localization of the affine coordinate ring at the maximal ideal of P;
completed local ring at P;
formal power series ring after choosing a local parameter.
```

In that local ring, `φ_n` and `ω_n` are units because their values at `P` are
nonzero, while `ψ_n` lies in the maximal ideal.  The projective local parameter at
infinity is, up to the project’s sign convention,

```text
t_O = -X*Z/Y
```

in weighted Jacobian coordinates `[X:Y:Z]`.  Therefore, if

```text
[n]Q = [φ_n(Q) : ω_n(Q) : ψ_n(Q)]
```

in the local sense, then near `P`

```text
t_O([n]Q) = - φ_n(Q) * ψ_n(Q) / ω_n(Q).
```

Since `φ_n(P)` and `ω_n(P)` are nonzero, the factor

```text
-φ_n / ω_n
```

is a unit in the local ring.  Thus `t_O([n]Q)` is a unit times `ψ_n(Q)`.  This is
exactly the right shape for proving simple zero / derivative nonvanishing of
`ψ_n`, once you know the linear term of `[n]^* t_O` is nonzero.

A local-ring skeleton:

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]
variable (x y : k)

/-- Schematic maximal ideal of the affine coordinate ring at `(x,y)`. -/
def pointIdeal : Ideal W.toAffine.CoordinateRing :=
  sorry

/-- Local ring at the point `(x,y)`. -/
abbrev LocalAtPoint : Type _ :=
  Localization.AtPrime (pointIdeal W x y)

/-- In the local ring, a function with nonzero value at `P` is a unit. -/
theorem isUnit_of_eval_ne_zero
    {f : W.toAffine.CoordinateRing}
    (hf : evalAtPoint W x y f ≠ 0) :
    IsUnit (algebraMap W.toAffine.CoordinateRing (LocalAtPoint W x y) f) := by
  -- Standard localization-at-maximal-ideal fact.
  sorry

/-- Local parameter formula for the projective representative. -/
theorem local_t_mul_eq_unit_mul_psi
    {n : ℕ}
    (hψ : evalAtPoint W x y (ψClass W n) = 0)
    (hφ : evalAtPoint W x y (φClass W n) ≠ 0)
    (hω : evalAtPoint W x y (ωClass W n) ≠ 0) :
    localPullbackT W x y n
      = localUnit W x y n * algebraMap _ _ (ψClass W n) := by
  -- Use the coordinate-ring/projective formula in the local ring.
  -- `φ` and `ω` are units by `hφ`, `hω`.
  sorry

end WeierstrassCurve
```

This is often simpler than the fraction-field `PointClass` route because you
avoid proving a global generic `nsmul` theorem and avoid descending from the
fraction field.  But it still needs local-ring infrastructure.

### Important caveat

The evaluated identity alone does **not** prove that

```text
[φ_n(P) : ω_n(P) : 0]
```

is `[n]P` as a Mathlib point, because raw cleared projective formulas can
degenerate at exceptional points.  What saves the local route is not mere
evaluation; it is the stronger statement that the projective formula holds in the
local ring / punctured neighborhood where the relevant unit factors are tracked.

---

## How to get `ω_n(P) ≠ 0` from `φ_n(P) ≠ 0`

This part is straightforward once you know the representative lies on the
Jacobian curve at `Z = 0`.

The weighted projective equation at infinity is:

```text
Y^2 = X^3
```

because all terms involving `Z` vanish.  Therefore, at `Z = 0`, if

```text
X = φ_n(P) ≠ 0,
```

then

```text
Y^2 = X^3 ≠ 0,
```

so

```text
Y = ω_n(P) ≠ 0.
```

Lean shape:

```lean
theorem omega_eval_ne_of_phi_eval_ne_of_Z_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k)
    {X Y : k}
    (hEq : W.toJacobian.Equation ![X, Y, 0])
    (hX : X ≠ 0) :
    Y ≠ 0 := by
  have hYX : Y ^ 2 = X ^ 3 := by
    -- unfold `Jacobian.Equation` / equation at `Z=0`
    -- all `aᵢ` terms vanish
    simpa [WeierstrassCurve.Jacobian.Equation] using hEq
  intro hY
  apply hX
  have : X ^ 3 = 0 := by
    simpa [hY] using hYX.symm
  exact pow_eq_zero this
```

The exact theorem names around `Jacobian.Equation` may need adjustment, but the
argument is just `Y^2 = X^3` at `Z=0` in a field.

---

## Which route is actually simplest?

For the narrow separability goal, ordered by expected formalization effort:

### 1. Per-`n` Bezout/resultant certificates

Still the fastest for `n ≤ 16`.

You avoid:

* generic point construction;
* fraction fields;
* local rings/completions;
* `ω_n` for all `n`;
* point-level `nsmul` induction.

You only prove:

```lean
A_n * preΨ'_n + B_n * derivative preΨ'_n = C_n * Δ^e
```

and then use `[W.IsElliptic]` and `(n : k) ≠ 0`.

### 2. Local/evaluated route

Likely the best conceptual route if you specifically want the local parameter
coefficient.  But it needs local rings or completions.  It is less global than the
fraction-field route and avoids the nonunit `PointClass` problem.

### 3. Fraction-field generic-point route

Useful if the project wants a reusable theorem that `[n]P` is represented by
`[φ_n:ω_n:ψ_n]` generically.  But it still requires proving the projective formula
and generic nonvanishing, and it does not by itself prove separability.

### 4. Full all-`n` projective formula over the coordinate ring

Most reusable, but largest.

---

## Recommendation

For the current separability/derivative nonvanishing brick, do **not** switch to
the fraction-field route unless you already need the general projective formula
for other reasons.

Use one of these two strategies:

1. **Fastest:** finish the finite `n ≤ 16` Bezout/resultant certificates.
2. **If local-parameter proof is required:** use the coordinate-ring identities in
   the **local ring at the evaluated point**, not the global fraction field.  Prove
   `φ_n(P)` and `ω_n(P)` are units locally, then show

   ```text
   t_O([n]Q) = unit · ψ_n(Q).
   ```

The fraction field answers the unit-scalar problem for generic point classes, but
it does not provide the missing theorem connecting `ψ_n` to `nsmul`; that theorem
is exactly the projective formula infrastructure.
