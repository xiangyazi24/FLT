# Q1149 (dm3): base-change embedding for `WeierstrassCurve.Affine.Point`

## Short answer

Yes: for the affine nonsingular-point group API, the right map is

```text
WeierstrassCurve.Affine.Point.map
```

and the injectivity theorem is

```text
WeierstrassCurve.Affine.Point.map_injective
```

There is also a convenience abbreviation

```text
WeierstrassCurve.Affine.Point.baseChange
```

for the usual field-extension map.

For a field extension `K/ℚ`, the map you probably want is most cleanly typed as

```text
(W⁄ℚ).Point →+ (W⁄K).Point
```

or equivalently

```text
(W⁄ℚ).Point →+ (W.map (algebraMap ℚ K)).Point
```

I would avoid writing the target as

```text
((W.map (algebraMap ℚ K))⁄K).Point
```

unless you really need that exact shape.  It is a double base change from `K` to `K`; it should simplify back to `(W.map (algebraMap ℚ K)).Point`, but it creates extra definitional/propositional-equality noise for no benefit.

One important constraint: the `Point.map` group homomorphism in `Affine/Point.lean` is over **fields**.  So if your target is called `R`, you need `[Field R] [Algebra ℚ R]`.  A bare `[CommRing R]` is not enough for this group-hom API.

## Source file inspected

I inspected the FLT-pinned Mathlib source at revision

```text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

in

```text
Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean
Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean
```

## 1. Is `Point.map` the right function? What is its exact signature?

Yes, if your point type is the affine nonsingular point type `WeierstrassCurve.Affine.Point`.

The relevant source block is under

```text
namespace WeierstrassCurve
namespace Affine
namespace Point
```

The source variables are essentially:

```text
{R S : Type*} [CommRing R] [CommRing S]
{F K : Type*} [Field F] [Field K]
{W' : Affine R}
[Algebra R S]
[Algebra R F] [Algebra S F] [IsScalarTower R S F]
[Algebra R K] [Algebra S K] [IsScalarTower R S K]
(f : F →ₐ[S] K)
```

and the declaration is:

```text
noncomputable def WeierstrassCurve.Affine.Point.map :
    (W'⁄F).Point →+ (W'⁄K).Point
```

The implementation sends `0` to `0`, and sends an affine point `(x,y)` to `(f x, f y)`, transporting nonsingularity using

```text
W'.baseChange_nonsingular f.injective
```

The companion simp/transport lemmas are:

```text
WeierstrassCurve.Affine.Point.map_zero :
  map f (0 : (W'⁄F).Point) = 0

WeierstrassCurve.Affine.Point.map_some :
  map f (some _ _ h) =
    some _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h)

WeierstrassCurve.Affine.Point.map_id :
  map (Algebra.ofId F F) P = P

WeierstrassCurve.Affine.Point.map_map :
  map g (map f P) = map (g.comp f) P
```

For ordinary scalar extension from `F` to `K`, use the abbreviation:

```text
noncomputable abbrev WeierstrassCurve.Affine.Point.baseChange
    [Algebra F K] [IsScalarTower R F K] :
    (W'⁄F).Point →+ (W'⁄K).Point :=
  map (Algebra.ofId F K)
```

## 2. Is there a `Point.map_injective` theorem?

Yes.  The exact theorem name is:

```text
WeierstrassCurve.Affine.Point.map_injective
```

with source shape:

```text
lemma map_injective : Function.Injective <| map (W' := W') f
```

It does **not** ask you to supply a separate proof that `f` is injective, because `f : F →ₐ[S] K` is an algebra hom between fields, and the proof uses `f.injective` internally.

Be careful: the file also has a different theorem named

```text
WeierstrassCurve.Affine.CoordinateRing.map_injective
```

for coordinate rings.  That one has the shape

```text
lemma CoordinateRing.map_injective {f : R →+* S}
    (hf : Function.Injective f) :
    Function.Injective <| CoordinateRing.map W' f
```

The theorem you want for the point map is the namespace-qualified one:

```text
WeierstrassCurve.Affine.Point.map_injective
```

## 3. Does `W.map (algebraMap ℚ K)` automatically get `IsElliptic`?

Yes.

In `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, after `[W.IsElliptic]`, the file defines the instance:

```text
instance : (W.map f).IsElliptic := by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]
```

So if you have

```text
W : WeierstrassCurve ℚ
[W.IsElliptic]
K : Type* [CommRing K]
```

then Lean should infer

```text
(W.map (algebraMap ℚ K)).IsElliptic
```

provided the necessary ring/algebra instances are available.  For the point-group base-change map, you will normally assume the stronger target hypotheses

```text
[Field K] [Algebra ℚ K]
```

because `Affine.Point.map` is a group homomorphism between point groups over fields.

## 4. Imports

For this API, the direct import is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
```

That file publicly imports `Affine.Formula`, which imports `Affine.Basic`, which imports the underlying Weierstrass/base-change material.

If you use the `⁄` notation outside the `WeierstrassCurve` namespaces, you may need to open the scoped notation.  The robust options are either:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open scoped WeierstrassCurve
open scoped WeierstrassCurve.Affine
```

or avoid the notation in fragile declarations by spelling out `WeierstrassCurve.Affine.baseChange` / `WeierstrassCurve.baseChange`.

## Concrete Lean wrapper: rational points into a field extension

This is the wrapper I would use locally.  I call the target field `K` to avoid clashing with the source-ring variable names in Mathlib.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open scoped WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FLT

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Base-change map on affine nonsingular points from `ℚ` to a field extension `K`. -/
noncomputable def ratPointBaseChange (W : WeierstrassCurve ℚ) :
    (W⁄ℚ).Point →+ (W⁄K).Point :=
  WeierstrassCurve.Affine.Point.baseChange (W' := W.toAffine) ℚ K

/-- The base-change map on affine nonsingular points is injective. -/
theorem ratPointBaseChange_injective (W : WeierstrassCurve ℚ) :
    Function.Injective (ratPointBaseChange (K := K) W) := by
  simpa [ratPointBaseChange, WeierstrassCurve.Affine.Point.baseChange] using
    (WeierstrassCurve.Affine.Point.map_injective
      (W' := W.toAffine) (f := Algebra.ofId ℚ K))

end FLT
```

If Lean complains about scoped notation in your local file, use this no-notation version:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

namespace FLT

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Same map, avoiding the `⁄` notation. -/
noncomputable def ratPointBaseChangeNoNotation (W : WeierstrassCurve ℚ) :
    (WeierstrassCurve.Affine.baseChange W.toAffine ℚ).Point →+
      (WeierstrassCurve.Affine.baseChange W.toAffine K).Point :=
  WeierstrassCurve.Affine.Point.baseChange (W' := W.toAffine) ℚ K

/-- Injectivity, no-notation version. -/
theorem ratPointBaseChangeNoNotation_injective (W : WeierstrassCurve ℚ) :
    Function.Injective (ratPointBaseChangeNoNotation (K := K) W) := by
  simpa [ratPointBaseChangeNoNotation, WeierstrassCurve.Affine.Point.baseChange] using
    (WeierstrassCurve.Affine.Point.map_injective
      (W' := W.toAffine) (f := Algebra.ofId ℚ K))

end FLT
```

## If you insist on the target `(W.map (algebraMap ℚ K)).Point`

The target `(W⁄K).Point` is the preferred spelling, because

```text
W⁄K = W.map (algebraMap ℚ K)
```

by definition of `WeierstrassCurve.baseChange`.

If another part of the project expects the explicit `map` spelling, use `simpa` to normalize the target:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open scoped WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FLT

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Same map, with target written using `W.map (algebraMap ℚ K)`. -/
noncomputable def ratPointBaseChangeToMapTarget (W : WeierstrassCurve ℚ) :
    (W⁄ℚ).Point →+ (W.map (algebraMap ℚ K)).Point := by
  simpa [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange] using
    (WeierstrassCurve.Affine.Point.baseChange (W' := W.toAffine) ℚ K)

/-- Injectivity of the explicitly-targeted version. -/
theorem ratPointBaseChangeToMapTarget_injective (W : WeierstrassCurve ℚ) :
    Function.Injective (ratPointBaseChangeToMapTarget (K := K) W) := by
  simpa [ratPointBaseChangeToMapTarget,
    WeierstrassCurve.Affine.Point.baseChange,
    WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange] using
    (WeierstrassCurve.Affine.Point.map_injective
      (W' := W.toAffine) (f := Algebra.ofId ℚ K))

end FLT
```

If your target is literally

```text
((W.map (algebraMap ℚ K))⁄K).Point
```

then you are base-changing the already-base-changed curve from `K` to `K`.  I would first change the goal to `(W⁄K).Point` or `(W.map (algebraMap ℚ K)).Point`.  If the double-base-change shape is forced by another declaration, try:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open scoped WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FLT

variable {K : Type*} [Field K] [Algebra ℚ K]

noncomputable def ratPointBaseChangeToDoubleTarget (W : WeierstrassCurve ℚ) :
    (W⁄ℚ).Point →+ ((W.map (algebraMap ℚ K))⁄K).Point := by
  simpa [WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map] using
    (WeierstrassCurve.Affine.Point.baseChange (W' := W.toAffine) ℚ K)

end FLT
```

The single-base-change target is cleaner and should be preferred.

## Final answers to the four questions

1. **Yes.** `WeierstrassCurve.Affine.Point.map` is the right function for affine nonsingular point groups.  Its type is `(W'⁄F).Point →+ (W'⁄K).Point` for `f : F →ₐ[S] K`.

2. **Yes.** The theorem is `WeierstrassCurve.Affine.Point.map_injective : Function.Injective <| map (W' := W') f`.

3. **Yes.** With `[W.IsElliptic]`, Mathlib has an instance `: (W.map f).IsElliptic`.  Hence `(W.map (algebraMap ℚ K)).IsElliptic` is inferred.

4. Use:

   ```lean
   import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
   ```

   and, if using `⁄` notation outside the namespace, open the appropriate scoped notation or spell out `WeierstrassCurve.Affine.baseChange` explicitly.
