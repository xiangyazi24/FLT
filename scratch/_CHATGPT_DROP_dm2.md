# Q2000 (dm2): Weil pairing formalization route analysis in Lean 4

Date searched: 2026-06-28.

Scope searched:

* `leanprover-community/mathlib4`, current `master` as exposed by the GitHub connector.
* `ImperialCollegeLondon/FLT`, current `main` as exposed by the GitHub connector.
* Target question: what infrastructure exists for defining the Weil pairing
  `e_m : E[m] × E[m] → μ_m` by the classical divisor/function-field route?

Bottom line: Mathlib has substantial adjacent algebraic geometry, elliptic-curve, class-group, function-field, torsion, and roots-of-unity infrastructure, but it does **not** yet have the divisor/Picard/Riemann-Roch layer needed to define the Weil pairing from divisors on a complete nonsingular curve in the textbook way.  The feasible near-term route is to axiomatize the Weil pairing package, or to build a special-purpose Weierstrass/Miller-function divisor calculus before attempting the fully general divisor-theoretic construction.

## Executive status table

| Needed for divisor-definition of Weil pairing | Mathlib status | FLT status | Planning consequence |
|---|---|---|---|
| Weil divisors on algebraic curves | Not found as a general algebraic-geometry API. There is `MeromorphicOn.divisor`, but it is complex/nonarchimedean analytic over normed fields and stores a locally finite integer-valued function. | Not found. | Must build, or avoid by using an explicit Miller-function/class-group route. |
| Principal divisors / divisor class group of a curve | No general `div : K(X)ˣ → Div X` or `Cl X` found. There is `ClassGroup R` for fractional ideals of a domain/Dedekind domain modulo principal fractional ideals. | No native curve class group. | Fractional ideals can help for affine coordinate rings, but do not replace projective curve divisors/Picard. |
| Picard group / line bundles on elliptic curve | `CommRing.Pic R` exists for invertible `R`-modules. Sheaves of modules have a locally-free predicate. But there is no Picard group of a scheme/curve or line bundle API connected to elliptic curves. | Not found. | Need either new scheme Picard/line-bundle layer, or avoid Picard entirely for first pairing applications. |
| Function field of a curve/scheme | Positive. `Scheme.functionField` exists for irreducible schemes as the generic-point stalk; integral schemes make it a field. Weierstrass affine curves also have `Affine.FunctionField := FractionRing CoordinateRing`. | FLT does not add new curve-function-field API. | Function-field input is available, especially for affine Weierstrass curves. |
| Degree map on divisors | No divisor degree map found. Polynomial/rational-function degrees and norm-degree lemmas exist, but no `degree : Divisor X → ℤ` with residue-field weights. | Not found. | Must define degree together with divisor type if going general. |
| Riemann-Roch / `ℓ(D)` dimension formulas | Not found. Searches for `RiemannRoch`, `Riemann-Roch`, and `Riemann Roch` found no formal theorem/API. | Not found. | Textbook existence of functions with divisor `m(P)-m(O)` is unavailable; use explicit Miller functions or axioms. |
| Elliptic curve group law and torsion | Positive. Mathlib has affine Weierstrass nonsingular points as an abelian group. FLT defines `E.nTorsion n := Submodule.torsionBy ℤ (E⁄k).Point n`. | Positive but theorem bodies still include `sorry` for finiteness/cardinality/dimension/Galois action details. | Pairing can target existing torsion subgroup types. |
| Roots of unity target `μ_m` | Positive: `rootsOfUnity n M` is a subgroup of units satisfying `ζ^n = 1`. | Available through Mathlib. | Good target type for a pairing. |

## Search log, positive hits, and negative hits

### Mathlib searches

Positive hits:

* `Divisor` → `Mathlib/Analysis/Meromorphic/Divisor.lean`.
* `locallyFinsuppWithin` → `Mathlib/Topology/LocallyFinsupp.lean`.
* `PicardGroup` → `Mathlib/RingTheory/PicardGroup.lean`.
* `LocallyFree` → `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`.
* `ClassGroup` → `Mathlib/RingTheory/ClassGroup/Basic.lean`, `Mathlib/RingTheory/UniqueFactorizationDomain/ClassGroup.lean`, and class-number files.
* `functionField` → `Mathlib/AlgebraicGeometry/FunctionField.lean`, `Mathlib/NumberTheory/FunctionField.lean`, `Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`.
* `EllipticCurve` → `Mathlib/AlgebraicGeometry/EllipticCurve/...`, especially `Affine/Point.lean`, `Projective/Point.lean`, division-polynomial files, and Jacobian files.
* `rootsOfUnity` → `Mathlib/RingTheory/RootsOfUnity/Basic.lean` and related files.

Negative or near-negative hits:

* `WeilDivisor` → no direct hit.
* `CartierDivisor` → no direct hit.
* `Cartier divisor` → no direct hit.
* `Weil divisor` → no formal API hit, only documentation/status metadata.
* `LineBundle` → no direct algebraic-geometry line-bundle API hit.
* `SheafOfModules Invertible` → no invertible-sheaf API hit.
* `WeilPairing` / `Weil pairing` → no hit.
* `RiemannRoch`, `Riemann-Roch`, `Riemann Roch` → no formal theorem/API hit.
* `locallyFinsuppWithin degree` → no hit.

### ImperialCollegeLondon/FLT searches

Positive hits:

* `EllipticCurve` → `FLT/EllipticCurve/Torsion.lean`, `FLT/FreyCurve/...`, `FLT/GaloisRepresentation/...`, assumptions/blueprint references.
* `Divisor` → hits in number-theory/p-adic/Dedekind/blueprint files, not a curve-divisor API.
* `FLT.lean` imports `FLT.EllipticCurve.Torsion` and many p-adic/Dedekind/Galois/patching modules.

Negative hits:

* `WeilPairing` / `Weil pairing` → no hit.
* `PicardGroup Picard line bundle locally free` → no hit.
* `FunctionField` → no hit.
* `RiemannRoch Riemann Roch` → no hit.
* `ClassGroup` → no direct hit in FLT source.

## Detailed findings by requested category

## 1. Divisors on algebraic curves: Weil divisors, principal divisors, divisor class group

### What exists

#### Analytic meromorphic divisors

`Mathlib/Analysis/Meromorphic/Divisor.lean` defines

```lean
noncomputable def MeromorphicOn.divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ
```

The file description says this is the divisor of a meromorphic function, mapping a point to the order of the function there and zero when the order is infinite.  It proves basic properties:

* divisor support is finite on compact sets/subsets;
* analytic functions have nonnegative divisors;
* constants have zero divisor;
* products/inverses/powers give additive/negative/scalar relations for divisors;
* restriction compatibility.

This is not a scheme/curve Weil-divisor API.  It is for functions on subsets of a normed field `𝕜`, with target a normed vector space, and is analytic/topological in nature.

#### Locally finite support substrate

`Mathlib/Topology/LocallyFinsupp.lean` defines

```lean
Function.locallyFinsuppWithin U Y
```

as functions `X → Y` with support contained in `U` and locally finite within `U`.  It gives additive group and lattice-ordered group structures pointwise.  This is a useful design precedent for analytic divisors and possibly for topological formulations, but it is not specifically algebraic Weil divisors.

#### Fractional-ideal class group

`Mathlib/RingTheory/ClassGroup/Basic.lean` defines

```lean
def ClassGroup R :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range
```

This is the ideal class group of a domain via invertible fractional ideals modulo principal fractional ideals.  It is heavily useful for Dedekind domains and arithmetic geometry, but it is not the same API as a divisor group on a projective curve.

#### Elliptic curve points map to an affine coordinate-ring class group

`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` is important: it defines the affine coordinate ring

```lean
abbrev CoordinateRing : Type r := AdjoinRoot W'.polynomial
abbrev FunctionField : Type r := FractionRing W'.CoordinateRing
```

and constructs an addition-preserving map

```lean
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)
```

sending a nonsingular point to the class of the ideal `⟨X - x, Y - y⟩` in the affine coordinate ring.  The group law on affine points is proved by injecting into this class group.

This is the closest existing algebraic substitute for divisor-class reasoning.  It is affine and ideal-class based, not a complete-projective-curve divisor/Picard formalization.

### What does not exist, as far as the search found

I found no general definitions/API with names like:

```lean
WeilDivisor
CartierDivisor
DivisorClassGroup
principalDivisor
closedPointDivisor
```

for algebraic curves or schemes.  I also found no general map

```lean
K(X)ˣ → Div X
```

from the function field of an integral scheme/curve to Weil divisors.

### Consequence for Weil pairing

The classical definition of the Weil pairing via divisors needs:

1. divisor group on a complete nonsingular curve;
2. principal divisors of rational functions;
3. finite support of principal divisors;
4. a way to evaluate rational functions on divisors with disjoint support;
5. functions `f_P` satisfying `div(f_P) = m(P) - m(O)`.

None of this exists as a ready general Mathlib API.

## 2. Picard group / line bundles on an elliptic curve

### What exists

#### Picard group of a commutative ring

`Mathlib/RingTheory/PicardGroup.lean` defines `CommRing.Pic R`, the Picard group of a commutative ring as invertible modules up to isomorphism under tensor product.  Its docstring explicitly describes `Module.Invertible R M`, `CommRing.Pic R`, and the link to class groups via `ClassGroup.equivPic`.

Important: the TODO section in this file says to connect the ring Picard group to invertible sheaves on `Spec R` and to sheaf cohomology `H¹(Spec R, 𝓞ˣ)`.  That is exactly the missing bridge for algebraic-geometric line bundles.

#### Locally free sheaves of modules

`Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean` defines:

```lean
class SheafOfModules.IsLocallyFree (M : SheafOfModules R) : Prop
```

and proves free sheaves are locally free and locally free sheaves are quasicoherent.  This is useful infrastructure, but I found no rank-one/invertible sheaf API and no Picard group of a scheme.

### What does not exist, as far as the search found

I found no algebraic-geometry API for:

```lean
LineBundle X
InvertibleSheaf X
Scheme.Pic X
PicardGroupOfScheme
Pic0 E
```

I also found no theorem identifying elliptic-curve points with `Pic⁰` of the projective curve.

### Consequence for Weil pairing

A Picard-based route to the Weil pairing is currently blocked.  The ring Picard group and locally-free sheaf infrastructure are promising foundations, but they are not yet assembled into line bundles on curves or the elliptic-curve Picard/Jacobian package.

## 3. Function fields of curves

This is one of the stronger positive areas.

### General scheme function field

`Mathlib/AlgebraicGeometry/FunctionField.lean` defines:

```lean
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)
```

The file states that this is the local ring at the generic point and is a field when the scheme is integral.  It also defines `Scheme.germToFunctionField`, proves injectivity for integral schemes, and proves that affine opens/stalks map into the function field as fraction rings.

This is very relevant for a future scheme-theoretic divisor API.

### Number-theory function fields

`Mathlib/NumberTheory/FunctionField.lean` defines:

```lean
abbrev FunctionField [Algebra F⟮X⟯ K] : Prop :=
  FiniteDimensional F⟮X⟯ K
```

and defines the function-field ring of integers as the integral closure of `F[X]` in `K`.  It proves the ring of integers is integrally closed, a fraction ring, and Dedekind under separability assumptions.

`Mathlib/NumberTheory/ClassNumber/FunctionField.lean` then defines the class number of a function field as the finite cardinality of the class group of its ring of integers.

This is arithmetic-function-field infrastructure, not the divisor/Picard group of a named curve, but it is adjacent.

### Weierstrass affine function field

`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` defines:

```lean
abbrev WeierstrassCurve.Affine.CoordinateRing := AdjoinRoot W'.polynomial
abbrev WeierstrassCurve.Affine.FunctionField := FractionRing W'.CoordinateRing
```

For explicit elliptic curves in Weierstrass form, this is likely the most practical function-field object to use for a special-purpose Weil-pairing construction.

### Consequence for Weil pairing

Function fields are not the blocker.  The blocker is attaching valuations/orders at all closed points, proving finite support, and building divisor/principal-divisor APIs on top of the function field.

## 4. Degree map on divisors

I found no general divisor degree map for algebraic curves.

What exists nearby:

* polynomial degree and rational-function degree APIs;
* division-polynomial degree files for elliptic curves;
* finite-dimensional/`finrank` infrastructure;
* in `Affine/Point.lean`, degree-of-norm calculations in the coordinate ring, used to prove injectivity of the map from points to the class group;
* `locallyFinsuppWithin` gives finite-support machinery in compact/topological contexts.

What is missing for curve divisors:

```lean
def Divisor.degree (D : Divisor X) : ℤ :=
  ∑ x in D.support, D x * [κ(x) : k]
```

or any equivalent API.  In particular, a correct general degree map must decide whether divisors are over algebraically closed fields, rational points only, or closed points with residue-degree weights.

### Consequence for Weil pairing

Degree-zero divisors, `Pic⁰`, and statements like `div(f)` has degree zero all need to be built if taking the full divisor route.  For a Miller-function route, degree may be avoidable initially if all needed divisor identities are explicit and finite.

## 5. Riemann-Roch or dimension formulas

I found no formal Riemann-Roch API or theorem in Mathlib or FLT.

Searches for `RiemannRoch`, `Riemann-Roch`, and `Riemann Roch` did not reveal a formal theorem or module.  Mathlib has sheaves, quasicoherent/locally-free sheaves, finite-dimensional vector spaces, and scheme function fields, but I found no definitions of:

```lean
L(D)
ℓ(D)
canonicalDivisor
genus
Divisor.linearSystem
riemannRoch
```

### Consequence for Weil pairing

The textbook proof of existence/uniqueness up to scalar of functions `f_P` with

```text
div(f_P) = m(P) - m(O)
```

usually relies on divisor theory and Riemann-Roch.  That path is not ready in Mathlib.

For a first formal Weil pairing, explicit Miller functions on Weierstrass curves are more realistic than invoking Riemann-Roch.

## 6. Existing elliptic-curve and torsion infrastructure

### Mathlib elliptic curves

`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` defines nonsingular points on a Weierstrass curve in affine coordinates and proves they form an abelian group.  It has:

* `WeierstrassCurve.Affine.Point`;
* explicit negation and addition formulas;
* base-change maps on points;
* coordinate ring and function field;
* a class-group map `toClass` used to prove the group law.

This is directly useful for `E[m]`.

### FLT torsion

`ImperialCollegeLondon/FLT/FLT/EllipticCurve/Torsion.lean` defines:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

It also supplies a `Module (ZMod n) (E.nTorsion n)` instance and states theorems about finiteness, cardinality, dimension over `ZMod n`, point maps, Galois actions, and Galois representations.  Several of these are still `sorry`.

### Roots of unity target

`Mathlib/RingTheory/RootsOfUnity/Basic.lean` defines:

```lean
def rootsOfUnity (k : ℕ) (M : Type*) [CommMonoid M] : Subgroup Mˣ
```

as units `ζ` satisfying `ζ^k = 1`.  This is the natural existing target for `μ_m`.

## Recommended formalization routes

## Route A: Full textbook divisor/Picard/Riemann-Roch construction

This is conceptually clean but very large.

Required new infrastructure:

1. Closed points or codimension-one points of an integral regular curve.
2. Weil divisors as finitely supported `ℤ`-valued functions on closed points.
3. Local rings/stalks at closed points proved to be DVRs for regular curves.
4. Valuation/order map
   ```lean
   ord_x : X.functionFieldˣ → ℤ
   ```
5. Principal divisor map
   ```lean
   principalDivisor : X.functionFieldˣ →+ Divisor X
   ```
   with finite-support proof.
6. Degree map with residue-field weights.
7. Divisor class group and `Pic` comparison.
8. Riemann-Roch and genus-one specialization.
9. Elliptic curve as a nonsingular complete curve with base point `O`.
10. Proofs that the divisor classes `(P)-(O)` identify `E` with `Pic⁰`.
11. Construction of Weil functions `f_P` and the pairing.

Risk: this is a multi-project algebraic-geometry development, not a single file.

Use this route only if the goal is to contribute a general AG divisor/RR library to Mathlib.

## Route B: Special-purpose Weierstrass/Miller-function construction

This is the best non-axiomatic route for an elliptic-curve Weil pairing.

Use existing assets:

* `WeierstrassCurve.Affine.Point` for points and group law;
* `WeierstrassCurve.Affine.CoordinateRing` and `.FunctionField`;
* existing line/addition polynomials in elliptic-curve formula files;
* ideal/class-group computations already used in `Affine/Point.lean`;
* `rootsOfUnity m K` for the target.

Plan:

1. Define a restricted divisor type for explicit finite sums of rational affine/projective points:
   ```lean
   structure ExplicitDivisor (E K) where
     coeff : (E⁄K).Point →₀ ℤ
   ```
   This avoids closed points and residue degrees initially.
2. Add a distinguished point at infinity `O`; use existing `0 : (E⁄K).Point`.
3. Define known divisors of explicit functions:
   * vertical line through `P` and `-P`;
   * line through `P` and `Q`;
   * tangent line at `P`;
   * quotients of such line functions.
4. Define Miller functions recursively by formulas rather than by RR existence:
   ```text
   f_{n+m,P} = f_{n,P} * f_{m,P} * g_{nP,mP}
   ```
   where `g` is the usual line/vertical quotient.
5. Prove recursive divisor identities by explicit divisor algebra.
6. Define Weil pairing by Miller evaluation:
   ```text
   e_m(P,Q) = f_P(D_Q) / f_Q(D_P)
   ```
   or by a standard Miller formula with carefully chosen disjoint auxiliary divisors.
7. Prove bilinear/alternating/nondegenerate properties after the computational definition is stable.

Advantages:

* avoids general Riemann-Roch;
* uses existing explicit Weierstrass formulas;
* can be developed incrementally;
* closer to computational elliptic-curve pairing algorithms.

Hard parts:

* evaluation at divisors must handle zeros/poles/disjoint support cleanly;
* proving values land in `rootsOfUnity m K` still takes work;
* nondegeneracy may require more theory or a temporary axiom.

## Route C: Axiomatized Weil pairing package, then replace later

This is the best route if FLT only needs consequences of the Weil pairing, such as Galois equivariance or determinant/cyclotomic-character statements.

Possible structure:

```lean
structure WeilPairingPackage
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (E : WeierstrassCurve k) [E.IsElliptic]
    [DecidableEq k] [DecidableEq K]
    (m : ℕ) where
  pairing : E.nTorsion m → E.nTorsion m → rootsOfUnity m K
  map_add_left : ∀ P P' Q, pairing (P + P') Q = pairing P Q * pairing P' Q
  map_add_right : ∀ P Q Q', pairing P (Q + Q') = pairing P Q * pairing P Q'
  alternating : ∀ P, pairing P P = 1
  nondegenerate_left : ∀ P, (∀ Q, pairing P Q = 1) → P = 0
  nondegenerate_right : ∀ Q, (∀ P, pairing P Q = 1) → Q = 0
  galois_equivariant : Prop
```

The exact field parameters should be adjusted to FLT's current torsion/Galois setup.  Since `rootsOfUnity m K` is a subgroup of `Kˣ`, equality statements may need coercions to units/base fields.

Advantages:

* matches FLT's style of isolating major external theorems as assumptions when needed;
* unlocks downstream work immediately;
* can be refined into a class/typeclass and later instantiated by Route B or Route A.

Hard parts:

* must choose the right target field: base field, separable closure, algebraic closure, or another extension;
* Galois equivariance needs alignment with existing FLT `WeierstrassCurve.galoisRepresentation` machinery;
* nondegeneracy may require finite/cardinality facts about `E[m]`, which FLT currently states with `sorry`.

## My recommendation

For current FLT/Mazur-style downstream work, use a two-layer plan:

1. **Immediate layer:** add an assumption/structure for a Weil pairing package on `E.nTorsion m` with target `rootsOfUnity m K`.  Use this to prove representation-theoretic consequences.
2. **Replacement layer:** start a special-purpose Weierstrass/Miller-function formalization, not full Riemann-Roch.  Use `CoordinateRing`, `FunctionField`, line polynomials, and explicit divisor identities.
3. **Long-term Mathlib layer:** only after Route B matures, generalize pieces into proper algebraic divisors, principal divisors, degree, Picard of schemes, and RR.

The fully general divisor construction is mathematically canonical but currently blocked on too much missing AG infrastructure.  A special-purpose Miller construction is the realistic native Lean route.

## Minimal imports likely useful for a first axiomatic package

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.RootsOfUnity.Basic
import FLT.EllipticCurve.Torsion
```

Potential extra imports, depending on the theorem:

```lean
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.ZMod.Torsion
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
```

## Files inspected as evidence

Mathlib:

* `Mathlib/Analysis/Meromorphic/Divisor.lean`
  * analytic `MeromorphicOn.divisor` into `Function.locallyFinsuppWithin U ℤ`;
  * product/inverse/power divisor rules;
  * compact-support finiteness lemmas.
* `Mathlib/Topology/LocallyFinsupp.lean`
  * locally finite support functions and additive/lattice group structure.
* `Mathlib/RingTheory/ClassGroup/Basic.lean`
  * ideal class group of fractional ideals modulo principal ideals.
* `Mathlib/RingTheory/PicardGroup.lean`
  * ring Picard group of invertible modules;
  * TODOs explicitly mention connecting to invertible sheaves and sheaf cohomology.
* `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`
  * locally free sheaves of modules.
* `Mathlib/AlgebraicGeometry/FunctionField.lean`
  * function field of an irreducible/integral scheme as generic-point stalk.
* `Mathlib/NumberTheory/FunctionField.lean`
  * function field as finite extension of rational function field; ring of integers.
* `Mathlib/NumberTheory/ClassNumber/FunctionField.lean`
  * class number of a function field via class group of the ring of integers.
* `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
  * coordinate ring, function field, point group law, class-group map.
* `Mathlib/RingTheory/RootsOfUnity/Basic.lean`
  * `rootsOfUnity n M` target.

FLT:

* `FLT/EllipticCurve/Torsion.lean`
  * `WeierstrassCurve.nTorsion` definition;
  * `ZMod n` module instance;
  * statements for finiteness/cardinality/dimension/Galois action, many still with `sorry`.
* `FLT.lean`
  * imports `FLT.EllipticCurve.Torsion` and broad FLT project modules, but no native divisor/Picard/RR/Weil-pairing development.
