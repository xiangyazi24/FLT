# Q1172 (dm2): B-Line real topology, `E(ℝ)` has at most two connected components

## Executive answer

Yes, the classical proof can be formalized without real manifold theory, but the best Lean route is **not** to begin with `Polynomial.roots`.  The shortest elementary route is to split the work into two layers:

1. **Topology layer, easy and well supported:** prove that the real affine curve

   ```text
   C_f = { (x,y) : ℝ × ℝ | y^2 = f x }
   ```

   has at most two path components once you are given a sign-decomposition certificate for the cubic `f`.

2. **Cubic sign layer, moderate/hard:** prove that a nonsingular real cubic has either the one-real-root sign pattern or the three-real-root sign pattern.

The topology layer is mostly `Set`, intervals, `Real.sqrt`, continuity, and `IsPathConnected`.  The cubic sign layer is where most of the formalization cost is.  The statement that each projective component is homeomorphic to `S^1` is much heavier and unnecessary for the bound `≤ 2`.

The most elementary FLT target should therefore be:

```text
short Weierstrass equation over ℝ
  -> sign certificate for the completed cubic
  -> at most two path components of the affine real locus
  -> at most two connected components of the projective real locus
```

The last projective step only needs to show that the point at infinity lies on the unbounded component.  It does **not** require proving that the component is a circle.

---

## Important correction: affine vs projective

For the affine curve

```text
y^2 = f(x),
```

the unbounded component is not compact.  In the one-real-root case it is homeomorphic to a line.  In the three-real-root case the bounded oval is already circle-like in the affine chart, while the unbounded branch becomes circle-like only after adding the projective point at infinity.

So:

```text
at most two components
```

is an affine elementary-topology theorem.

But:

```text
each component is homeomorphic to S^1
```

is a projective compactification theorem and is much heavier.

For B-Line purposes, avoid the `S^1` statement.  It is strictly stronger than needed.

---

## Mathlib support ranking for the three requested facts

### Fact 2 has the most support

Fact 2:

```text
{(x,y) : y^2 = f(x)} has one or two connected components.
```

This has the best Mathlib support **after** replacing “`f` is a cubic” by a sign-decomposition hypothesis.

Useful APIs:

```lean
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
```

Concrete names to use:

```lean
-- Connected sets/components
IsConnected
IsPreconnected
connectedComponent
connectedComponentIn
connectedComponent_eq
connectedComponent_eq_iff_mem
isConnected_Icc
isConnected_Ici
isConnected_Iic
isConnected_Ioi
isConnected_Iio
IsConnected.image
IsConnected.union

-- Path connected sets/components
Joined
JoinedIn
JoinedIn.ofLine
JoinedIn.trans
JoinedIn.symm
IsPathConnected
isPathConnected_iff
IsPathConnected.image
IsPathConnected.union
pathComponent
pathComponent_subset_component
ZerothHomotopy
ZerothHomotopy.toConnectedComponents
ZerothHomotopy.toConnectedComponents_surjective

-- Intermediate value / intervals
intermediate_value_Icc
intermediate_value_Icc'
intermediate_value_univ
IsPreconnected.intermediate_value
isPreconnected_Icc
isPreconnected_Ici
isPreconnected_Iic
isPreconnected_Ioi
isPreconnected_Iio
ContinuousOn.surjOn_Icc

-- Square root and continuity support
Real.sqrt
Real.sqrt_nonneg
Real.sq_sqrt
Real.sqrt_sq_eq_abs
Real.sqPartialHomeomorph
Real.hasDerivAt_sqrt
Real.contDiffAt_sqrt
```

For global continuity of expressions involving square roots, I would generally let the `continuity` tactic try first:

```lean
  continuity
```

and only fall back to named sqrt continuity lemmas if needed.

### Fact 1 has partial support, but not the exact packaged theorem

Fact 1:

```text
f(x) = x^3 + ax + b has one or three real roots.
```

For a nonsingular cubic this is true, but Mathlib does not appear to package exactly this theorem in a ready-to-use form.  You can build it from existing APIs.

Useful APIs:

```lean
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic
```

Concrete names:

```lean
Polynomial.roots
Polynomial.rootSet
Polynomial.IsRoot
Polynomial.mem_roots
Polynomial.mem_roots'
Polynomial.isRoot_of_mem_roots
Polynomial.card_roots
Polynomial.card_roots'
Polynomial.card_le_degree_of_subset_roots
Polynomial.finite_setOf_isRoot
Polynomial.exists_min_root
Polynomial.exists_max_root
Polynomial.rootMultiplicity
Polynomial.count_roots
Polynomial.derivative
Polynomial.natDegree
Polynomial.degree
Polynomial.eval
```

The missing work is not root-counting in a multiset; it is **ordered real root geometry**:

```text
r1 < r2 < r3,
zero set = {r1,r2,r3},
sign f is constant on each complementary interval,
sign alternates across simple roots,
leading coefficient determines the signs at ±∞.
```

That ordered-sign package is the part you should isolate as a local theorem, not redo inside the component proof.

### Fact 3 has the least support for this task

Fact 3:

```text
each component is homeomorphic to S^1.
```

This is not the right first target.  It needs:

```text
projective compactification,
explicit topology on the projective point type,
gluing the two ends of the unbounded affine branch at infinity,
a homeomorphism to a circle model.
```

Mathlib has general topology and homeomorphism infrastructure, but this is far beyond what is needed for `≤ 2` components.  Proving the component count by path covers avoids all of it.

---

## Best elementary theorem statement

Do **not** initially state the theorem for all cubics using `Polynomial.roots`.  State it for a continuous function with one of the two cubic sign patterns.

```lean
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots

namespace FLT

open Set
open scoped Topology

/-- Affine real locus of `y^2 = f x`. -/
def RealHyperellipticLocus (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ^ 2 = f p.1}

/-- A soft meaning of “at most two path components”.

This is deliberately easier to use than a cardinal statement about quotient types.
It implies the corresponding connected-component bound because path components map
onto connected components via `ZerothHomotopy.toConnectedComponents`.
-/
def HasAtMostTwoPathComponents (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ a b : X, ∀ x : X, x ∈ pathComponent a ∨ x ∈ pathComponent b

/-- One-real-root cubic sign pattern, normalized to positive leading coefficient. -/
structure OneRootSignPattern (f : ℝ → ℝ) : Prop where
  root : ℝ
  root_zero : f root = 0
  neg_left : ∀ x, x < root → f x < 0
  pos_right : ∀ x, root < x → 0 < f x

/-- Three-real-root cubic sign pattern, normalized to positive leading coefficient. -/
structure ThreeRootSignPattern (f : ℝ → ℝ) : Prop where
  r1 r2 r3 : ℝ
  h12 : r1 < r2
  h23 : r2 < r3
  zero1 : f r1 = 0
  zero2 : f r2 = 0
  zero3 : f r3 = 0
  neg_left : ∀ x, x < r1 → f x < 0
  pos_12 : ∀ x, r1 < x → x < r2 → 0 < f x
  neg_23 : ∀ x, r2 < x → x < r3 → f x < 0
  pos_right : ∀ x, r3 < x → 0 < f x

end FLT
```

Then prove the topology theorem from these sign patterns.

```lean
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace FLT

open Set
open scoped Topology

/--
Topology theorem for the one-root sign pattern.

Mathematically, the whole affine locus is the union of the upper and lower graphs
over `[r, ∞)`, glued at `(r,0)`, so it is path-connected.
-/
theorem real_locus_pathConnected_of_oneRootSignPattern
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hsign : OneRootSignPattern f) :
    IsPathConnected (RealHyperellipticLocus f) := by
  -- Proof plan:
  -- 1. Let `r := hsign.root`.
  -- 2. Every point in the locus has `r ≤ x`, since `x < r` would imply
  --    `f x < 0`, contradicting `y^2 = f x`.
  -- 3. The upper graph
  --      x ↦ (x, Real.sqrt (f x))
  --    over `Set.Ici r` is path-connected as the continuous image of an interval.
  -- 4. The lower graph
  --      x ↦ (x, -Real.sqrt (f x))
  --    over `Set.Ici r` is path-connected.
  -- 5. They intersect at `(r,0)`, using `hsign.root_zero` and `Real.sqrt_zero`.
  -- 6. Their union is the whole locus, using `Real.sq_sqrt` and
  --    `Real.sqrt_sq_eq_abs` / sign of `y`.
  -- 7. Use `IsPathConnected.union`.
  sorry

/--
Topology theorem for the three-root sign pattern.

Mathematically, the affine locus is the disjoint union of:

* the bounded oval over `[r1,r2]`, upper and lower graphs glued at both endpoints;
* the unbounded branch over `[r3,∞)`, upper and lower graphs glued at `r3`.

Thus it has at most two path components.
-/
theorem real_locus_atMostTwoPathComponents_of_threeRootSignPattern
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hsign : ThreeRootSignPattern f) :
    HasAtMostTwoPathComponents {p : ℝ × ℝ // p ∈ RealHyperellipticLocus f} := by
  -- Proof plan:
  -- 1. Define the bounded set `B` inside the subtype by `x ∈ Set.Icc r1 r2`.
  -- 2. Define the unbounded set `U` inside the subtype by `x ∈ Set.Ici r3`.
  -- 3. Show every point of the locus lies in `B ∪ U`, using the sign pattern
  --    and `0 ≤ y^2`.
  -- 4. Show `B` is path-connected as union of upper/lower sqrt graphs over
  --    `Set.Icc r1 r2`, glued at both endpoints.
  -- 5. Show `U` is path-connected as union of upper/lower sqrt graphs over
  --    `Set.Ici r3`, glued at `r3`.
  -- 6. Pick basepoints in `B` and `U`, e.g. `(r1,0)` and `(r3,0)`, and show
  --    every point lies in one of their path components.
  sorry

end FLT
```

The `sorry`s here are not deep manifold theory.  They are graph/path-connectedness boilerplate plus square-root algebra.  The key supporting lemmas should be factored out as reusable graph lemmas.

---

## Reusable graph lemmas to build first

The most useful helper is: a continuous graph over a path-connected interval is path-connected.

```lean
import Mathlib.Topology.Connected.PathConnected

namespace FLT

open Set
open scoped Topology

/-- Continuous image of a path-connected set is path-connected, graph version. -/
lemma isPathConnected_graph_on
    {s : Set ℝ} {g : ℝ → ℝ}
    (hs : IsPathConnected s)
    (hg : ContinuousOn g s) :
    IsPathConnected ((fun x : ℝ => (x, g x)) '' s) := by
  exact hs.image' (by
    -- continuity of `x ↦ (x, g x)` on `s`
    exact continuousOn_id.prod hg)

end FLT
```

The exact proof line may need minor adjustment depending on the local `ContinuousOn.prod` names, but this is the intended API.

For intervals, if a direct `isPathConnected_Icc` lemma is not available in the local Mathlib namespace, use paths explicitly via:

```lean
JoinedIn.ofLine
```

because intervals in `ℝ` are convex.  The path-connectedness file exposes `JoinedIn.ofLine`, and this is often easier than searching for interval-specific path-connected lemmas.

Then build:

```lean
lemma upper_graph_pathConnected_Icc
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) :
    IsPathConnected ((fun x : ℝ => (x, Real.sqrt (f x))) '' Set.Icc a b) := by
  apply isPathConnected_graph_on
  · -- prove path-connectedness of `Set.Icc a b`
    -- use an interval path-connected lemma if present, otherwise `JoinedIn.ofLine`
    sorry
  · -- continuity on interval
    continuity

lemma lower_graph_pathConnected_Icc
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) :
    IsPathConnected ((fun x : ℝ => (x, -Real.sqrt (f x))) '' Set.Icc a b) := by
  apply isPathConnected_graph_on
  · sorry
  · continuity
```

Likewise for `Set.Ici a`.

---

## How to prove the cubic sign certificate

For an elliptic curve over `ℝ`, after completing the square, reduce to

```text
Y^2 = F(X)
```

where `F` is a real cubic with positive leading coefficient and no repeated root.

For a short equation:

```text
F(X) = X^3 + aX + b.
```

For a general Weierstrass equation:

```text
Y = 2y + a1 x + a3
Y^2 = 4x^3 + b2 x^2 + 2 b4 x + b6.
```

Over `ℝ`, the map

```text
(x,y) ↦ (x, 2y + a1*x + a3)
```

is a homeomorphism of affine loci, with inverse

```text
(x,Y) ↦ (x, (Y - a1*x - a3)/2).
```

So the topology theorem can be stated for the completed cubic first.

The cubic sign proof should be isolated:

```lean
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace FLT

/--
A nonsingular monic cubic has either the one-root or three-root real sign pattern.
This is the main nontrivial elementary-real-analysis lemma.
-/
theorem monic_cubic_has_one_or_three_root_signPattern
    (a b : ℝ)
    (hdisc : -(4 * a^3 + 27 * b^2) ≠ 0) :
    OneRootSignPattern (fun x : ℝ => x^3 + a*x + b) ∨
      ThreeRootSignPattern (fun x : ℝ => x^3 + a*x + b) := by
  -- Proof plan:
  -- 1. `f x = x^3 + a*x + b` is continuous.
  -- 2. `f x -> -∞` as `x -> -∞`, and `f x -> +∞` as `x -> +∞`.
  -- 3. IVT gives at least one real root.
  -- 4. `Polynomial.card_roots'` gives at most three roots.
  -- 5. `hdisc` excludes multiple roots.
  -- 6. A cubic cannot have exactly two distinct real roots unless one is multiple.
  -- 7. Sort the finite real root set.  If one root, prove signs on the two
  --    complementary intervals by IVT plus absence of additional roots.
  --    If three roots, prove alternating signs similarly.
  sorry

end FLT
```

This is where `Polynomial.roots` is useful, but it is not enough by itself.  You need extra lemmas about ordered finite subsets of `ℝ` and sign constancy on intervals without roots.

A very practical way to reduce pain is to prove a more general sign-constancy lemma first:

```lean
/-- A continuous real function with no zeros on a preconnected set has constant sign. -/
lemma continuousOn_constant_sign_of_no_zero
    {s : Set ℝ} {f : ℝ → ℝ}
    (hs : IsPreconnected s)
    (hf : ContinuousOn f s)
    (hno : ∀ x ∈ s, f x ≠ 0)
    {x0 : ℝ} (hx0 : x0 ∈ s) :
    (0 < f x0 → ∀ x ∈ s, 0 < f x) ∧
    (f x0 < 0 → ∀ x ∈ s, f x < 0) := by
  -- Use `IsPreconnected.intermediate_value`: if the sign changed, IVT gives a zero.
  sorry
```

This lemma is broadly useful and avoids repeatedly doing sign arguments by hand.

---

## Do we need `Polynomial.roots`?

Use `Polynomial.roots` for **counting and multiplicity**, not for topology.

Good uses:

```lean
Polynomial.roots
Polynomial.card_roots'
Polynomial.mem_roots
Polynomial.rootMultiplicity
Polynomial.count_roots
Polynomial.finite_setOf_isRoot
Polynomial.rootSet
```

Bad first target:

```lean
-- Too ambitious as a first theorem:
#check fun (p : ℝ[X]) => p.roots
```

because `p.roots` is a multiset and does not immediately give the ordered interval decomposition of the real line.  You still need to turn the roots into sorted real numbers and prove sign behavior on the complementary intervals.

For the component theorem, a sign certificate is a much better interface than a multiset of roots.

---

## Concrete module plan for FLT

### Module 1: topology from sign patterns

Create something like:

```text
FLT/RealTopology/CubicLocusComponents.lean
```

Contents:

```lean
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace FLT

open Set
open scoped Topology

-- `RealHyperellipticLocus`
-- `HasAtMostTwoPathComponents`
-- `OneRootSignPattern`
-- `ThreeRootSignPattern`
-- graph path-connected lemmas
-- one-root path-connected theorem
-- three-root at-most-two theorem

end FLT
```

This file should not mention elliptic curves yet.

### Module 2: cubic sign classification

Create:

```text
FLT/RealTopology/CubicSign.lean
```

Contents:

```lean
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import FLT.RealTopology.CubicLocusComponents

namespace FLT

-- continuous no-zero constant-sign lemma
-- monic cubic root existence via IVT
-- nonsingular cubic has 1 or 3 real roots
-- sign-pattern theorem

end FLT
```

This is the main work file.

### Module 3: Weierstrass bridge

Create:

```text
FLT/RealTopology/WeierstrassRealComponents.lean
```

Contents:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import FLT.RealTopology.CubicLocusComponents
import FLT.RealTopology.CubicSign

namespace FLT

-- Complete square over ℝ:
--   (x,y) ↦ (x, 2*y + a1*x + a3)
-- and inverse.
-- Show this is a homeomorphism of affine loci.
-- Add the point at infinity to the unbounded component if the target is projective.

end FLT
```

Only this file should know about `WeierstrassCurve`.

---

## Minimal theorem to target first

The first theorem I would actually try to prove in Lean is not a cardinal theorem about connected components.  It is this path-component cover statement:

```lean
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace FLT

open Set
open scoped Topology

/--
First realistic target: under a three-root sign certificate, every point of the
real locus lies in one of two path components.
-/
theorem threeRoot_locus_pathComponent_cover
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hsign : ThreeRootSignPattern f) :
    ∃ A B : {p : ℝ × ℝ // p ∈ RealHyperellipticLocus f},
      ∀ P : {p : ℝ × ℝ // p ∈ RealHyperellipticLocus f},
        P ∈ pathComponent A ∨ P ∈ pathComponent B := by
  -- Choose `A = (r1,0)` and `B = (r3,0)` as subtype points.
  -- Use the bounded/unbounded path-connected subsets described above.
  sorry

end FLT
```

This avoids quotient cardinal arithmetic.  Once this is proved, converting it into “at most two connected components” is a small wrapper using:

```lean
pathComponent_subset_component
ZerothHomotopy.toConnectedComponents
ZerothHomotopy.toConnectedComponents_surjective
connectedComponent_eq_iff_mem
```

or whatever component-count notion the B-Line file already uses.

---

## Why this avoids manifold theory

The proof uses only:

```text
continuous images of intervals,
union of path-connected sets with a common point,
`y = ± sqrt(f x)` graph descriptions,
IVT to control signs,
finite root counting for cubics.
```

No tangent spaces, charts, smooth manifolds, Lie groups, or real algebraic geometry are needed for the component bound.

The only place where compactness/projective topology appears is if you insist on proving:

```text
each component is homeomorphic to S^1.
```

Do not make that part of the B-Line dependency.

---

## Bottom line

Among the three facts:

```text
1. cubic has 1 or 3 real roots,
2. real locus has 1 or 2 components,
3. each component is homeomorphic to S^1,
```

the Mathlib support ranking is:

```text
best support:      (2), after a sign-pattern hypothesis;
medium support:    (1), but the ordered sign-pattern theorem must be built;
weakest / avoid:   (3), because it needs projective compactification and explicit homeomorphisms.
```

The shortest elementary Lean path is therefore:

```text
prove topology from sign-pattern certificates first;
then prove nonsingular cubic sign-pattern certificates;
then bridge a real Weierstrass equation to the completed cubic;
do not prove homeomorphic-to-S^1 unless a later theorem truly needs it.
```
