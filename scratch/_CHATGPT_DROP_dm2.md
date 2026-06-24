# Q101 (dm2): Plan for general `preΨ'_separable_of_natCast_ne_zero`

Target:

```lean
theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

This is a route recommendation and dependency plan, not a full proof.

## Checked existing API at the pinned Mathlib revision

The following pieces are already present and should be treated as reusable, not reproved.

### Division-polynomial API exists

Import:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
```

Existing definitions and simp lemmas include:

```lean
W.Ψ₂Sq      : R[X]
W.Ψ₃        : R[X]
W.preΨ₄     : R[X]
W.preΨ' n   : R[X]
W.preΨ n    : R[X]

@[simp] lemma W.preΨ'_zero
@[simp] lemma W.preΨ'_one
@[simp] lemma W.preΨ'_two
@[simp] lemma W.preΨ'_three : W.preΨ' 3 = W.Ψ₃
@[simp] lemma W.preΨ'_four  : W.preΨ' 4 = W.preΨ₄

lemma W.preΨ'_even (m : ℕ) : ...
lemma W.preΨ'_odd  (m : ℕ) : ...

lemma W.preΨ_even (m : ℤ) : ...
lemma W.preΨ_odd  (m : ℤ) : ...
```

The exact recurrence in `Basic.lean` is:

```lean
lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2

lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 *
        (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 *
        (if Even m then 1 else W.Ψ₂Sq ^ 2)
```

Also present are the coordinate-ring congruences:

```lean
Affine.CoordinateRing.mk_ψ
Affine.CoordinateRing.mk_Ψ_sq
Affine.CoordinateRing.mk_φ
```

and the map/base-change lemmas:

```lean
map_Ψ₂Sq
map_Ψ₃
map_preΨ₄
map_preΨ'
map_preΨ
```

### Degree and leading-coefficient API exists

Import:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
```

Useful existing lemmas:

```lean
lemma W.natDegree_preΨ'_le (n : ℕ) : ...
lemma W.coeff_preΨ' (n : ℕ) : ...
lemma W.coeff_preΨ'_ne_zero {n : ℕ} (h : (n : R) ≠ 0) : ...
@[simp] lemma W.natDegree_preΨ' {n : ℕ} (h : (n : R) ≠ 0) : ...
@[simp] lemma W.leadingCoeff_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n
lemma W.preΨ'_ne_zero [Nontrivial R] {n : ℕ} (h : (n : R) ≠ 0) : W.preΨ' n ≠ 0
```

The degree file explicitly records the parity-dependent leading coefficient:

```text
preΨₙ has leading coefficient n/2 when n is even, and n when n is odd.
```

This is exactly the source of pain for a global resultant induction.

### Polynomial separability API exists

Import:

```lean
import Mathlib.FieldTheory.Separable
```

Existing facts:

```lean
def Polynomial.Separable (f : R[X]) : Prop := IsCoprime f (derivative f)

theorem Polynomial.separable_def  (f : R[X]) :
    f.Separable ↔ IsCoprime f (derivative f)

theorem Polynomial.separable_def' (f : R[X]) :
    f.Separable ↔ ∃ a b : R[X], a * f + b * derivative f = 1

theorem Polynomial.Separable.map {p : R[X]} (h : p.Separable) {f : R →+* S} :
    (p.map f).Separable

theorem Polynomial.Separable.eval₂_derivative_ne_zero ...
```

So once we have a Bezout identity, or a no-common-root/no-common-factor lemma that gives `IsCoprime`, the wrapper to `.Separable` is literally `Iff.rfl`.

### Formal-group API is too thin for the full geometric proof

Import:

```lean
import Mathlib.RingTheory.FormalGroup.Basic
```

Existing in Mathlib:

```lean
structure FormalGroup
class FormalGroup.IsComm
FormalGroup.Point
FormalGroup.𝔾ₐ
FormalGroup.𝔾ₘ
FormalGroup.map
```

Not present:

```text
formal group attached to a Weierstrass curve,
formal completion at O,
formal-group homomorphisms,
[n]-series,
height,
invariant differential,
isogenies,
étaleness/separable-degree of [n].
```

### Dual numbers exist, but do not solve the group-law problem alone

Import:

```lean
import Mathlib.Algebra.DualNumber
```

Existing:

```lean
DualNumber R = TrivSqZeroExt R R
DualNumber.eps
TrivSqZeroExt.inl / inr / fst / snd
DualNumber.lift
```

However, the nonsingular Jacobian point group law in Mathlib is currently over fields:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
```

`DualNumber k` is not a field, so the tempting proof “a multiple root gives a nonzero `k[ε]`-point in the kernel of `[n]`” does not plug directly into the existing point-group API.  The raw Jacobian formula polynomials are over a commutative ring, but the packaged nonsingular `Point` group is not.

That wrinkle is important for route selection.

## Executive recommendation

The mathematically clean reason the theorem is true is still:

```text
char(k) ∤ n  ⇒  d[n] is multiplication by n on the tangent line  ⇒  [n] is étale
  ⇒ E[n] is reduced  ⇒ the non-2-torsion x-coordinate polynomial preΨ'_n is squarefree.
```

But **do not build the full formal-group/isogeny/subgroup-scheme stack first**.  In this repository, the smaller Lean build is a **bespoke first-order/tangent version** of that argument, specialized to Weierstrass curves and the already-existing division-polynomial coordinate formulas.

The recommended proof should not be an induction on `preΨ'_even` / `preΨ'_odd` after differentiating the recurrence.  Use the recurrence and adjacent-Somos only for value-level root-exclusion lemmas.  Use a first-order differential/tangent lemma for the derivative.

In one sentence:

```text
Prove separability by excluding nonzero tangent vectors in the n-torsion root scheme, not by differentiating the EDS recurrence globally.
```

## 1. Formal group route: right concept, but not the minimal Lean build

### What the full formal-group route would require

A full route would be:

1. Construct the Weierstrass formal group `Ê` at `O` using a parameter, usually `t = -X/Y`.
2. Construct the formal `[n]`-series `[n]_Ê(T)`.
3. Prove

   ```text
   [n]_Ê(T) = n*T + higher terms.
   ```

4. If `(n : k) ≠ 0`, prove `[n]_Ê` is a formal automorphism by a one-variable formal inverse theorem.
5. Upgrade formal automorphism at `O` to `[n]` being étale at `O`.
6. Translate to every point of `ker [n]`, proving the kernel has no nonzero tangent vectors.
7. Convert reducedness of the non-2 part of the kernel to squarefreeness of `W.preΨ' n`.

This route is reusable and mathematically canonical.  But in current Mathlib, steps 1, 2, 4, 5, 6, and 7 are all essentially missing infrastructure.

### Minimal formal sub-theory actually needed

You do **not** need the full invariant differential or full isogeny theory if the target is only polynomial squarefreeness.  The minimal theorem needed from the formal group is just the first jet of `[n]`:

```lean
-- Schematic statement, not current API.
theorem tangent_nsmul_eq_natCast_smul
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    tangentMapAtO (fun P => n • P) = (n : k) • LinearMap.id := by
  -- first-order group law / formal parameter computation
  sorry
```

Equivalently, in formal series language:

```lean
-- Schematic statement, not current API.
theorem coeff_one_nseries
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    coeff 1 (formalNsmul W n) = (n : k) := by
  -- follows for any 1-dimensional formal group law whose linear term is X+Y
  sorry
```

This first-jet theorem is the only place `(n : k) ≠ 0` should enter.

### How formal automorphism connects to squarefree `preΨ'_n`

The rigorous connection is rootwise:

1. Work after base change to an algebraic closure or splitting field.
2. Suppose `a` is a multiple root of `F := W.preΨ' n`:

   ```lean
   F.eval a = 0
   F.derivative.eval a = 0
   ```

3. Use the root-to-point theorem for division polynomials to choose a non-2-torsion point `P` with `P.x = a` and `n • P = 0`.
4. Since the root is multiple, the infinitesimal displacement `x = a + ε` still satisfies `F = 0` to first order.
5. Because `P` is non-2-torsion, `ψ₂(P) = 2y + a₁x + a₃ ≠ 0`; therefore the curve equation solves uniquely for an infinitesimal `y = y₀ + ηε`.  This gives a nonzero tangent vector at `P` lying inside the infinitesimal zero-locus of `F`.
6. The division-polynomial root-to-torsion formula upgrades that tangent vector to a tangent vector in the kernel of `[n]`.
7. Translate it to a tangent vector at `O`.  The tangent map of `[n]` is multiplication by `(n : k)`, so this vector must be zero when `(n : k) ≠ 0`, contradiction.

This avoids proving a general theorem “`E[n]` is an étale finite group scheme”.  It proves exactly the needed local consequence.

## 2. Is there a slicker non-formal route?

### A pure EDS derivative induction is still the wrong main route

The tempting induction is:

```lean
P n := (n : k) ≠ 0 → (W.preΨ' n).Separable
```

But the induction hypotheses do not match the lower indices.  From

```lean
((2*m+1 : ℕ) : k) ≠ 0
```

one does not get

```lean
(m : k) ≠ 0,
((m+1 : ℕ) : k) ≠ 0,
((m+2 : ℕ) : k) ≠ 0,
...
```

in positive characteristic.  The differentiated odd recurrence contains all of those lower derivatives.  The even branch is worse because of the `Ψ₂Sq` factors and the `n/2` leading coefficient.

Also, squarefreeness of lower factors does not imply squarefreeness of a difference of products.  The derivative creates cancellation terms not controlled by adjacent coprimality.

### A Wronskian identity is useful, but not sufficient in all characteristics

There is a promising coordinate-ring identity behind the standard proof, schematically:

```text
D(Φ_n) * ΨSq_n - Φ_n * D(ΨSq_n) = n * preΨ_{2n}
```

or a parity-adjusted version.  This is the algebraic shadow of `[n]^*ω = nω`.  It is useful and should probably be proved eventually.

But by itself it is not enough for the target theorem.  Since

```text
ΨSq_n = (preΨ_n)^2 * (possibly Ψ₂Sq),
```

the identity sees the derivative of a square.  In characteristic `2`, this loses exactly the information needed to show `preΨ_n' ≠ 0` for odd `n`.  So the Wronskian must be supplemented by a `y`-coordinate/local-parameter argument, or replaced by the tangent argument above.

### An abstract cardinality argument is circular here

One might try:

```text
#E[n] = n²  ⇒ enough distinct roots ⇒ preΨ'_n squarefree.
```

But the project already uses the separability of `preΨ'_n` to prove the root count and then `#E[n] = n²`.  Therefore this route is circular unless an independent non-division-polynomial proof of `#E[n] = n²` is added.  That independent proof would itself amount to isogeny/formal-group infrastructure.

### Per-`n` Bezout/resultants work but do not scale

The proven `n=3` and `n=4` certificates are excellent base cases and regression tests.  They show the fixed-`n` E2 technique is sound.

For general `n`, though, a universal resultant induction would need to control:

```text
Res(preΨ'_n, derivative preΨ'_n)
leading coefficient n or n/2 depending on parity
positive-characteristic degree drops
normalization under `preΨ'_even` / `preΨ'_odd`
```

This is likely longer and more fragile than the tangent route.

## Recommended route: first-order tangent proof specialized to division polynomials

This is essentially the formal-group proof, but only its first-order consequence is implemented.

### Core theorem to aim for

First prove a rootwise derivative theorem over an algebraically closed or splitting field:

```lean
-- Proposed helper theorem.
theorem preΨ'_derivative_ne_zero_at_root
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0)
    {x : K}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- tangent/no-infinitesimal-kernel argument
  sorry
```

Then turn it into separability:

```lean
-- Proposed helper theorem, probably in a general polynomial file.
theorem Polynomial.separable_of_derivative_ne_zero_at_roots
    {K : Type*} [Field K] {f : K[X]}
    (h : ∀ x : K, f.eval x = 0 → f.derivative.eval x ≠ 0)
    (hsplit : f.Splits (RingHom.id K)) :
    f.Separable := by
  -- factor f as product of linear factors and use `separable_prod` / no duplicates,
  -- or use root multiplicity / `emultiplicity` API.
  sorry
```

For arbitrary `k`, either prove a descent lemma for coprimality under field extension, or phrase the rootwise theorem over a splitting field and descend from the gcd over `k`.

A practical descent lemma:

```lean
-- Proposed general algebra lemma.
theorem Polynomial.separable_of_map_separable
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [FaithfulSMul k K] {f : k[X]}
    (h : (f.map (algebraMap k K)).Separable) :
    f.Separable := by
  -- If f and f' had a nonunit gcd over k, its map would give a nonunit common divisor over K.
  -- Use Euclidean gcd / natDegree preservation under injective maps.
  sorry
```

Mathlib already has the forward direction:

```lean
Polynomial.Separable.map
```

but the descent direction may need to be added.

## Dependency DAG of new lemmas

The DAG below is the recommended build order.

```text
A. General polynomial / dual-number lemmas
│
├─ A1. eval_dual_eq_eval_add_derivative
│     p.eval (inl x + inr v)
│       = inl (p.eval x) + inr (v * p.derivative.eval x)
│
├─ A2. multiple_root_gives_nonzero_dual_root
│     f.eval x = 0 ∧ f.derivative.eval x = 0
│       ⇒ f.eval (inl x + ε) = 0
│
├─ A3. separable_of_no_multiple_roots_over_splitting_field
│
└─ A4. separability_descent_from_field_extension

B. Value-level division-polynomial root exclusions
│
├─ B1. preΨ'_root_not_Ψ₂Sq_root
│     [W.IsElliptic] → (n:k)≠0 → F_n(a)=0 → W.Ψ₂Sq.eval a ≠ 0
│
├─ B2. root_lifts_to_affine_point
│     over algebraically closed/splitting field, choose y with W(x,y)=0
│
├─ B3. non_two_root_has_unique_first_order_y_lift
│     ψ₂(P)≠0 solves the linearized curve equation uniquely
│
└─ B4. preΨ'_root_iff_non_two_n_torsion_x
      root of F_n ↔ x-coordinate of non-2 n-torsion point

C. First-order group/tangent lemmas
│
├─ C1. tangent_line_at_smooth_point
│     explicit first-order tangent equation for affine nonsingular point
│
├─ C2. tangent_translate_to_O
│     translation by -P identifies tangent at P with tangent at O
│
├─ C3. tangent_nsmul_at_O
│     derivative of nsmul at O is scalar `(n:k)`
│
├─ C4. tangent_nsmul_at_torsion_point
│     if n•P=0, derivative of nsmul at P is scalar `(n:k)` after translation
│
└─ C5. no_nonzero_tangent_in_kernel_of_nsmul
      (n:k)≠0 ⇒ tangent kernel is zero

D. Bridge from multiple roots to tangent kernel
│
├─ D1. multiple_root_of_preΨ'_gives_nonzero_tangent_vector
│
├─ D2. that tangent vector lies in kernel of tangent nsmul
│
└─ D3. contradiction by C5

E. Final theorem
│
├─ E1. preΨ'_derivative_ne_zero_at_root
├─ E2. map to splitting field / algebraic closure
├─ E3. descend separability
└─ E4. theorem preΨ'_separable_of_natCast_ne_zero
```

## Which parts are already available?

### Already available

```lean
-- Polynomial separability as coprime with derivative.
Polynomial.Separable
Polynomial.separable_def
Polynomial.separable_def'
Polynomial.Separable.map

-- Division polynomials and recurrences.
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₃
WeierstrassCurve.preΨ₄
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd

-- Base cases.
WeierstrassCurve.preΨ'_three
WeierstrassCurve.preΨ'_four

-- Coordinate-ring congruences.
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ

-- Map/base-change.
WeierstrassCurve.map_Ψ₂Sq
WeierstrassCurve.map_Ψ₃
WeierstrassCurve.map_preΨ₄
WeierstrassCurve.map_preΨ'
WeierstrassCurve.map_preΨ

-- Degree/leading coeff/nonzero.
WeierstrassCurve.natDegree_preΨ'
WeierstrassCurve.leadingCoeff_preΨ'
WeierstrassCurve.preΨ'_ne_zero

-- Nonsingular point group over fields.
WeierstrassCurve.Jacobian.Point.instAddCommGroup

-- Dual-number algebra, but not elliptic points over dual numbers.
DualNumber
DualNumber.eps
DualNumber.lift
```

### Missing and needed for the recommended route

```lean
-- General polynomial helpers.
Polynomial.eval_dual_eq_eval_add_derivative
Polynomial.separable_of_derivative_ne_zero_at_roots
Polynomial.separable_of_map_separable   -- descent across a field extension

-- Division-polynomial geometry/root dictionary.
preΨ'_root_not_Ψ₂Sq_root
preΨ'_root_iff_non_two_n_torsion_x
preΨ'_root_over_splitting_field_to_point

-- First-order/tangent group law.
WeierstrassCurve.tangent_at_affine_point
WeierstrassCurve.tangent_translate_to_O
WeierstrassCurve.tangent_nsmul_at_O
WeierstrassCurve.tangent_nsmul_at_torsion_point

-- Final bridge.
preΨ'_multiple_root_gives_nonzero_tangent_kernel_vector
preΨ'_derivative_ne_zero_at_root
```

## Lean skeleton for the recommended route

This is intentionally a skeleton: theorem names are proposed for new lemmas, while imports and existing namespaces are real.

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

open Polynomial
open scoped Polynomial DualNumber

namespace Polynomial

variable {k K : Type*} [Field k] [Field K]

/-- First-order Taylor expansion into dual numbers. -/
lemma eval_dual_eq_eval_add_derivative
    (f : k[X]) (x v : k) :
    f.eval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : DualNumber k) =
      TrivSqZeroExt.inl (f.eval x) +
        TrivSqZeroExt.inr (v * f.derivative.eval x) := by
  -- Polynomial.induction_on' f; simp [derivative_add, derivative_mul, derivative_X]
  sorry

/-- A field-extension descent lemma for polynomial separability. -/
lemma separable_of_map_separable
    [Algebra k K] [FaithfulSMul k K] {f : k[X]}
    (h : (f.map (algebraMap k K)).Separable) :
    f.Separable := by
  -- Contrapose using gcd or a nonunit common divisor over k;
  -- map it to K[X] and use natDegree preservation under injective coefficient map.
  sorry

/-- Rootwise criterion over a splitting field. -/
lemma separable_of_derivative_ne_zero_at_roots
    {f : k[X]}
    (hsplit : f.Splits (RingHom.id k))
    (hroot : ∀ x : k, f.eval x = 0 → f.derivative.eval x ≠ 0) :
    f.Separable := by
  -- Factor into linear terms, use `separable_prod` and no repeated roots,
  -- or use multiplicity/emultiplicity API.
  sorry

end Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k)

/-- Value-level exclusion: roots of the reduced n-division polynomial are non-2-torsion. -/
lemma preΨ'_root_not_Ψ₂Sq_root
    [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  -- Use adjacent-Somos/root-exclusion machinery plus the Q37/Q47 small Bezout certs.
  -- This layer is value-only; do not differentiate the recurrence here.
  sorry

/-- Root dictionary, non-2 part: preΨ'_n root corresponds to a non-2 n-torsion point. -/
lemma preΨ'_root_iff_non_two_n_torsion_x
    [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) {x : k} :
    (W.preΨ' n).eval x = 0 ↔
      ∃ P : W.Jacobian.Point, P.x = x ∧ W.Ψ₂Sq.eval x ≠ 0 ∧ n • P = 0 := by
  -- Use existing `mk_ψ`, `mk_Ψ_sq`, `mk_φ` and the multiplication formulas.
  -- If current point API exposes affine rather than Jacobian coordinates for x,
  -- state this with the available point projection.
  sorry

/-- First-order tangent statement: d[n] at O is scalar n. -/
lemma tangent_nsmul_at_O
    [W.IsElliptic] (n : ℕ) :
    tangentMapAtO W (fun P : W.Jacobian.Point => n • P) =
      (n : k) • LinearMap.id := by
  -- Prove by first-order expansion of the local group law at O.
  -- This is the minimal formal-group replacement.
  sorry

/-- Translate the tangent statement from O to an n-torsion point. -/
lemma tangent_nsmul_at_torsion_point
    [W.IsElliptic] {n : ℕ} {P : W.Jacobian.Point} (hP : n • P = 0) :
    tangentMapAt W P (fun Q : W.Jacobian.Point => n • Q) =
      (n : k) • LinearMap.id := by
  -- Translate by `-P`, use group law and `tangent_nsmul_at_O`.
  sorry

/-- A multiple root of preΨ'_n gives a nonzero tangent vector in the kernel of d[n]. -/
lemma preΨ'_multiple_root_gives_tangent_kernel
    [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0)
    (hdx : (Polynomial.derivative (W.preΨ' n)).eval x = 0) :
    ∃ P : W.Jacobian.Point, ∃ v : TangentAt W P,
      v ≠ 0 ∧ n • P = 0 ∧ tangentMapAt W P (fun Q : W.Jacobian.Point => n • Q) v = 0 := by
  -- 1. use root dictionary to get P;
  -- 2. use `preΨ'_root_not_Ψ₂Sq_root` to know x is a local parameter;
  -- 3. use the dual-number Taylor lemma to build a nonzero first-order root;
  -- 4. lift the y-coordinate using ψ₂(P) ≠ 0;
  -- 5. use division-polynomial formulas to show it is an infinitesimal n-torsion point.
  sorry

/-- Rootwise derivative nonvanishing. -/
theorem preΨ'_derivative_ne_zero_at_root
    [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  intro hdx
  obtain ⟨P, v, hv_ne, hP, hv⟩ :=
    W.preΨ'_multiple_root_gives_tangent_kernel hn hx hdx
  have htangent := W.tangent_nsmul_at_torsion_point hP
  -- `htangent` rewrites `hv` to `(n:k) • v = 0`; since `(n:k) ≠ 0`, v=0.
  exact hv_ne (by
    -- linear algebra over field
    sorry)

/-- Final theorem. -/
theorem preΨ'_separable_of_natCast_ne_zero
    [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Map to a splitting field / algebraic closure, apply the rootwise theorem there,
  -- then descend separability to k.
  -- Small n close by simp; n=0 impossible from hn.
  sorry

end WeierstrassCurve
```

## How to use the already-proven `n=3` and `n=4` certs

Keep the explicit Bezout certificates for:

```lean
W.preΨ' 3 = W.Ψ₃
W.preΨ' 4 = W.preΨ₄
```

They are still valuable as:

1. base cases for value-level root exclusion;
2. regression tests for the final theorem;
3. fallback lemmas when adjacent-Somos degenerates into the `Ψ₂Sq`, `Ψ₃`, `preΨ₄` stratum.

But do not extrapolate them into a general resultant proof unless the tangent route fails.

## Risk estimate

### Full formal-group / isogeny route

Estimated size: very large, probably several thousand lines before touching `preΨ'`.

Missing components:

```text
Weierstrass formal group,
[n]-series,
formal inverse theorem,
formal/scheme étaleness bridge,
finite subgroup-scheme reducedness,
connection to x-coordinate divisor.
```

Verdict: mathematically best long-term infrastructure, but not the smallest path for this theorem.

### Recurrence + differentiated EDS induction

Estimated size: large and brittle.

Main failures:

```text
lower index casts do not follow from `(n:k)≠0`,
product-rule expansion creates cancellation terms,
positive characteristic causes degree/derivative normalization failures,
char 2 loses information from derivative of squared denominators.
```

Verdict: avoid as the main proof.

### Recommended first-order/tangent route

Estimated size: medium-large but targeted.

Likely new code:

```text
~100-200 lines: general polynomial dual-number/Taylor/separability helpers
~300-600 lines: value-level root exclusion and non-2 root lemmas using Somos + Q37/Q47 certs
~400-900 lines: first-order tangent/addition/nsmul lemmas for Weierstrass points
~200-400 lines: root-to-tangent-kernel bridge and final theorem
```

Total rough estimate: `1000-2000` Lean lines, with most of the hard work reusable for later torsion/isogeny facts.

Verdict: best tradeoff.  It implements exactly the geometric reason for separability without building all of isogeny theory.

## Final recommendation

Build the proof around this lemma first:

```lean
theorem preΨ'_derivative_ne_zero_at_root
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0
```

Do not start with a global `IsCoprime` proof.  Once this rootwise lemma is proven, the final `.Separable` theorem is a standard polynomial wrapper.

Use formal-group language as the mathematical guide, but implement only the first-order/tangent pieces needed for the contradiction.  The full formal group at `O` is not necessary unless the project wants reusable isogeny infrastructure beyond this separability brick.
