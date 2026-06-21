# Q94: `preΨ'_separable` design — formal group vs resultant

## Executive verdict

The cleanest honest route to

```lean
(W.preΨ' n).Separable
```

for an elliptic Weierstrass curve `W/k` and `(n : k) ≠ 0` is **formal/local**, not a global resultant computation.

The mathematical primitive is:

```text
multiplication-by-n on E has invertible differential when (n : k) ≠ 0.
```

In local coordinates at the origin, with the standard formal parameter

```text
t = -x / y,
```

this is the statement that the formal `[n]`-series has linear coefficient `n`:

```text
[n](T) = n T + higher order terms.
```

When `(n : k) ≠ 0`, the linear coefficient is a unit, so `[n]` is étale at the origin. Translation moves this to every point, so the kernel `E[n]` is reduced. Since the `x`-map is unramified away from the two-torsion ramification points, and `preΨ'` is exactly the reduced/non-two-torsion `x`-factor of the division polynomial, the roots of `preΨ'` are simple.

The previous dual-number/projective-addition attempt failed for the right reason: the projective addition formula is not a good local coordinate at `(O,O)`. The formal group works in the completed local ring and avoids the basepoint indeterminacy.

## Current Mathlib status

Mathlib has:

```lean
Polynomial.Separable
Polynomial.separable_def
Polynomial.separable_map       -- or closely related map/descent lemmas
Polynomial.resultant
Polynomial.resultant_eq_zero_iff
Polynomial.isUnit_resultant_iff_isCoprime
Polynomial.discr
Polynomial.resultant_deriv
```

Mathlib also has a generic one-dimensional formal group API:

```lean
FormalGroup
FormalGroup.Point
```

in `Mathlib.RingTheory.FormalGroup.Basic`.

What Mathlib does **not** appear to have yet is:

```lean
WeierstrassCurve.formalGroup
WeierstrassCurve.formalParameter
WeierstrassCurve.nsmul_formal_linearCoeff
WeierstrassCurve.nsmul_etale_of_natCast_ne_zero
WeierstrassCurve.preΨ'_separable_of_nsmul_etale
```

So the right architecture is to keep `preΨ'_separable` as a named seam now, and discharge it later by building the Weierstrass formal group and the local transfer to the division polynomial.

## The downstream seam to expose now

This is the theorem downstream torsion-counting code should depend on.

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

/--
Main separability seam for the reduced/odd part of the division polynomial.

This is the exact theorem needed for the geometric `n`-torsion count.  It should eventually be
proved from formal étaleness of multiplication-by-`n` on the Weierstrass formal group.
-/
theorem preΨ'_separable
    {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Future proof route:
  -- 1. Base-change to `AlgebraicClosure k`.
  -- 2. Prove every geometric root of `W.preΨ' n` is simple.
  -- 3. Use `Polynomial.separable_map` / descent along the injective algebra map.
  --
  -- The currently missing primitive is the Weierstrass formal-group/local-divisor package.
  -- This theorem is intentionally the single named seam.
  admit

end WeierstrassCurve
```

For the geometric count over a separably closed field, a slightly more direct version is also useful:

```lean
namespace WeierstrassCurve

universe u

/-- Geometric version, usually the one used inside `n_torsion_card`. -/
theorem preΨ'_separable_geometric
    {k : Type u} [Field k] [IsSepClosed k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Future proof avoids descent/base-change and works directly with geometric roots.
  -- It still needs formal étaleness of `[n]` and the local transfer to the x-coordinate factor.
  admit

end WeierstrassCurve
```

## Formal-group route: theorem chain

The formal route should be built in layers. The following declarations are the intended API.

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/--
The Weierstrass formal group attached to `W`, using the standard parameter `t = -x/y` at `O`.

Missing Mathlib API.
-/
-- noncomputable def formalGroup : FormalGroup k := ...

/--
The formal `[n]`-series on the Weierstrass formal group has linear coefficient `n`.

This is the key local calculation.  It should ultimately be a generic formal-group lemma once
`W.formalGroup` is constructed and shown to have linear part `X + Y`.
-/
theorem formal_nsmul_linearCoeff
    (n : ℕ) :
    -- placeholder for: coefficient of `T` in the formal `[n]`-series equals `(n : k)`
    True := by
  -- Proof idea:
  -- * For any commutative one-dimensional formal group law `F(X,Y) = X + Y + terms of degree ≥ 2`,
  --   prove by induction that `[n]_F(T) = n*T + terms of degree ≥ 2`.
  -- * Specialize to the Weierstrass formal group.
  trivial

/-- Multiplication by `n` is étale when `(n : k) ≠ 0`. -/
theorem nsmul_etale_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    -- placeholder for: the morphism `[n] : E → E` is étale / has invertible differential
    True := by
  -- Proof idea:
  -- * At `O`, use `formal_nsmul_linearCoeff` and `hn`.
  -- * At arbitrary `P`, conjugate by translation: `[n]` commutes with translations up to a translate,
  --   so the differential has the same determinant.
  trivial

/-- The kernel of `[n]` is geometrically reduced when `(n : k) ≠ 0`. -/
theorem n_torsion_reduced_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    -- placeholder for: no nontrivial tangent vector lies in the scheme-theoretic kernel
    True := by
  -- Proof idea: reducedness of the fiber over `O` follows from étaleness of `[n]`.
  trivial

/--
The x-coordinate map is unramified away from two-torsion.

This is the local fact that the quotient map `E → E/{±1} ≃ P¹` ramifies exactly at the fixed
points of negation, i.e. the 2-torsion points.
-/
theorem x_unramified_of_not_two_torsion
    -- schematic arguments: a point `P`, hypothesis `(2 : ℕ) • P ≠ 0`
    : True := by
  -- Proof idea:
  -- * In affine coordinates, the two points over an x-coordinate are `P` and `-P`.
  -- * Ramification occurs precisely when `P = -P`, equivalently `2 • P = 0`.
  trivial

/--
Simple-root statement for `preΨ'`: each geometric root has nonzero derivative.

This is the concrete bridge from formal étaleness to polynomial separability.
-/
theorem derivative_preΨ'_eval_ne_zero_of_eval_eq_zero
    [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hx : (W.preΨ' n).eval x = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- Proof skeleton:
  -- 1. Use the root-realization theorem to choose a point `P` with x-coordinate `x`,
  --    `n • P = 0`, and `2 • P ≠ 0`.
  -- 2. `n_torsion_reduced_of_natCast_ne_zero hn` says the kernel is reduced at `P`.
  -- 3. `x_unramified_of_not_two_torsion` says the local x-coordinate is an étale parameter at `P`.
  -- 4. Therefore the local equation in the x-line cuts transversely, so the derivative of
  --    `preΨ' n` at `x` is nonzero.
  --
  -- Missing API: local rings / order of vanishing / divisor-to-polynomial multiplicity bridge
  -- specialized to Weierstrass curves.
  admit

/-- Separability from the simple-root derivative criterion over a separably closed field. -/
theorem preΨ'_separable_of_derivative_ne_zero_at_roots
    [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Standard polynomial API route:
  -- `Polynomial.Separable` is `IsCoprime f f.derivative`.
  -- Over a splitting/separably closed field, nonzero derivative at every root gives coprimality.
  -- Use existing `Polynomial.separable_def` and root-set/cardinality lemmas, or add a small helper:
  -- `Polynomial.separable_of_derivative_ne_zero_at_roots`.
  admit

end WeierstrassCurve
```

## Transfer from formal étaleness to `preΨ'` separability

The most delicate bridge is not the linear coefficient itself. It is the local-to-polynomial transfer:

```text
[n] étale + x unramified at non-2 torsion
⇒ the x-coordinate divisor of non-2 n-torsion has multiplicity one
⇒ every root of preΨ'_n is simple.
```

A good explicit seam is:

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k] [IsSepClosed k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/--
Local multiplicity bridge from reduced geometric torsion to squarefreeness of `preΨ'`.

This theorem is independent of the proof of étaleness. It only says that, once the geometric kernel
is reduced and `preΨ'` is known to be the non-2-torsion x-coordinate factor, roots of `preΨ'` have
multiplicity one.
-/
theorem preΨ'_simple_roots_of_n_torsion_reduced
    {n : ℕ} (hn : (n : k) ≠ 0) :
    ∀ x : k,
      (W.preΨ' n).eval x = 0 →
      (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- Needed ingredients:
  -- * root-realization for `preΨ'` roots;
  -- * no-common-root with `Ψ₂Sq` so roots are non-2-torsion;
  -- * reducedness of `E[n]` from `[n]` étale;
  -- * x-map unramified at non-2 torsion;
  -- * local multiplicity = polynomial derivative multiplicity for a root in A¹.
  admit

end WeierstrassCurve
```

This is the precise location where the earlier dual-number/projective attempt failed: it tried to compute the differential of `[n]` with a global addition formula instead of using the completed local group law.

## Resultant/discriminant route

The alternative is to prove a closed formula such as

```lean
resultant (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
  = unit * (n : k)^a * W.Δ^b * maybe powers of 2 and leading-coefficient factors
```

and then use Mathlib's generic resultant API.

The generic bridge is short:

```lean
import Mathlib

open Polynomial

namespace Polynomial

lemma separable_of_resultant_derivative_ne_zero
    {k : Type*} [Field k] {f : k[X]}
    (hf : f ≠ 0)
    (hres : f.resultant f.derivative ≠ 0) :
    f.Separable := by
  rw [Polynomial.separable_def]
  by_contra hcop
  have hz : f.resultant f.derivative = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl hf, hcop⟩
  exact hres hz

end Polynomial
```

Then the desired theorem would be:

```lean
namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Resultant seam for the reduced division polynomial. -/
theorem resultant_preΨ'_derivative_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).resultant (Polynomial.derivative (W.preΨ' n)) ≠ 0 := by
  -- This would require a closed discriminant/resultant formula for Mathlib's exact `preΨ'`
  -- normalization, including parity split and removed `Ψ₂Sq` factor.
  admit

theorem preΨ'_separable_via_resultant
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  exact Polynomial.separable_of_resultant_derivative_ne_zero
    (by
      -- existing degree API should provide this:
      -- `WeierstrassCurve.preΨ'_ne_zero W hn`
      exact WeierstrassCurve.preΨ'_ne_zero W hn)
    (W.resultant_preΨ'_derivative_ne_zero hn)

end WeierstrassCurve
```

This route is formally viable because Mathlib has `Polynomial.resultant`, `Polynomial.discr`, `Polynomial.resultant_deriv`, and `Polynomial.resultant_eq_zero_iff`. But it is not actually shorter unless one already has the exact normalized division-polynomial discriminant formula. Proving that formula from the EDS recursion is likely long and brittle: it must track the parity normalization of `preΨ'`, the removed `Ψ₂Sq` factor, powers of the discriminant, leading coefficients, and small exceptional indices.

## Recommendation

For the FLT/Mazur torsion work, the best scoping decision is:

1. Keep the downstream theorem named and narrow:

```lean
theorem WeierstrassCurve.preΨ'_separable
    {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

2. Use this seam to finish `n_torsion_card = n^2` and the rank-two geometric torsion structure.

3. Discharge the seam later through the formal group route:

```lean
WeierstrassCurve.formalGroup
→ formal_nsmul_linearCoeff
→ nsmul_etale_of_natCast_ne_zero
→ n_torsion_reduced_of_natCast_ne_zero
→ preΨ'_simple_roots_of_n_torsion_reduced
→ preΨ'_separable
```

4. Avoid the resultant route unless someone first produces a reliable paper formula for the exact `preΨ'` normalization used by Mathlib.

The single hardest missing Mathlib primitive is therefore:

```text
Weierstrass formal group + local order-of-vanishing bridge to the division polynomial.
```

Not the abstract polynomial separability API; that part is already available.
