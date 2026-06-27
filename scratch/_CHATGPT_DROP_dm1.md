# Q1025 (dm1): `dm4` — use a tangent bridge as the real cycle breaker

The prompt body I received was only:

```text
Q1025 (dm1): dm4
```

I searched the repository for `Q1025` and `dm4` and found no matching task body.  I therefore interpret `dm4` as the natural next step after the earlier even/odd circularity and `dm3` strengthened-induction discussion: whether the **formal-group / tangent bridge** should be used to bypass the parity induction and prove separability of the division polynomial directly.

## Bottom line

For Lean 4, the most robust non-circular architecture is:

```text
formal tangent of [n]
  ⇒ n-torsion kernel is reduced when (n : K) ≠ 0
  ⇒ the division-polynomial root cutout is reduced
  ⇒ every root of preΨ n is simple
  ⇒ no parity induction is needed for separability
```

This is the cleanest way to break the loop

```text
odd(n) → even(2n) → odd(n).
```

The important implementation point is: **do not try to thread the formal-group proof through the existing even/odd recurrence proof.**  Instead, add one bridge theorem with a narrow polynomial-facing API, then make both odd and even separability call that theorem.

## Recommended theorem interface

The parity files should depend on a theorem with this shape:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Rootwise separability of a polynomial. -/
def RootwiseSep (P : K[X]) : Prop :=
  ∀ x : K, P.eval x = 0 → P.derivative.eval x ≠ 0

/--
Polynomial-facing tangent bridge for division polynomials.

This is the theorem that should hide the point/formal-group geometry.  Do not
prove it by calling the even/odd recurrence; prove it from the tangent of `[n]`.
-/
theorem preΨ_rootwiseSep_of_tangent
    {n : ℕ} (hn : (n : K) ≠ 0) :
    RootwiseSep (W.preΨ n) := by
  intro x hx
  -- Geometry hidden behind this theorem:
  -- 1. lift the root `x` to a point `P` above `x` over a splitting field or
  --    algebraic closure;
  -- 2. use the division-polynomial root bridge to get `[n] P = 0`;
  -- 3. use that the differential of `[n]` is multiplication by `(n : K)`;
  -- 4. since `(n : K) ≠ 0`, the local equation of the kernel is reduced;
  -- 5. descend reducedness/simple-root information back to the x-polynomial.
  sorry

end WeierstrassCurve
```

The rest of the current separability development should treat this as the main theorem.  That keeps the recurrence lemmas from becoming part of the proof of the bridge, which would recreate the circularity.

## Why this breaks the circularity

The old proof graph was:

```text
Sep(2k) uses Sep(k) and CofactorGood(k)
Sep(2k+1) tries to use Sep(2(2k+1))
Sep(2(2k+1)) uses Sep(2k+1)
```

So the odd case depends on itself through the even case.

With the tangent bridge, the graph becomes:

```text
Sep(n)
  ← preΨ_rootwiseSep_of_tangent(hn)
      ← differential([n]) = n
      ← (n : K) ≠ 0
```

There is no recursive call to `Sep(n)`, `Sep(2n)`, or any cofactor statement.

## The right internal bridge decomposition

Do not attempt to prove the whole bridge in one giant theorem.  Split it into four lemmas.  The names below are schematic; the point is the dependency graph.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Placeholder for the point type used by the existing elliptic-curve API. -/
opaque ECPoint : Type _

/-- Placeholder for the x-coordinate map. -/
opaque xCoord : ECPoint (W := W) → K

/-- Placeholder for scalar multiplication by `n`. -/
opaque smulPoint : ℕ → ECPoint (W := W) → ECPoint (W := W)

/-- Placeholder for the identity point. -/
opaque zeroPoint : ECPoint (W := W)

/-- Root of `preΨ n` gives an `n`-torsion point above that x-coordinate. -/
theorem exists_torsion_point_of_preΨ_root
    {n : ℕ} {x : K}
    (hx : (W.preΨ n).eval x = 0) :
    ∃ P : ECPoint (W := W),
      xCoord (W := W) P = x ∧
      smulPoint (W := W) n P = zeroPoint (W := W) := by
  sorry

/-- The tangent map of `[n]` is multiplication by `(n : K)`. -/
theorem tangent_mulBy_eq_natCast
    {n : ℕ} (P : ECPoint (W := W)) :
    True := by
  -- Replace `True` by the actual differential statement available in the
  -- chosen formal-group/local-ring API.
  trivial

/-- If `(n : K) ≠ 0`, the local kernel of `[n]` is reduced at an `n`-torsion point. -/
theorem torsion_kernel_reduced_at
    {n : ℕ} (hn : (n : K) ≠ 0)
    {P : ECPoint (W := W)}
    (hP : smulPoint (W := W) n P = zeroPoint (W := W)) :
    True := by
  -- This is where `tangent_mulBy_eq_natCast` is used.
  trivial

/-- Reducedness of the torsion kernel descends to a simple root of `preΨ n`. -/
theorem preΨ_simple_root_of_kernel_reduced
    {n : ℕ} {x : K}
    (hx : (W.preΨ n).eval x = 0)
    (hred : True) :
    (W.preΨ n).derivative.eval x ≠ 0 := by
  -- Replace `True` by the actual reducedness statement.
  -- This is the only place that should know how the x-division polynomial cuts
  -- out the quotient of nonzero n-torsion by `P ↦ -P`.
  sorry

/-- The assembled polynomial-facing theorem. -/
theorem preΨ_rootwiseSep_of_tangent_bridge
    {n : ℕ} (hn : (n : K) ≠ 0) :
    ∀ x : K, (W.preΨ n).eval x = 0 → (W.preΨ n).derivative.eval x ≠ 0 := by
  intro x hx
  rcases exists_torsion_point_of_preΨ_root (W := W) (n := n) (x := x) hx with
    ⟨P, hxP, htor⟩
  have hred : True := torsion_kernel_reduced_at (W := W) (n := n) hn htor
  exact preΨ_simple_root_of_kernel_reduced (W := W) (n := n) (x := x) hx hred

end WeierstrassCurve
```

The `opaque` placeholders above are not meant as final production definitions.  They show the **shape** of the dependency boundary.  In the real file, replace them with the actual point type, scalar multiplication, identity point, and tangent/local-ring API available in the development.

## What must be handled carefully

### 1. Work over an algebraic closure if necessary

A root `x : K` of the x-division polynomial does not always come with a `K`-rational point above it.  The corresponding `y` may live in a quadratic extension.  The bridge should therefore be phrased either:

```text
rootwise over an algebraic closure, then descend derivative nonvanishing to K
```

or:

```text
use the coordinate ring/local algebra directly, avoiding explicit rational points
```

The algebraic-closure route is often easier conceptually, but it can create more Lean coercion/base-change work.

### 2. The x-coordinate quotient has a ramification issue at 2-torsion

The map

```text
P ↦ x(P)
```

identifies `P` and `-P`.  Away from 2-torsion, this is an étale quotient.  At 2-torsion, it is ramified, so the descent from point-level reducedness to x-polynomial simple roots needs a small separate argument.

This is not a reason to abandon the tangent bridge.  It just means the final descent lemma should explicitly split:

```text
P ≠ -P      -- ordinary ± pair
P = -P      -- 2-torsion branch
```

For even `n`, the 2-torsion branch is unavoidable.  It is also exactly where trying to reason only by parity recurrences tends to become messy.

### 3. Keep characteristic hypotheses explicit

The bridge requires the separability condition:

```lean
(n : K) ≠ 0
```

or equivalently, in characteristic language:

```text
char(K) ∤ n.
```

Use `(n : K) ≠ 0` in the polynomial theorem.  It is the most convenient Lean-facing hypothesis because it is exactly what the tangent multiplier needs.

### 4. Do not make cofactor lemmas prerequisites of the tangent theorem

The tangent theorem should not depend on:

```text
Sep(k)
CofactorSep(k)
Sep(2k)
Sep(2k+1)
```

Otherwise the proof graph can silently reintroduce the same cycle.

The cofactor work remains useful as a recurrence-level check, but not as the foundation of separability.

## How to refactor the current parity proof

Once the bridge theorem exists, the parity proof can become a wrapper rather than an induction.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Rootwise separability of a polynomial. -/
def RootwiseSep (P : K[X]) : Prop :=
  ∀ x : K, P.eval x = 0 → P.derivative.eval x ≠ 0

/-- This is the only theorem the old parity layer should call. -/
theorem preΨ_rootwiseSep
    {n : ℕ} (hn : (n : K) ≠ 0) :
    RootwiseSep (W.preΨ n) := by
  -- Replace by the actual bridge theorem once proved/imported.
  exact preΨ_rootwiseSep_of_tangent_bridge (W := W) (n := n) hn

/-- Even case is now just a specialization, not an induction step. -/
theorem preΨ_rootwiseSep_even
    {k : ℕ} (hk : ((2 * k : ℕ) : K) ≠ 0) :
    RootwiseSep (W.preΨ (2 * k)) := by
  exact preΨ_rootwiseSep (W := W) (n := 2 * k) hk

/-- Odd case is now just a specialization, not a reduction to `2n`. -/
theorem preΨ_rootwiseSep_odd
    {k : ℕ} (hk : (((2 * k + 1 : ℕ) : K)) ≠ 0) :
    RootwiseSep (W.preΨ (2 * k + 1)) := by
  exact preΨ_rootwiseSep (W := W) (n := 2 * k + 1) hk

end WeierstrassCurve
```

This is the key design change: the odd theorem no longer calls the even theorem for `2n`.

## If you still want a polynomial-only fallback

If the tangent bridge is too large for the current stage of the development, the polynomial-only fallback is:

```text
1. keep the dm3 target-bound ledger for the even cofactor branch;
2. prove a direct odd recurrence step;
3. never prove odd(n) via even(2n).
```

The fallback dependency graph must look like:

```text
Sep(2k)     ← Sep(k) + CofactorGood(k)
Sep(2k+1)   ← Sep(j) for j < 2k+1 via the odd recurrence
```

not like:

```text
Sep(2k+1) ← Sep(2(2k+1)).
```

## Final recommendation

For `dm4`, I would implement the formal tangent bridge as a single polynomial-facing theorem first, even if its proof is initially a `sorry`:

```lean
preΨ_rootwiseSep_of_tangent
  {n : ℕ} → (n : K) ≠ 0 → RootwiseSep (W.preΨ n)
```

Then refactor the existing odd/even separability statements to call that theorem.  This immediately removes the circular proof graph.  After that, fill the bridge internally using point lifting, the differential of `[n]`, reducedness of the torsion kernel, and descent from point-level reducedness to the x-division polynomial.
