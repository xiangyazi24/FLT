# Q1061 (dm1): `dm2` — exact-order induction for division-polynomial separability

The prompt body I received was only:

```text
Q1061 (dm1): dm2
```

I searched the repository for `Q1061` and `dm2` and found no matching task body.  I therefore interpret `dm2` as the second strategy from the earlier division-polynomial circularity discussion: **break the even/odd circularity by inducting on the exact order of the torsion point/root rather than on the syntactic index `n` or on parity.**

## Bottom line

The exact-order strategy is mathematically sound and it really does break the parity cycle, but in Lean it should not be implemented as a bare induction on `n` with an ad hoc root split.  The robust form is:

```text
Root of preΨ n
  → root has an exact torsion order d with d ∣ n
  → if d < n, reduce to the exact-order layer d
  → if d = n, prove primitive/simple directly
```

This avoids the circular dependency

```text
odd(n) → even(2n) → odd(n)
```

because the recursive call is always to the **exact order** `d < n`, never to `2n`.

However, this approach still needs a primitive-root/simple-root theorem.  In other words, exact-order induction does not eliminate the need for the formal tangent fact; it isolates it into the primitive case.

The right dependency graph is:

```text
Sep(n)
  ├─ nonprimitive root: exact order d < n → Sep(d) + transport from d to n
  └─ primitive root: tangent/differential of [n] gives simple root directly
```

So `dm2` is feasible, but only if you package the following two bridge lemmas:

```text
1. primitive exact-order roots are simple;
2. simple roots transport from exact order d to any multiple n.
```

## Why this breaks the old cycle

The parity proof got stuck because the odd case tried to prove `Sep(n)` by asking for `Sep(2n)`:

```text
OddSep(n)
  → EvenSep(2n)
  → Sep(n)
```

Exact-order induction never makes that move.  Given a root `x` of `preΨ n`, it asks for the smallest/exact torsion order `d` represented by `x`.  Then:

* if `d = n`, no induction is used; use the primitive tangent lemma;
* if `d < n`, recurse on `d`, which is genuinely smaller.

That is a well-founded graph.

## The key caveat: `preΨ d` separability is not enough by itself

Suppose `x` is a root of `preΨ d` and `d ∣ n`.  The induction hypothesis gives

```text
(preΨ d)'(x) ≠ 0.
```

But the goal is

```text
(preΨ n)'(x) ≠ 0.
```

To transfer this, you need a nonvanishing/disjointness theorem saying that the additional exact-order layers appearing in `preΨ n / preΨ d` do not vanish at `x`.

Conceptually this is true because a point cannot have two different exact orders.  But in Lean it must be an explicit lemma, not hidden inside a product-rule proof.

So the exact-order method needs a transport lemma of the following form:

```text
if d ∣ n and x has exact order d,
then simplicity of x as a root of preΨ d implies simplicity of x as a root of preΨ n.
```

This is the order-theoretic replacement for the fragile cofactor separability/disjointness branches.

## Recommended Lean-facing API

I would expose the exact-order strategy through a small polynomial-facing interface.  The point/order geometry can be hidden behind these statements.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Rootwise separability of a polynomial. -/
def RootwiseSep (P : K[X]) : Prop :=
  ∀ x : K, P.eval x = 0 → P.derivative.eval x ≠ 0

/-- Rootwise separability of the `n`th x-division polynomial. -/
def PreΨSep (n : ℕ) : Prop :=
  RootwiseSep (W.preΨ n)

/--
Polynomial-facing exact-order predicate.

`ExactOrderXRoot W d x` means that `x` comes from a point of exact order `d`.
In production, this should probably be defined through the point/order API rather
than by the minimal-polynomial-root condition below.  The predicate is kept
abstract here because the exact point type/base-change API is repository-specific.
-/
opaque ExactOrderXRoot : WeierstrassCurve K → ℕ → K → Prop

/-- Every root of `preΨ n` has some exact order `d` dividing `n`. -/
theorem exists_exactOrderXRoot_of_preΨ_root
    {n : ℕ} {x : K}
    (hx : (W.preΨ n).eval x = 0) :
    ∃ d : ℕ, d ∣ n ∧ ExactOrderXRoot W d x := by
  -- Use the point/root bridge:
  --   preΨ n root → point P above x with [n]P = 0,
  -- then set d := orderOf P.
  sorry

/-- Exact order represented by a fixed x-coordinate is unique. -/
theorem exactOrderXRoot_unique
    {d e : ℕ} {x : K}
    (hd : ExactOrderXRoot W d x)
    (he : ExactOrderXRoot W e x) :
    d = e := by
  -- If two points above the same x-coordinate are P and -P, they have the same
  -- order.  This is the order-theoretic disjointness lemma.
  sorry

/-- Primitive/exact-order roots are simple in their own layer. -/
theorem primitive_preΨ_derivative_ne_zero
    {d : ℕ} (hd_char : (d : K) ≠ 0) {x : K}
    (hx_exact : ExactOrderXRoot W d x) :
    (W.preΨ d).derivative.eval x ≠ 0 := by
  -- This is the local tangent input:
  -- the differential of `[d]` is multiplication by `(d : K)`, hence nonzero.
  sorry

/--
Simplicity transports from the exact-order layer `d` to any multiple `n`.

This replaces the cofactor nonvanishing branch of the parity proof.
-/
theorem derivative_ne_zero_of_exactOrder_dvd
    {d n : ℕ} (hdvd : d ∣ n) {x : K}
    (hx_exact : ExactOrderXRoot W d x)
    (h_simple_d : (W.preΨ d).derivative.eval x ≠ 0) :
    (W.preΨ n).derivative.eval x ≠ 0 := by
  -- Use factorization of `preΨ n` into exact-order layers, plus
  -- `exactOrderXRoot_unique` to show all other layers are nonzero at `x`.
  sorry

/-- If `d ∣ n` and `(n : K) ≠ 0`, then `(d : K) ≠ 0`. -/
theorem natCast_ne_zero_of_dvd
    {d n : ℕ} (hdvd : d ∣ n) (hn_char : (n : K) ≠ 0) :
    (d : K) ≠ 0 := by
  -- Over a field, if `n = d * q` and `d` vanished in `K`, then `n` would vanish.
  rcases hdvd with ⟨q, rfl⟩
  intro hd_zero
  apply hn_char
  simp [Nat.cast_mul, hd_zero]

/--
Exact-order proof of rootwise separability of `preΨ n`.

This theorem has no parity split and never calls the theorem for `2*n`.
-/
theorem preΨ_rootwiseSep_by_exactOrder
    {n : ℕ} (hn_char : (n : K) ≠ 0) :
    PreΨSep W n := by
  intro x hx
  rcases exists_exactOrderXRoot_of_preΨ_root (W := W) (n := n) (x := x) hx with
    ⟨d, hdvd, hx_exact⟩
  have hd_char : (d : K) ≠ 0 :=
    natCast_ne_zero_of_dvd (K := K) hdvd hn_char
  have h_simple_d : (W.preΨ d).derivative.eval x ≠ 0 :=
    primitive_preΨ_derivative_ne_zero (W := W) (d := d) hd_char hx_exact
  exact derivative_ne_zero_of_exactOrder_dvd
    (W := W) (d := d) (n := n) hdvd hx_exact h_simple_d

end WeierstrassCurve
```

This is the cleanest statement of the exact-order approach: the proof of `Sep(n)` no longer needs recursive parity induction at all.  It delegates all work to exact-order decomposition and primitive simplicity.

## If you want actual induction, use exact-order layers, not parity

The previous code actually avoids induction by proving primitive simplicity for every `d`.  If you want a literal induction, the induction should be over exact-order layers and should have this shape:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Schematic: a root of `preΨ n` either has exact order `n` or lower exact order. -/
theorem exactOrder_split
    {n : ℕ} {x : K}
    (hx : (W.preΨ n).eval x = 0) :
    ExactOrderXRoot W n x ∨
      ∃ d : ℕ, d ∣ n ∧ d < n ∧ ExactOrderXRoot W d x := by
  rcases exists_exactOrderXRoot_of_preΨ_root (W := W) (n := n) (x := x) hx with
    ⟨d, hdvd, hd_exact⟩
  by_cases hdn : d = n
  · subst hdn
    exact Or.inl hd_exact
  · have hdlt : d < n := by
      -- For positive torsion orders, `d ∣ n` and `d ≠ n` imply `d < n`.
      -- In production this needs the usual positivity side conditions.
      sorry
    exact Or.inr ⟨d, hdvd, hdlt, hd_exact⟩

/-- Strong-induction skeleton using exact order. -/
theorem preΨ_rootwiseSep_exactOrder_induction
    {n : ℕ} (hn_char : (n : K) ≠ 0) :
    PreΨSep W n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      rcases exactOrder_split (W := W) (n := n) (x := x) hx with hprim | hlower
      · have hsimple : (W.preΨ n).derivative.eval x ≠ 0 :=
          primitive_preΨ_derivative_ne_zero (W := W) (d := n) hn_char hprim
        exact hsimple
      · rcases hlower with ⟨d, hdvd, hdlt, hd_exact⟩
        have hd_char : (d : K) ≠ 0 :=
          natCast_ne_zero_of_dvd (K := K) hdvd hn_char
        have hSepD : PreΨSep W d := ih d hdlt hd_char
        -- The IH proves `preΨ d` is simple at roots of order `d`.
        -- Then transport that simplicity to `preΨ n`.
        have hd_root : (W.preΨ d).eval x = 0 := by
          -- follows from `ExactOrderXRoot W d x` via the root bridge
          sorry
        have hsimple_d : (W.preΨ d).derivative.eval x ≠ 0 := hSepD x hd_root
        exact derivative_ne_zero_of_exactOrder_dvd
          (W := W) (d := d) (n := n) hdvd hd_exact hsimple_d

end WeierstrassCurve
```

This induction is well-founded because the recursive call is on `d < n`.  It never proves an odd theorem by calling the even theorem for `2n`.

## What must be proved for this to work

The exact-order strategy depends on four nontrivial facts.

### 1. Root-to-torsion bridge

```text
(W.preΨ n).eval x = 0
  → there exists P above x with [n]P = 0
```

This may require working over an algebraic closure or a quadratic extension, because a root in the x-coordinate need not have a `K`-rational y-coordinate.

### 2. Exact-order uniqueness for an x-coordinate

If two points have the same x-coordinate, they are `P` and `-P`.  These have the same order.  Therefore the x-coordinate has a well-defined exact order.

This is what replaces many pairwise gcd/cofactor-disjointness arguments.

### 3. Primitive-root simplicity

If `x` comes from a point of exact order `d` and `(d : K) ≠ 0`, then `x` is a simple root of the primitive `d`-torsion layer.

This is where the tangent statement enters:

```text
d([d]) = d.
```

So the exact-order method does not avoid the tangent bridge.  It only confines it to the primitive case.

### 4. Transport from exact layer to `preΨ n`

If `d ∣ n`, the full division polynomial `preΨ n` contains the exact-order layer `d`.  Simplicity at that layer must remain simplicity in the product.  This requires showing no other exact-order layer also vanishes at `x`.

That follows from exact-order uniqueness.

## Comparison with the other strategies

### Compared with parity induction

Exact-order induction is better.  It has a genuinely decreasing measure: the exact order `d` of the point/root.

### Compared with strengthened cofactor induction

Exact-order induction is conceptually cleaner.  Cofactor nonvanishing is replaced by the statement that exact-order layers are disjoint.

### Compared with the direct tangent bridge

The direct tangent bridge is probably the shortest public API:

```lean
(n : K) ≠ 0 → RootwiseSep (W.preΨ n)
```

The exact-order method is a good internal proof architecture for that bridge, but it requires more point/order infrastructure.

## Recommendation

Use `dm2` as an internal architecture only if the project already has, or is about to add, the point/order bridge for roots of division polynomials.

The final exposed theorem should still be the simple polynomial-facing statement:

```lean
preΨ_rootwiseSep
  {n : ℕ} → (n : K) ≠ 0 → RootwiseSep (W.preΨ n)
```

Inside its proof, exact-order induction is a good way to avoid the old parity cycle:

```text
root of preΨ n
  → exact order d ∣ n
  → primitive case if d = n
  → smaller exact-order case if d < n
```

So the answer for `dm2` is:

```text
Yes, exact-order induction breaks the circularity,
but it requires two explicit bridge lemmas:
  primitive exact-order roots are simple,
  and exact-order simplicity transports to multiples.
It is Lean-feasible once the point/order/root API exists;
without that API, the direct tangent bridge is the faster route.
```
