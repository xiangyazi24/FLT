# Q1914 (dm3): Weil-pairing bridge for full rational `m`-torsion

## Short answer

I do **not** find usable Mathlib infrastructure for the Weil pairing on elliptic curves.

What Mathlib does have is adjacent infrastructure:

* `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`: nonsingular affine points and their abelian group law;
* `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula`: explicit Jacobian-coordinate negation/doubling/addition formulae;
* `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`: division polynomials `ψₙ`, `φₙ`, etc.;
* `Mathlib.RingTheory.RootsOfUnity.*` and `Mathlib.NumberTheory.Cyclotomic.*`: `IsPrimitiveRoot`, roots of unity, and cyclotomic material.

I found no direct declaration/file for `WeilPairing`, `weilPairing`, or “Weil pairing” in Mathlib code search.  The lowercase `weil` hits I found are unrelated to elliptic-curve Weil pairing.  So the cleanest formalization path is **not** to axiomatize Mazur’s conclusion, but to axiomatize exactly the missing Weil-pairing consequence:

```text
full rational m-torsion on E/Q, with m ≥ 3,
implies the existence of ζ : ℚ with IsPrimitiveRoot ζ m.
```

Then your already-proved

```lean
isPrimitiveRoot_rat_order_le_two
```

closes the desired theorem immediately.

## Recommended axiom boundary

Do **not** axiomatize a vague statement like “`μ_m` is in `ℚ*`” unless you have already built a `μ_m` subgroup API.  In Lean, the most useful target is simply:

```lean
∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

This is exactly what your rational-roots-of-unity lemma consumes.  It is also the narrowest replacement point: when someone later formalizes the Weil pairing, only this one bridge axiom needs to be replaced.

I would include the hypothesis `3 ≤ m` in the bridge axiom.  Mathematically the Weil-pairing consequence works for positive `m`, but the proof of `m ≤ 2` only needs the bad case `m ≥ 3`; putting `3 ≤ m` in the axiom avoids uninteresting edge cases around `m = 0, 1, 2` and keeps the axiom minimal for the Mazur exclusion step.

## Drop-in Lean scaffold

This is intentionally generic in the elliptic-curve type and in the “full rational torsion” predicate, because your project’s actual definitions for elliptic curves over `ℚ` and `E[m](ℚ) = (ZMod m)^2` will determine those names.

```lean
import Mathlib

namespace MazurTorsionBridge

/--
Replace `ECQ` by your actual type of elliptic curves over `ℚ`, and replace
`FullRationalMTorsion E m` by your actual predicate saying that all `m`-torsion
is rational, equivalently that `E[m](ℚ)` is isomorphic to `(ZMod m) × (ZMod m)`.

This is the one missing Weil-pairing bridge:
if full `m`-torsion is rational over `ℚ`, then the Weil pairing on a rational
basis gives a primitive `m`-th root of unity in `ℚ`.
-/
axiom full_rational_m_torsion_gives_primitive_root
    {ECQ : Type*} {FullRationalMTorsion : ECQ → ℕ → Prop}
    {E : ECQ} {m : ℕ}
    (hm : 3 ≤ m)
    (hfull : FullRationalMTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

/--
Pure Lean wrapper: the only mathematical input is the bridge axiom above plus
the already-proved fact that `ℚ` has no primitive roots of unity of order `> 2`.

The argument is by contradiction.  If `m` is not `≤ 2`, then `3 ≤ m`; the
bridge axiom gives a primitive rational `m`-th root, and the rational-root lemma
forces `m ≤ 2`, contradiction.
-/
theorem full_rational_m_torsion_order_le_two_core
    {ECQ : Type*} {FullRationalMTorsion : ECQ → ℕ → Prop}
    {E : ECQ} {m : ℕ}
    (rat_no_primitive_roots :
      ∀ {ζ : ℚ} {n : ℕ}, IsPrimitiveRoot ζ n → n ≤ 2)
    (hfull : FullRationalMTorsion E m) :
    m ≤ 2 := by
  by_contra hnot
  have hm : 3 ≤ m := by omega
  rcases full_rational_m_torsion_gives_primitive_root
      (E := E) (m := m) hm hfull with ⟨ζ, hζ⟩
  have hm_le_two : m ≤ 2 := rat_no_primitive_roots hζ
  omega

end MazurTorsionBridge
```

## Version using your existing lemma name

Once your theorem

```lean
isPrimitiveRoot_rat_order_le_two
```

is imported, the final theorem should be this small.  Adjust only the names of `ECQ` and `FullRationalMTorsion` to match your codebase.

```lean
import Mathlib

namespace MazurTorsionBridge

-- Existing in your development:
-- theorem isPrimitiveRoot_rat_order_le_two
--     {ζ : ℚ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) : m ≤ 2 := ...

axiom full_rational_m_torsion_gives_primitive_root
    {ECQ : Type*} {FullRationalMTorsion : ECQ → ℕ → Prop}
    {E : ECQ} {m : ℕ}
    (hm : 3 ≤ m)
    (hfull : FullRationalMTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

theorem full_rational_m_torsion_order_le_two
    {ECQ : Type*} {FullRationalMTorsion : ECQ → ℕ → Prop}
    {E : ECQ} {m : ℕ}
    (hfull : FullRationalMTorsion E m) :
    m ≤ 2 := by
  exact full_rational_m_torsion_order_le_two_core
    (E := E) (m := m)
    (rat_no_primitive_roots := fun {ζ : ℚ} {n : ℕ} hζ =>
      isPrimitiveRoot_rat_order_le_two hζ)
    hfull

end MazurTorsionBridge
```

If your lemma is stated with the order argument first, for example

```lean
isPrimitiveRoot_rat_order_le_two (m := n) hζ
```

then only the lambda body changes:

```lean
(rat_no_primitive_roots := fun {ζ : ℚ} {n : ℕ} hζ =>
  isPrimitiveRoot_rat_order_le_two (m := n) hζ)
```

## More faithful but usually less convenient axiom

If your formalization already has rational `m`-torsion bases, you could axiomatize one level lower:

```lean
import Mathlib

namespace MazurTorsionBridge

/-- Placeholder type for your elliptic curves over `ℚ`. -/
variable {ECQ : Type*}

/-- Placeholder type for your rational points on a curve. -/
variable {Point : ECQ → Type*}

/-- Placeholder predicate: `P` is an `m`-torsion point. -/
variable (IsMTorsion : {E : ECQ} → Point E → ℕ → Prop)

/-- Placeholder predicate: `P,Q` form a `(ZMod m)^2` basis of `E[m]`. -/
variable (IsFullMTorsionBasis : {E : ECQ} → Point E → Point E → ℕ → Prop)

/--
Lower-level Weil-pairing axiom: evaluating the Weil pairing on a full torsion
basis produces a primitive rational `m`-th root of unity.
-/
axiom weil_pairing_on_rational_full_basis_is_primitive
    {E : ECQ} {m : ℕ} {P Q : Point E}
    (hm : 3 ≤ m)
    (hbasis : IsFullMTorsionBasis P Q m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

end MazurTorsionBridge
```

But unless you need to reason about individual torsion bases elsewhere, this is more ceremony than benefit.  For the Mazur exclusion step, the theorem-shaped axiom

```lean
FullRationalMTorsion E m → ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

is the cleanest cut.

## Bottom line

For the current project, I would add exactly one axiom/theorem placeholder:

```lean
axiom full_rational_m_torsion_gives_primitive_root
    {E : ECQ} {m : ℕ}
    (hm : 3 ≤ m)
    (hfull : FullRationalMTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then prove:

```lean
by_contra hnot
have hm : 3 ≤ m := by omega
rcases full_rational_m_torsion_gives_primitive_root hm hfull with ⟨ζ, hζ⟩
have hm_le_two : m ≤ 2 := isPrimitiveRoot_rat_order_le_two hζ
omega
```

This gives a small, auditable trusted kernel for the missing Weil-pairing input and leaves all rational-root-of-unity reasoning inside your existing Lean proof.
