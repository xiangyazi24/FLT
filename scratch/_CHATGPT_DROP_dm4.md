# Q2002 (dm4): Weil-pairing minimal route for the Mazur torsion-bound proof

## Executive answer

For the current axiom assembly, the best minimal route is **not** to formalize the full Weil pairing.  The right hard input is exactly the consequence already used by `TorsionBound.lean`:

```lean
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

This is the mathematically precise shortcut:

```text
E[m](ℚ) ≅ (ℤ/mℤ)^2  ==>  μ_m ⊂ ℚ*.
```

Then the existing elementary theorem

```lean
isPrimitiveRoot_rat_order_le_two : IsPrimitiveRoot ζ m → m ≤ 2
```

closes the only thing needed by `mazur_torsion_bound`.

In other words, the current axiom

```lean
axiom weil_pairing_primitive_root ...
```

is already the minimal useful interface.  I would only rename/re-document it so it is clear that this is **not** asking for a full formal Weil-pairing API.

## Recommended Lean interface

Replace or alias the existing axiom as follows.

```lean
/--
Minimal Weil-pairing consequence needed for Mazur's torsion-bound proof.

This is intentionally much weaker than a formal construction of the Weil pairing.
It packages only the standard consequence:
if all `m`-torsion points of `E/ℚ` are rational, then `ℚ` contains a primitive
`m`-th root of unity.

Geometrically, this is the determinant / exterior-square statement
`∧² E[m] ≃ μ_m`, together with trivial Galois action on rational `m`-torsion.
-/
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

/-- Backwards-compatible name for the old scaffold. -/
theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m :=
  full_rational_torsion_forces_primitive_root E hm hfull
```

Then `TorsionBound.lean` can stay essentially unchanged:

```lean
/-- If `E` has full rational `m`-torsion, then `m ≤ 2`. -/
theorem full_rational_torsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) : m ≤ 2 := by
  rcases full_rational_torsion_forces_primitive_root E hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ
```

If the goal is to minimize the axiom count even more aggressively, one could instead axiomatize the final numerical consequence:

```lean
axiom full_rational_torsion_order_le_two_input
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2
```

but I do **not** recommend this: it hides the clean split between the hard elliptic-curve input and the easy already-proved fact that `ℚ` has no primitive roots of unity of order `> 2`.

## Route (1): exterior power / determinant shortcut

This is the right conceptual explanation, but not a proof from pure group theory.

The true theorem is not merely about the abstract module `E[m] ≅ (ℤ/mℤ)^2`.  From pure finite-module data one only gets

```text
∧² E[m] ≅ ℤ/mℤ
```

after choosing an orientation/basis.  There is no canonical map from that abstract exterior power to `μ_m` without elliptic-curve geometry.

The geometric input is the canonical Galois-equivariant identification

```text
∧² E[m]  ≃  μ_m,
```

equivalently the Weil pairing

```text
e_m : E[m] × E[m] → μ_m.
```

If every point of `E[m]` is rational over `ℚ`, the Galois action on the left side is trivial.  Therefore the Galois action on `μ_m` is trivial, so all `m`-th roots of unity are rational.  In particular, there is a primitive `m`-th root in `ℚ`.

For Lean, the best minimal abstraction of this route is exactly the axiom above.  A slightly lower-level version would be:

```lean
axiom exterior_square_torsion_is_cyclotomic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} ... :
    -- Galois-equivariant determinant of `E[m]` is the cyclotomic character
```

but this would force you to build or import a Galois-action API, finite `ZMod m` modules, determinants, and `μ_m` as a Galois module.  That is probably more work than the current theorem-level axiom.

Verdict for route (1): **best mathematical explanation; axiomatize the final implication, not the full machinery.**

## Route (2): j-invariant / modular-polynomial / CM shortcut

I would not use this.

Reasons:

1. It is much heavier than the Weil-pairing consequence.
2. It is not the right theorem.  Full `m`-torsion over a field does **not** imply CM in general.  Take any non-CM elliptic curve and enlarge the base field to its `m`-division field; the full `m`-torsion becomes rational over that field, but the curve remains non-CM.
3. Over `ℚ`, the obstruction is precisely the cyclotomic determinant / Weil-pairing obstruction: if the mod-`m` Galois action is trivial, its determinant is trivial, but the determinant is the mod-`m` cyclotomic character.  This says `χ_m` is trivial, i.e. `μ_m ⊂ ℚ`.
4. Modular polynomials usually control cyclic isogenies (`X_0(m)`-type data), not full level structure (`X(m)` / ordered bases of `E[m]`).  Moving to full level structure reintroduces the same determinant/cyclotomic issue.

Verdict for route (2): **not a shortcut; likely much harder and conceptually indirect.**

## Route (3): Hasse-bound shortcut

This is a tempting idea, and a useful local sanity check, but it cannot prove the uniform theorem needed here.

What one can prove locally is:

```text
If p is a good prime for E and p ∤ m, and all E[m] points are rational,
then E[m] injects into E(𝔽_p), hence m^2 ∣ #E(𝔽_p).
```

Together with Hasse,

```text
#E(𝔽_p) ≤ p + 1 + 2*sqrt(p) = (sqrt(p)+1)^2,
```

so

```text
m ≤ sqrt(p) + 1.
```

This is only a **curve-dependent** bound, because it depends on having a small good prime `p` with `p ∤ m`.

To rule out `m ≥ 3`, one would like to use `p = 2` or `p = 3`, since

```text
p = 2 or 3 gives #E(𝔽_p) < 9,
```

contradicting `m^2 ≥ 9`.  But an elliptic curve over `ℚ` may have bad reduction at `2` and `3`.  For `m = 3`, the next prime `p = 5` already has Hasse upper bound bigger than `9`, so the simple inequality no longer contradicts full `3`-torsion.  For even `m`, one cannot use primes dividing `m`, and the remaining small primes can also be bad.

More generally, large primes do not force `m` small; the Hasse upper bound grows with `p`.  The sentence

```text
for large p this forces m small
```

is backwards for this application.  Large `p` gives a weaker numerical bound.

A conditional Lean lemma along this route would look like:

```lean
-- schematic, not intended to compile with current project names
axiom reduction_injective_on_prime_to_p_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m p : ℕ}
    (hp_good : GoodReduction E p)
    (hpm : Nat.Coprime p m)
    (hfull : HasFullRationalTorsion E m) :
    m ^ 2 ∣ Fintype.card (E_mod_p_points E p)

axiom hasse_bound_for_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp_good : GoodReduction E p) :
    Fintype.card (E_mod_p_points E p) ≤ p + 1 + 2 * Nat.sqrt p
```

But even with these heavy inputs, the universal `m ≤ 2` theorem does not follow without a uniform supply of suitably small good primes, which is false in this naive form.

Verdict for route (3): **formalizable as a conditional local bound, but not sufficient for Mazur's uniform full-torsion step.**

## The clean minimal replacement in `Axioms.lean`

The current file has:

```lean
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

I would rewrite only the name and docstring, not the mathematical content:

```lean
/--
Minimal Weil-pairing consequence.

This is the only Weil-pairing input needed for the torsion-bound theorem:
full rational `m`-torsion forces `ℚ` to contain a primitive `m`-th root of unity.
No divisor theory, Miller functions, explicit pairing construction, or bilinearity API
is needed downstream.
-/
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then either update `TorsionBound.lean` to use the new name, or keep the old name as a theorem alias.

## Bottom line

The shortest honest route is:

```text
AXIOM: full rational m-torsion over Q forces a primitive m-th root of unity in Q
PROVED: Q has primitive roots only for m ≤ 2
CONCLUDE: full rational m-torsion over Q implies m ≤ 2
```

This is exactly the amount of Weil-pairing theory needed by the Mazur axiom assembly.  Routes through CM/modular polynomials or Hasse bounds are not shorter and do not cleanly prove the required uniform implication.
