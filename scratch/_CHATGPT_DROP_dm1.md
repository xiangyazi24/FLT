# Q1078 (dm1): avoiding full Weil pairing for full rational torsion over `ℚ`

## Executive answer

The shortest Lean path is **not** to try to construct a rational primitive root for `m ≥ 3`.  Over `ℚ`, such a root cannot exist.  Instead, prove a contradiction from `hfull`:

```text
HasFullRationalTorsion E m  →  m ≤ 2.
```

Then the theorem is finished by the already-handled `m = 1` and `m = 2` cases.

The smallest useful missing lemma is therefore:

```lean
fullRationalTorsion_order_le_two
  (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} :
  0 < m → HasFullRationalTorsion E m → m ≤ 2
```

or equivalently:

```lean
not_hasFullRationalTorsion_of_three_le
  (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} :
  3 ≤ m → ¬ HasFullRationalTorsion E m
```

This is a much better target than a full formalization of the Weil pairing.  It also avoids the awkward fixed-field descent step “a primitive root in `AlgebraicClosure ℚ` fixed by Galois is actually in `ℚ`”.

## Why `isPrimitiveRoot_rat_order_le_two` alone does not solve it

The lemma

```lean
isPrimitiveRoot_rat_order_le_two
```

is useful only **after** you already have a rational primitive root.  But your theorem is trying to produce such a root from `hfull`.

For `m ≥ 3`, the conclusion is false, so Lean needs to prove that the assumptions are contradictory.  The impossible-conclusion lemma does not by itself give:

```lean
¬ HasFullRationalTorsion E m
```

You still need the mathematical obstruction from full rational torsion to `m ≤ 2`.

## Best conceptual shortcut: determinant at complex conjugation

The determinant route is the right abstraction, but specialize it as much as possible.

The full standard statement is:

```text
det ρ_m = cyclotomic character ε_m.
```

If `E[m] ⊆ E(ℚ)`, then the mod-`m` Galois representation is trivial, hence `det ρ_m` is trivial.  Therefore the cyclotomic character is trivial.

For the present theorem over `ℚ`, you do not need to build all of `μ_m ⊆ ℚ`.  It is enough to evaluate at complex conjugation.  Complex conjugation acts on roots of unity by inversion, so its cyclotomic character is `-1`.  Triviality gives

```text
-1 = 1 in (ZMod m)ˣ,
```

hence `m ∣ 2`, hence, with `0 < m`,

```text
m ≤ 2.
```

So the ideal hard lemma is not a full Weil-pairing API.  It is this targeted obstruction:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
Project-specific abbreviation, shown only to document the intended shape.
Use the actual FLT definition instead of redefining it if it already exists.
-/
abbrev HasFullRationalTorsion_Schematic
    (E : WeierstrassCurve ℚ) (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E.Point), Function.Injective f

/--
The minimal obstruction needed for the main theorem.

Mathematical proof idea:

1. `hfull` gives `m²` rational `m`-torsion points.
2. In characteristic zero, geometric `E[m]` has exactly `m²` points.
3. Hence all geometric `m`-torsion is rational, so the mod-`m` Galois
   representation is trivial.
4. The determinant of the mod-`m` representation equals the cyclotomic
   character.
5. At complex conjugation, the cyclotomic character is `-1`.
6. Triviality gives `-1 = 1 mod m`, so `m ∣ 2`; since `0 < m`, `m ≤ 2`.

This is much smaller than exposing a general Weil pairing, nondegeneracy,
and Galois-equivariance interface to the rest of the project.
-/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  -- Recommended single remaining hard lemma.
  -- Prove this later either from a determinant/cyclotomic theorem, or from a
  -- still more specialized complex-conjugation determinant theorem.
  sorry

end FLT
```

The final theorem then becomes only casework on `m ≤ 2`.

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
Skeleton for the final theorem once the two base cases and the obstruction lemma
are available.

Replace `primitiveRoot_rat_one` and `primitiveRoot_rat_two` by the names of the
base-case lemmas already present in FLT.
-/
theorem weil_pairing_gives_primitive_root_skeleton
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m)
    -- already handled in the project:
    (primitiveRoot_rat_one : IsPrimitiveRoot (1 : ℚ) 1)
    (primitiveRoot_rat_two : IsPrimitiveRoot (-1 : ℚ) 2) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  have hm_le_two : m ≤ 2 :=
    fullRationalTorsion_order_le_two (E := E) (m := m) hm hfull
  have hm_cases : m = 1 ∨ m = 2 := by
    omega
  rcases hm_cases with rfl | rfl
  · exact ⟨1, primitiveRoot_rat_one⟩
  · exact ⟨-1, primitiveRoot_rat_two⟩

end FLT
```

That is the shortest clean architecture: the final theorem should never enter the `m ≥ 3` branch except to contradict `hfull`.

## Answer to option 1: determinant of the mod-`m` Galois representation

Conceptually yes.  In fact, this is the best abstraction:

```text
det ρ_m = ε_m.
```

But in Lean/Mathlib terms, this is not currently a free theorem you can just import and apply.  Even if `WeierstrassCurve.galoisRep` and `WeierstrassCurve.nTorsion` exist in the project/Mathlib layer, the hard missing theorem is exactly the determinant/cyclotomic compatibility.

The determinant theorem is usually proved from the Weil pairing.  So if you formalize

```lean
det_galoisRep_eq_cyclotomic
```

from scratch, you have not really avoided the Weil pairing; you have merely hidden it behind a determinant API.

However, for this FLT theorem you can shrink the needed determinant theorem to the complex-conjugation obstruction:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
A very narrow replacement for the full theorem `det ρ_m = cyclotomic`.
It says: if all `m`-torsion is rational, then complex conjugation would have to
act trivially on `E[m]`; but determinant/cyclotomic says its determinant is `-1`.
-/
theorem fullRationalTorsion_order_le_two_via_complex_conjugation
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  -- This is the recommended theorem to isolate if you want fewer moving parts
  -- than a complete Weil-pairing development.
  sorry

end FLT
```

This is strictly less surface area than proving and exposing:

```text
Weil pairing definition
bilinearity
alternating property
nondegeneracy
Galois equivariance
identification with μ_m
fixed-field descent to ℚ
```

## Answer to option 2: structure of `E(ℚ)_tors`

Plain finiteness of torsion does **not** help.

From

```text
ZMod m × ZMod m ↪ E(ℚ)
```

you get at least `m²` rational torsion points.  Finiteness only says the torsion subgroup is finite, not that its size is bounded independently of `E`.

A uniform **classification** would help.  Mazur's torsion theorem would immediately rule out `(ZMod m)^2` for every `m ≥ 3`, because the rational torsion subgroup is one of:

```text
Z/nZ,              n = 1, ..., 10, or 12
Z/2Z × Z/2nZ,      n = 1, ..., 4
```

and none of those contains `(Z/mZ)^2` for `m ≥ 3`.

But this is not a shorter Lean path unless Mazur's theorem is already formalized in your project.  A mere cardinality bound is also not enough unless it is very sharp: for example, an order bound allowing `9` or `16` torsion points would not by itself rule out `(Z/3Z)^2` or `(Z/4Z)^2`; you need the group-structure classification.

There is also a nice real-topological obstruction:

```text
E(ℚ)[m] ⊆ E(ℝ)[m],
#E(ℝ)[m] ≤ 2m,
```

whereas full rational `m`-torsion gives `m²` points.  Thus `m² ≤ 2m`, so `m ≤ 2`.  This avoids cyclotomic fields entirely.  Unfortunately it requires formalizing the topology/Lie group structure of real elliptic curves, which is not a short Mathlib route at present.

## Answer to option 3: class field theory, Kronecker-Weber, or Néron-Ogg-Shafarevich

No.  This is much heavier and still does not remove the key missing link.

Kronecker-Weber classifies abelian extensions of `ℚ`; it does not by itself say that full rational elliptic `m`-torsion forces `ℚ(ζ_m)` to appear.  The theorem that creates that link is again the determinant/cyclotomic compatibility, equivalently the Weil pairing package.

Néron-Ogg-Shafarevich is also the wrong hammer here.  It controls ramification of torsion representations from reduction behavior.  It does not directly prove that full rational `m`-torsion implies rational `m`th roots of unity without the same determinant/cyclotomic input.

So the class-field-theory route is not shorter in Lean.  It is both mathematically overkill and far less likely to be available as an importable Mathlib theorem.

## Answer to option 4: `galoisRep`, `nTorsion`, and `IsPrimitiveRoot.autToPow`

These are the right pieces, but they do not automatically close the theorem.

The desired wiring would be:

```text
hfull
  → all of E[m] is rational
  → ρ_m is trivial
  → det ρ_m is trivial
  → cyclotomic character is trivial
  → complex conjugation acts trivially on μ_m
  → -1 = 1 mod m
  → m ≤ 2
```

`IsPrimitiveRoot.autToPow` is useful for expressing the cyclotomic character once a primitive root in an extension has been chosen.  But the missing bridge is still:

```lean
det (WeierstrassCurve.galoisRep E m σ) = cyclotomicCharacter m σ
```

or its complex-conjugation specialization.

If `WeierstrassCurve.galoisRep` is currently defined with `sorry`, then using it may be acceptable inside FLT, but the determinant theorem will be another serious theorem unless you also take it as a project-local lemma.  It is still much smaller to localize the hard input as:

```lean
fullRationalTorsion_order_le_two
```

rather than formalizing the whole Weil pairing API.

## Recommended final implementation plan

Use the following dependency shape:

```text
main theorem
  ├─ m = 1 base case, already done
  ├─ m = 2 base case, already done
  └─ m ≥ 3 branch:
       exact False.elim (not_hasFullRationalTorsion_of_three_le E hm3 hfull)
```

Add exactly one project-local hard lemma:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
No elliptic curve over `ℚ` has full rational `m`-torsion for `m ≥ 3`.

Preferred eventual proof: determinant of the mod-`m` Galois representation at
complex conjugation, or equivalently the minimal Weil-pairing consequence.
-/
theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_pos : 0 < m := by omega
  have hm_le_two : m ≤ 2 :=
    fullRationalTorsion_order_le_two (E := E) (m := m) hm_pos hfull
  omega

/--
Final theorem shape using only the obstruction lemma plus the already-proved
`m = 1` and `m = 2` cases.
-/
theorem weil_pairing_gives_primitive_root_final_shape
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m)
    -- Replace these two hypotheses by the actual base-case lemmas in FLT.
    (primitiveRoot_rat_one : IsPrimitiveRoot (1 : ℚ) 1)
    (primitiveRoot_rat_two : IsPrimitiveRoot (-1 : ℚ) 2) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, primitiveRoot_rat_one⟩
  by_cases hm2 : m = 2
  · subst hm2
    exact ⟨-1, primitiveRoot_rat_two⟩
  have hm3 : 3 ≤ m := by omega
  exact False.elim (not_hasFullRationalTorsion_of_three_le (E := E) hm3 hfull)

end FLT
```

## Final recommendation

As of the current Lean/Mathlib landscape, the shortest route is:

```text
Do not formalize the full Weil pairing.
Do not use class field theory.
Do not rely on torsion finiteness.
Do not try to extract a rational primitive root for m ≥ 3.

Instead, add the targeted obstruction
  HasFullRationalTorsion E m → m ≤ 2,
prove it later by determinant/cyclotomic at complex conjugation,
and finish the theorem by the existing m=1 and m=2 cases.
```

If you allow one localized project `sorry`, put it in `fullRationalTorsion_order_le_two` or `not_hasFullRationalTorsion_of_three_le`.  That is the smallest honest missing mathematical input.  If you require a no-`sorry` proof using only currently exposed Mathlib theorems, I do not see a shorter available path than formalizing a determinant/cyclotomic consequence, which is essentially the Weil-pairing theorem in a compressed form.
