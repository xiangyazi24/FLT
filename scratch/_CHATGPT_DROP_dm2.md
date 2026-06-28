# Q2055 (dm2): wiring `WeilPairingInterface` into Mazur downstream code

Date: 2026-06-28.

Question: `WeilPairingInterface.lean` now compiles, `primitive_root_in_base` is fully proved, and the only remaining `sorry` is the bridge theorem constructing `AbstractGaloisWeilData` from an actual elliptic curve.  Should this replace the existing `WeilPairing.lean`, or should both files remain?  What is the cleanest way to connect `WeilPairingInterface.primitive_root_in_base` to downstream `TorsionBound.lean`?

## Recommendation

Keep **both** files, but make their roles different:

```text
WeilPairingInterface.lean  = real abstract theorem layer
WeilPairing.lean           = thin compatibility/shim layer exposing the old theorem name
TorsionBound.lean          = unchanged, or nearly unchanged
```

Do **not** make `TorsionBound.lean` depend directly on the internals of `AbstractGaloisWeilData`.  The downstream torsion-bound proof only needs the consequence

```lean
weil_pairing_primitive_root
```

so keep that theorem name as the stable public API.

The one remaining `sorry`/axiom should be concentrated in exactly one bridge theorem:

```lean
weil_interface_bridge
```

and the old `weil_pairing_primitive_root` theorem should become a proved wrapper:

```lean
theorem weil_pairing_primitive_root ... := by
  exact primitive_root_in_base (weil_interface_bridge ...)
```

This makes the bridge axiom visibly equivalent to the old axiom, but all downstream code benefits from the already-proved abstract descent theorem.

## Why keep both?

`WeilPairingInterface.lean` is the right place for the abstract mathematical payload:

* abstract Galois Weil data;
* bilinearity / nondegeneracy fields;
* Galois equivariance or base-field rationality;
* the fully proved theorem `primitive_root_in_base`.

`WeilPairing.lean` should keep the old Mazur-facing theorem name:

```lean
weil_pairing_primitive_root
```

That name is already what downstream code expects.  In the current scaffold I inspected, `TorsionBound.lean` proves

```lean
theorem full_rational_torsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) : m ≤ 2 := by
  rcases weil_pairing_primitive_root E hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ
```

So the best integration is to preserve that call site.

## Clean file graph

The cleanest architecture is:

```text
Definitions / low-level torsion predicates
  ↓
WeilPairingInterface.lean
  contains AbstractGaloisWeilData and proved primitive_root_in_base
  contains or imports the one bridge declaration weil_interface_bridge
  ↓
WeilPairing.lean
  proves the old public theorem weil_pairing_primitive_root from the interface
  ↓
Axioms.lean / TorsionBound.lean
  continue using weil_pairing_primitive_root
```

There is one important cycle hazard: if `WeilPairingInterface.lean` or `WeilPairing.lean` needs the definitions

```lean
HasFullRationalTorsion
HasRationalPointOfOrder
HasTorsionStructure
TorsionStructureData
```

and those are currently inside `Axioms.lean`, then do not make `Axioms.lean` import `WeilPairing.lean` unless those definitions have been split out first.

The clean split is:

```text
AxiomsBasic.lean        -- only definitions: torsionSet, HasFullRationalTorsion, etc.
WeilPairingInterface.lean imports AxiomsBasic
WeilPairing.lean imports WeilPairingInterface
Axioms.lean imports AxiomsBasic + WeilPairing + remaining hard inputs
TorsionBound.lean imports Axioms
```

If you do not want a new `AxiomsBasic.lean`, then the next-best option is:

```text
WeilPairingInterface.lean imports Axioms.lean
WeilPairing.lean imports WeilPairingInterface.lean
TorsionBound.lean imports WeilPairing.lean directly
```

but then `Axioms.lean` must not also declare an axiom with the same name, and the dependency layering is less clean.

## Concrete shim pattern

Put this in `WeilPairing.lean` or refactor the existing file to this shape.  Names may need minor adjustment to your actual interface names.

```lean
import FLT.Assumptions.MazurProof.WeilPairingInterface

/-!
# Weil-pairing public API for the Mazur proof

This file is intentionally a compatibility layer.  The abstract theorem is proved
in `WeilPairingInterface.lean`; the only construction gap is the bridge from an
actual elliptic curve with full rational `m`-torsion to `AbstractGaloisWeilData`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/--
Bridge from an actual elliptic curve with full rational `m`-torsion to the
abstract Galois Weil-pairing data.

This is the only remaining Weil-pairing construction input.  It is equivalent in
strength to the old `weil_pairing_primitive_root` axiom.
-/
axiom weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    AbstractGaloisWeilData E m

/--
Old public Mazur-facing consequence of the Weil pairing.

Keep this theorem name so `TorsionBound.lean` does not need to know about the
abstract interface.
-/
theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  exact primitive_root_in_base (weil_interface_bridge E hm hfull)

end MazurProof
```

If `weil_interface_bridge` already lives in `WeilPairingInterface.lean`, then `WeilPairing.lean` should not redeclare it.  It should just import the interface and prove the wrapper theorem:

```lean
theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  exact primitive_root_in_base (weil_interface_bridge E hm hfull)
```

## What to change in `Axioms.lean`

Current scaffold shape has the old Group B axiom:

```lean
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Replace that axiom with an import of the shim theorem, or move it out entirely.  The file should no longer declare `weil_pairing_primitive_root` as an axiom.

Best version:

```lean
import FLT.Assumptions.MazurProof.WeilPairing
```

and delete the Group B axiom block from `Axioms.lean`.

If import cycles appear, split the basic definitions first:

```text
AxiomsBasic.lean
```

then import that basic file from both `Axioms.lean` and `WeilPairingInterface.lean`.

## What to change in `TorsionBound.lean`

Ideally, nothing.

The current downstream proof uses exactly the correct abstraction boundary:

```lean
rcases weil_pairing_primitive_root E hm hfull with ⟨ζ, hζ⟩
exact isPrimitiveRoot_rat_order_le_two hζ
```

Keep this.  `TorsionBound.lean` should not know about:

* `AbstractGaloisWeilData`;
* `primitive_root_in_base`;
* the bridge theorem;
* Weil-pairing bilinearity/nondegeneracy details.

If the import graph requires one explicit import, add only the public shim:

```lean
import FLT.Assumptions.MazurProof.WeilPairing
```

Do not import `WeilPairingInterface` directly into `TorsionBound.lean` unless you are temporarily debugging.

## The clean theorem chain

The final proof chain should read:

```text
actual elliptic curve + full rational m-torsion
  -- weil_interface_bridge              (only construction axiom/sorry)
AbstractGaloisWeilData
  -- primitive_root_in_base             (fully proved in WeilPairingInterface)
∃ ζ : ℚ, IsPrimitiveRoot ζ m
  -- isPrimitiveRoot_rat_order_le_two   (already downstream)
m ≤ 2
```

In Lean shape:

```lean
have hdata : AbstractGaloisWeilData E m :=
  weil_interface_bridge E hm hfull
rcases primitive_root_in_base hdata with ⟨ζ, hζ⟩
exact isPrimitiveRoot_rat_order_le_two hζ
```

but this chain should be hidden behind the old public theorem:

```lean
weil_pairing_primitive_root
```

so downstream remains stable.

## Decision

Use `WeilPairingInterface.lean` to replace the **mathematical content** of `WeilPairing.lean`, but do not delete or bypass `WeilPairing.lean` yet.  Turn `WeilPairing.lean` into the compatibility layer that exports the old theorem name.

That gives the cleanest migration:

```text
old downstream theorem name preserved;
old Weil-pairing axiom removed;
new abstract theorem used;
only one bridge axiom/sorry remains;
TorsionBound.lean stays conceptually clean.
```

## Checklist

1. Ensure `WeilPairingInterface.lean` has the fully proved theorem:
   ```lean
   primitive_root_in_base
   ```
2. Ensure there is exactly one bridge declaration:
   ```lean
   weil_interface_bridge
   ```
3. Make `WeilPairing.lean` prove:
   ```lean
   weil_pairing_primitive_root
   ```
   from those two items.
4. Remove or stop importing the old axiom version of `weil_pairing_primitive_root` from `Axioms.lean`.
5. Keep `TorsionBound.lean` using `weil_pairing_primitive_root`.
6. Run:
   ```bash
   lake env lean FLT/Assumptions/MazurProof/WeilPairingInterface.lean
   lake env lean FLT/Assumptions/MazurProof/WeilPairing.lean
   lake env lean FLT/Assumptions/MazurProof/Axioms.lean
   lake env lean FLT/Assumptions/MazurProof/TorsionBound.lean
   ```
