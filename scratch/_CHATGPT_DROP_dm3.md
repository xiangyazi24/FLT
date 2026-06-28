# Q2056 (dm3): `WeilPairing.lean` vs `WeilPairingInterface.lean`

Date: 2026-06-28.

Question: `WeilPairing.lean` has

```lean
fullRationalTorsion_order_le_two
```

with one `sorry` at line 76.  The new `WeilPairingInterface.lean` has the abstract infrastructure and a fully proved

```lean
primitive_root_in_base
```

The remaining `sorry` in `WeilPairing.lean` is mathematically the same content as the remaining

```lean
weil_interface_bridge
```

`sorry` in `WeilPairingInterface.lean`.  Should we:

* A. delete `WeilPairing.lean` and wire everything through `WeilPairingInterface`;
* B. keep `WeilPairing.lean` but have it import/use `WeilPairingInterface`;
* C. keep both independent?

## Executive answer

Choose **B**.

Keep `WeilPairing.lean` as the **public Mazur-proof wrapper**, but make it import `WeilPairingInterface.lean` and use the interface theorem.  Do not keep the two files independent, and do not delete the public wrapper yet.

The goal should be:

```text
WeilPairingInterface.lean
  = abstract reusable algebra + exactly one concrete bridge gap

WeilPairing.lean
  = thin public-facing wrapper for the Mazur proof, no independent Weil-pairing sorry
```

This gives the best combination of stable imports, clean architecture, and no duplicated mathematical seam.

## Why not A: deleting `WeilPairing.lean`

Deleting `WeilPairing.lean` is too aggressive unless every downstream import has already migrated and the file has no public names you want to keep.

`WeilPairing.lean` likely has the more domain-specific public name:

```lean
fullRationalTorsion_order_le_two
```

or a theorem shaped exactly for the Mazur torsion proof.  Even if the real proof now lives in the interface file, keeping this wrapper preserves the public API and avoids churn in downstream files.

Deletion is only attractive after a cleanup pass confirms:

```text
grep/import graph: no file imports WeilPairing.lean
no public theorem names in WeilPairing.lean are still used
```

Until then, deleting it creates unnecessary refactor risk.

## Why not C: keeping both independent

Keeping both independent is the worst option because it leaves two copies of the same mathematical gap:

```text
WeilPairing.lean:          sorry in fullRationalTorsion_order_le_two
WeilPairingInterface.lean: sorry in weil_interface_bridge
```

That creates three problems:

1. **Duplicate proof obligations.**  When the bridge is finally proved, one file can still accidentally retain a redundant `sorry`.
2. **API drift.**  The two statements may slowly diverge in hypotheses, namespaces, or exact target shape.
3. **Unclear source of truth.**  It becomes ambiguous whether future code should depend on the old direct theorem or the new abstract interface.

The current situation already says the two `sorry`s are the same mathematical content.  There should be exactly one place where that content is assumed/proved.

## Recommended architecture

### `WeilPairingInterface.lean`: source of the abstract argument

This file should contain:

```lean
-- abstract pairing/fixed-point/descent infrastructure
primitive_root_in_base : ...
```

fully proved, plus the single bridge from concrete elliptic-curve hypotheses to the abstract theorem:

```lean
-- this is the one remaining geometric/Weil-pairing seam
 theorem weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- remaining sorry here only
  sorry
```

The exact theorem name can vary, but the target should be the primitive-root consequence, because that is what the Mazur proof actually consumes.

### `WeilPairing.lean`: public wrapper, no independent `sorry`

This file should import the interface and define the old theorem by calling the bridge:

```lean
import FLT.Assumptions.MazurProof.WeilPairingInterface
import FLT.Assumptions.MazurProof.RootsOfUnity

namespace MazurProof

/--
Weil-pairing consequence for the Mazur proof: full rational `m`-torsion forces `m ≤ 2`.
This is now just a wrapper around `WeilPairingInterface` plus the rational-roots-of-unity lemma.
-/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  rcases weil_interface_bridge E hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

end MazurProof
```

This removes the independent `sorry` from `WeilPairing.lean`.  The only remaining `sorry` is the bridge.

## Where should `weil_pairing_primitive_root` live?

For the Mazur scaffold, the most stable public statement is still:

```lean
theorem/axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

If `Axioms.lean` currently declares this as an axiom, then after `WeilPairingInterface.lean` is wired in, the next cleanup should be:

```lean
-- remove axiom from Axioms.lean, or move it behind an import boundary
-- replace with theorem from interface/wrapper
```

But avoid creating an import cycle.  A clean dependency graph is:

```text
Basic definitions / HasFullRationalTorsion
        ↓
RootsOfUnity.lean
        ↓
WeilPairingInterface.lean
        ↓
WeilPairing.lean
        ↓
TorsionBound.lean
```

If `HasFullRationalTorsion` currently lives in `Axioms.lean`, and `Axioms.lean` also contains the axiom you want to replace, split definitions first:

```text
Axioms.lean or Basic.lean:
  HasFullRationalTorsion
  HasRationalPointOfOrder
  HasTorsionStructure
  TorsionStructureData

WeilPairingInterface.lean:
  primitive_root_in_base
  weil_interface_bridge

WeilPairing.lean:
  fullRationalTorsion_order_le_two wrapper
```

This prevents the interface file from importing an axiom file that it is supposed to discharge.

## Exact migration plan

Recommended steps:

1. Make `WeilPairingInterface.lean` the source of the primitive-root bridge:
   ```lean
   theorem weil_interface_bridge ... : ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
     sorry
   ```

2. In `WeilPairing.lean`, replace the line-76 `sorry` with:
   ```lean
   rcases weil_interface_bridge E hm hfull with ⟨ζ, hζ⟩
   exact isPrimitiveRoot_rat_order_le_two hζ
   ```

3. Keep `fullRationalTorsion_order_le_two` in `WeilPairing.lean` for downstream compatibility.

4. Do not expose separate A1/A2/A3 axioms in the Mazur proof API.  Let the bridge theorem be the single seam.

5. Later, when the actual geometric Weil-pairing proof exists, replace only the body of `weil_interface_bridge`.

## Naming recommendation

Use names that clarify the layering:

```lean
-- in WeilPairingInterface.lean
primitive_root_in_base              -- fully proved pure algebra
weil_pairing_primitive_root_bridge  -- one remaining geometric bridge

-- in WeilPairing.lean
fullRationalTorsion_order_le_two    -- public Mazur-facing corollary
```

If there is already a name `weil_interface_bridge`, it is fine to keep it for now, but `weil_pairing_primitive_root_bridge` is more descriptive.

## Final recommendation

Choose **B**:

```text
Keep `WeilPairing.lean`, but make it import and use `WeilPairingInterface.lean`.
```

Then remove the independent `sorry` from `WeilPairing.lean`.  The only remaining `sorry` should be the concrete bridge in `WeilPairingInterface.lean`.  This keeps the public Mazur proof stable while ensuring there is exactly one source of truth for the unfinished Weil-pairing content.
