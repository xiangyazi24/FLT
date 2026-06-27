# Q1182 (dm3): import restructure for `TorsionDefs.lean`

## Connector note

I attempted to read the file path implied by the request:

```text
FLT/Assumptions/MazurProof/Axioms.lean
```

on branch `scratch`, but the GitHub connector returned `404`. Repository code search also did not find `HasFullRationalTorsion`, `TorsionStructureData`, or `weil_pairing_primitive_root`. I could read the public `FLT/Assumptions/Mazur.lean`, but not the newer `MazurProof/Axioms.lean` file referenced in the prompt.

So the content below is the exact extraction I recommend from the signatures described in the prompt. If the unpublished `Axioms.lean` has different field names inside `TorsionStructureData`, preserve those field names exactly when doing the mechanical cut/paste. The import-cycle fix itself is independent of those field names.

## Goal

Break the cycle:

```text
Axioms.lean
  imports RealTorsionBound.lean
    imports Axioms.lean
```

by moving only the torsion **definitions** into:

```text
FLT/Assumptions/MazurProof/TorsionDefs.lean
```

Then use:

```text
Axioms.lean
  imports TorsionDefs.lean
  imports RealTorsionBound.lean

RealTorsionBound.lean
  imports TorsionDefs.lean
```

No file below `RealTorsionBound.lean` should import `Axioms.lean` merely to see `HasFullRationalTorsion`.

## New file: `FLT/Assumptions/MazurProof/TorsionDefs.lean`

Create this file:

```lean
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Torsion

/-!
# Torsion definitions for the Mazur-proof A-line

This file contains only definitions.  It is intentionally axiom-free.

It exists to break the import cycle:

* `Axioms.lean` needs the torsion definitions and the Route 4B theorem;
* `RealTorsionBound.lean` needs the torsion definitions;
* therefore the shared definitions must live below both files.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

/-- The torsion subset of the rational point group of an elliptic curve over `ℚ`. -/
def torsionSet (E : WeierstrassCurve ℚ) [E.IsElliptic] : Set (E⁄ℚ).Point :=
  (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point)

/--
`E` has full rational `m`-torsion if `(ℤ/mℤ)^2` injects into the rational point group.
-/
def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/-- `E` has a rational point of exact additive order `n`. -/
def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/--
The rational torsion subgroup of `E` has invariant-factor shape `ZMod m × ZMod n`.
-/
def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  Nonempty ((AddCommGroup.torsion (E⁄ℚ).Point) ≃+ (ZMod m × ZMod n))

/-- `E(ℚ)` contains a subgroup isomorphic to `ZMod 2 × ZMod n`. -/
def ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ f : ZMod 2 × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

/--
Data form of the rational torsion invariant-factor theorem.

This packages the two invariant factors, the divisibility relation, and an additive equivalence from
`E(ℚ)_tors` to `ZMod m × ZMod n`.
-/
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  dvd : m ∣ n
  torsionEquiv : (AddCommGroup.torsion (E⁄ℚ).Point) ≃+ (ZMod m × ZMod n)
```

### If your current `Axioms.lean` uses `HasTorsionStructure` inside `TorsionStructureData`

If lines 24–62 currently define `TorsionStructureData` by storing a proof of `HasTorsionStructure E m n`, rather than an equivalence directly, use this variant instead:

```lean
/--
Data form of the rational torsion invariant-factor theorem.

This packages the two invariant factors, the divisibility relation, and the proof that the torsion
subgroup has that invariant-factor structure.
-/
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  dvd : m ∣ n
  torsionStructure : HasTorsionStructure E m n
```

The first version is usually better, because it avoids unpacking `Nonempty` later.  But if existing code references a field named `torsionStructure`, preserve the existing field name to avoid changing downstream proofs.

## Exact `Axioms.lean` changes

At the top of `Axioms.lean`, add the shared definitions import:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
```

When you replace the old Weil-pairing axiom by Route 4B, also add:

```lean
import FLT.Assumptions.MazurProof.RealTorsionBound
```

So the import header should have the shape:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound
```

You can delete redundant Mathlib imports if `Axioms.lean` no longer uses them directly.  The important imports for the cycle are:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound
```

Then delete the old local definitions block from `Axioms.lean`:

```lean
-- DELETE from Axioms.lean after moving to TorsionDefs.lean:
--
-- def torsionSet ...
-- def HasFullRationalTorsion ...
-- def HasRationalPointOfOrder ...
-- def HasTorsionStructure ...
-- def ContainsZ2xZn ...
-- structure TorsionStructureData ...
```

Do **not** leave aliases with the same names in `Axioms.lean`; duplicate declarations will fail.  Existing uses in `Axioms.lean` should continue to resolve because the imported declarations have the same names.

The top of `Axioms.lean` should look conceptually like this after the change:

```lean
module

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

-- No torsion definitions here anymore.
-- The first declarations in this file should now be the axioms/theorems that depend on the
-- definitions imported from `TorsionDefs`.
```

## Exact `RealTorsionBound.lean` change

Replace the import of `Axioms.lean`:

```lean
import FLT.Assumptions.MazurProof.Axioms
```

with:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
```

If `RealTorsionBound.lean` currently has other imports, keep them.  The top should look like:

```lean
module

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion
import FLT.Assumptions.MazurProof.TorsionDefs

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine
```

Do **not** import `Axioms.lean` anywhere in `RealTorsionBound.lean` after the restructure.

## Route 4B wiring after the restructure

Once the imports are acyclic, the replacement inside `Axioms.lean` can use Route 4B directly:

```lean
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hfull
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

If the theorem has an explicit positivity argument, use:

```lean
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hp.pos hfull
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

## Recommended verification sequence

After making the file changes, run these checks:

```bash
lake build FLT.Assumptions.MazurProof.TorsionDefs
lake build FLT.Assumptions.MazurProof.RealTorsionBound
lake build FLT.Assumptions.MazurProof.Axioms
```

Then confirm the old axiom is gone:

```lean
#print axioms no_odd_prime_square_in_torsion
```

The expected result should not mention:

```text
weil_pairing_primitive_root
```

If `TorsionDefs.lean` builds but `Axioms.lean` fails at `TorsionStructureData.<field>`, that means the field names in the local copy of `Axioms.lean` differ from the names I had to infer.  In that case, keep the exact field names from the old structure when moving it.
