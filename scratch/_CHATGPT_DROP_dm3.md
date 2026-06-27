# Q1208 (dm3): Route 4B wiring for `no_odd_prime_square_in_torsion`

## Executive answer

Use Route 4B by making the import graph one-way:

```text
TorsionDefs.lean
  ↑
RealTorsionBound.lean
  ↑
Axioms.lean
```

That means:

1. `TorsionDefs.lean` owns the shared definition `HasFullRationalTorsion`.
2. `RealTorsionBound.lean` imports `TorsionDefs.lean`, not `Axioms.lean`.
3. `Axioms.lean` imports `RealTorsionBound.lean` and changes the private theorem body to call `fullRationalTorsion_order_le_two_route4B` directly.

No Weil-pairing primitive-root extraction remains in this theorem.

## 1. `TorsionDefs.lean`

Add `HasFullRationalTorsion` here if it is not already here.  If the same definition currently lives in `Axioms.lean`, move it verbatim into `TorsionDefs.lean` and delete the old copy from `Axioms.lean`.

### Edit operation 1A — add/move shared definition into `TorsionDefs.lean`

Use the namespace marker already present in the file.

old_string:

```lean
namespace FLT.MazurProof
```

new_string:

```lean
namespace FLT.MazurProof

/-- Full rational `n`-torsion: `(ZMod n)^2` injects into the rational point group. -/
def HasFullRationalTorsion
    (E : WeierstrassCurve Q) [E.IsElliptic] (n : N) : Prop :=
  exists f : ZMod n × ZMod n →+ (E/Q).Point, Function.Injective f
```

If the file uses the project’s ASCII product notation in this area, keep the same spelling as the rest of the file:

```lean
  exists f : ZMod n x ZMod n →+ (E/Q).Point, Function.Injective f
```

Do **not** import `Axioms.lean` or `RealTorsionBound.lean` from `TorsionDefs.lean`.

### Edit operation 1B — delete the old copy from `Axioms.lean`, if present

old_string:

```lean
/-- Full rational `n`-torsion: `(ZMod n)^2` injects into the rational point group. -/
def HasFullRationalTorsion
    (E : WeierstrassCurve Q) [E.IsElliptic] (n : N) : Prop :=
  exists f : ZMod n × ZMod n →+ (E/Q).Point, Function.Injective f
```

new_string:

```lean
```

If the current old copy has no docstring, delete just the definition:

old_string:

```lean
def HasFullRationalTorsion
    (E : WeierstrassCurve Q) [E.IsElliptic] (n : N) : Prop :=
  exists f : ZMod n × ZMod n →+ (E/Q).Point, Function.Injective f
```

new_string:

```lean
```

Again, if the current file uses `x` instead of `×`, match the current file spelling in the `old_string`.

## 2. `RealTorsionBound.lean` imports

`RealTorsionBound.lean` must stop importing `Axioms.lean`.  It should depend only on the lower shared definitions file.

### Edit operation 2 — replace the bad upward import

old_string:

```lean
import FLT.Assumptions.MazurProof.Axioms
```

new_string:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
```

The complete import block should have this shape after the edit:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs
```

Preserve any additional Mathlib imports that are already in `RealTorsionBound.lean`; the key point is that this file must not import `FLT.Assumptions.MazurProof.Axioms`.

## 3. `Axioms.lean` imports and theorem body

`Axioms.lean` is now allowed to import `RealTorsionBound.lean`, because `RealTorsionBound.lean` no longer imports `Axioms.lean`.

### Edit operation 3A — add the Route 4B import to `Axioms.lean`

If `Axioms.lean` already imports `TorsionDefs.lean`, use this exact edit:

old_string:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
```

new_string:

```lean
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound
```

If `Axioms.lean` does not currently import `TorsionDefs.lean` directly, add both imports after the existing `Mathlib` import block.  The complete relevant import shape should be:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound
```

Preserve any other existing imports in `Axioms.lean`.

### Edit operation 3B — replace the theorem body lines

old_string:

```lean
  rcases weil_pairing_primitive_root E hp.pos hfull with (zeta, hzeta)  -- THIS LINE CHANGES
  have hle : p <= 2 := isPrimitiveRoot_rat_order_le_two hzeta  -- THIS LINE CHANGES
  omega
```

new_string:

```lean
  have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
  omega
```

### Complete modified theorem

```lean
private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
  omega
```

If the actual file uses ASCII `x` for product notation, the exact same theorem should be spelled as:

```lean
private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p x ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
  omega
```

The only mathematical proof change is exactly this replacement:

```lean
-- old:
rcases weil_pairing_primitive_root E hp.pos hfull with (zeta, hzeta)
have hle : p <= 2 := isPrimitiveRoot_rat_order_le_two hzeta

-- new:
have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
```

## 4. Import-cycle verification

After the edits, the relevant graph is:

```text
TorsionDefs.lean
  imports: Mathlib / low-level torsion prerequisites only

RealTorsionBound.lean
  imports: TorsionDefs.lean

Axioms.lean
  imports: TorsionDefs.lean
  imports: RealTorsionBound.lean
```

There is no cycle because all edges point upward:

```text
Axioms.lean → RealTorsionBound.lean → TorsionDefs.lean
Axioms.lean → TorsionDefs.lean
```

There is no edge:

```text
TorsionDefs.lean → RealTorsionBound.lean
TorsionDefs.lean → Axioms.lean
RealTorsionBound.lean → Axioms.lean
```

So importing `RealTorsionBound.lean` from `Axioms.lean` is safe once edit operation 2 has removed the old `RealTorsionBound.lean → Axioms.lean` edge.

## Final exact patch summary

```text
TorsionDefs.lean:
  add/move HasFullRationalTorsion here.

RealTorsionBound.lean:
  import FLT.Assumptions.MazurProof.Axioms
    ->
  import FLT.Assumptions.MazurProof.TorsionDefs

Axioms.lean:
  add import FLT.Assumptions.MazurProof.RealTorsionBound

Axioms.lean theorem body:
  rcases weil_pairing_primitive_root E hp.pos hfull with (zeta, hzeta)
  have hle : p <= 2 := isPrimitiveRoot_rat_order_le_two hzeta
    ->
  have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
```
