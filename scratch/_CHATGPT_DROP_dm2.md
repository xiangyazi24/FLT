# Q1220 (dm2): Route 4B import-restructured `Axioms.lean` edit

## Required import change

`Axioms.lean` should no longer own the shared torsion definitions.  It should import `TorsionDefs.lean`, and it should import `RealTorsionBound.lean` so that `no_odd_prime_square_in_torsion` can call Route 4B directly.

Use this import shape at the top of `Axioms.lean`, preserving any unrelated existing imports if the file already has them:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound
```

Then delete the local duplicated definitions now owned by `TorsionDefs.lean`:

```lean
-- delete from Axioms.lean if still present here:
-- torsionSet
-- HasFullRationalTorsion
-- HasRationalPointOfOrder
-- HasTorsionStructure
-- ContainsZ2xZn
-- TorsionStructureData
```

## Delete the old Weil-pairing axiom

Delete the old `weil_pairing_primitive_root` axiom block at lines 72--74.  There is no replacement axiom in `Axioms.lean`.

```lean
-- DELETE this axiom block entirely:
-- axiom weil_pairing_primitive_root ...
```

## Exact new lines 573--586 replacement

Replace the old `no_odd_prime_square_in_torsion` block with this Route 4B version:

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

The proof no longer calls either of these:

```lean
weil_pairing_primitive_root
isPrimitiveRoot_rat_order_le_two
```

The key replacement is exactly:

```lean
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  have hle : p <= 2 := fullRationalTorsion_order_le_two_route4B E hp.pos hfull
  omega
```
