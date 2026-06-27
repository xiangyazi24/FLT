# Q1245 (dm3): Clean axiom architecture for rational torsion

## Executive answer

Yes, the analysis is correct.

Route 4B, as currently described, is **not** an axiom reduction. It replaces the single Weil-pairing corollary axiom

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve Q) [E.IsElliptic] {m : N} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    exists zeta : Q, IsPrimitiveRoot zeta m
```

with two real-topology/cardinality axioms:

```lean
real_mTorsion_finite
real_mTorsion_card_le
```

Unless `real_mTorsion_card_le` is actually proved, Route 4B is a net increase in the trusted axiom surface. It also obscures the mathematical dependency: the real Lie/topology argument is being used only to recover the same conclusion that the Weil pairing already gives in exactly the form needed by the B-line.

So the cleanest architecture is:

```text
B-Line: axiom weil_pairing_primitive_root   -- existing, 1 axiom
A-Line: axiom mazur_cyclic_order_bound      -- cyclic Mazur input, 1 axiom
Total:  2 mathematical axioms
```

Do **not** introduce Route 4B axioms unless the real-torsion cardinality bound is a theorem, not an axiom.

## Why the single Weil-pairing axiom is the right B-line boundary

The only B-line conclusion needed is that an elliptic curve over `Q` cannot have full rational `p`-torsion for an odd prime `p`. The proof route is:

```text
HasFullRationalTorsion E p
  -> exists zeta : Q, IsPrimitiveRoot zeta p        -- Weil pairing corollary
  -> p <= 2                                        -- primitive roots in Q have order <= 2
  -> contradiction for 2 < p
```

That is precisely the existing `weil_pairing_primitive_root` axiom plus the already-local arithmetic lemma `isPrimitiveRoot_rat_order_le_two`.

The proposed axiom name

```lean
weil_pairing_corollary
```

has the same mathematical content as the existing

```lean
weil_pairing_primitive_root
```

so introducing it as an additional axiom would be duplication. If a nicer name is desired, make it a theorem/alias, not an axiom.

## Complete alternative `RealTorsionBound.lean` using one axiom

This file is logically coherent **only if** it replaces the current two-axiom Route 4B file. It should not be imported by `Axioms.lean` if it itself imports `Axioms.lean`, or that recreates the import cycle. In the recommended architecture below, this file is unnecessary because the existing `WeilPairing.lean` already provides the same wrapper.

```lean
import Mathlib
import FLT.EllipticCurve.TorsionDefs

noncomputable section

open scoped WeierstrassCurve.Affine

/-- Full rational `m`-torsion gives a rational primitive `m`-th root of unity.

This is the Weil-pairing corollary. If `Axioms.lean` already contains
`weil_pairing_primitive_root` with this exact content, do not add this as a
second axiom; use the existing axiom instead or define this as a theorem alias.
-/
axiom weil_pairing_corollary
    (E : WeierstrassCurve Q) [E.IsElliptic] {m : N} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    exists zeta : Q, IsPrimitiveRoot zeta m

/-- The only consequence of the Weil-pairing corollary needed for the B-line. -/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve Q) [E.IsElliptic] {m : N} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m <= 2 := by
  rcases weil_pairing_corollary E hm hfull with ⟨zeta, hzeta⟩
  exact isPrimitiveRoot_rat_order_le_two hzeta
```

Again, the important point is that the above file has **one** axiom, but that one axiom is just the existing `weil_pairing_primitive_root` under a different name. Therefore it is not better than the current B-line axiom; it is only better than the two-axiom Route 4B attempt.

## Preferred final architecture

The preferred architecture is not to use `RealTorsionBound.lean` for the B-line at all. Keep the B-line axiom explicit and named.

### `TorsionDefs.lean`

Definitions and elementary non-axiomatic lemmas only.

```lean
import Mathlib

noncomputable section

open scoped WeierstrassCurve.Affine

-- Keep shared definitions here, for example:
--   HasFullRationalTorsion
--   any coercion/subtype helpers used by Axioms.lean and downstream files
--   isPrimitiveRoot_rat_order_le_two, if it is proved without using the B-line axiom
--
-- Do not put the Weil-pairing axiom here unless this file is explicitly the
-- project-wide axiom boundary.
```

### `Axioms.lean`

This is the recommended minimal axiom boundary.

```lean
import Mathlib
import FLT.EllipticCurve.TorsionDefs

noncomputable section

open scoped WeierstrassCurve.Affine

/-- B-line axiom: the Weil-pairing corollary for full rational torsion. -/
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve Q) [E.IsElliptic] {m : N} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    exists zeta : Q, IsPrimitiveRoot zeta m

/-- A-line axiom: the cyclic Mazur order bound needed by the project.

Use the exact local statement already chosen for `mazur_cyclic_order_bound`.
The intended mathematical payload is:

  if `E/Q` has a rational point of exact order `n`, then `n <= 12` and `n != 11`.
-/
axiom mazur_cyclic_order_bound
    -- keep the existing local binder/order API here
    : Prop

/-- Local wrapper for the only B-line consequence needed downstream. -/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve Q) [E.IsElliptic] {m : N} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m <= 2 := by
  rcases weil_pairing_primitive_root E hm hfull with ⟨zeta, hzeta⟩
  exact isPrimitiveRoot_rat_order_le_two hzeta
```

If the actual local `mazur_cyclic_order_bound` statement is already present, keep that exact statement; the schematic `: Prop` above is only a placeholder showing where the A-line axiom belongs.

### `no_odd_prime_square_in_torsion`

The clean theorem body should use the existing Weil-pairing axiom directly, or the local wrapper derived from it. With the wrapper in `Axioms.lean`, the body becomes:

```lean
import Mathlib
import FLT.EllipticCurve.TorsionDefs

noncomputable section

open scoped WeierstrassCurve.Affine

private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p x ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  have hle : p <= 2 := fullRationalTorsion_order_le_two E hp.pos hfull
  omega
```

Equivalently, without the wrapper:

```lean
import Mathlib
import FLT.EllipticCurve.TorsionDefs

noncomputable section

open scoped WeierstrassCurve.Affine

private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p x ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  rcases weil_pairing_primitive_root E hp.pos hfull with ⟨zeta, hzeta⟩
  have hle : p <= 2 := isPrimitiveRoot_rat_order_le_two hzeta
  omega
```

The second version has the smallest file-dependency footprint because it does not need a separate `RealTorsionBound.lean` or wrapper import.

## Import-cycle rule

The safe dependency graph is:

```text
TorsionDefs.lean
  -> Axioms.lean
      -> downstream users
```

Optional wrappers may sit downstream of `Axioms.lean`:

```text
TorsionDefs.lean
  -> Axioms.lean
      -> WeilPairing.lean / RealTorsionBound.lean wrappers
      -> downstream users
```

But then `Axioms.lean` must **not** import those wrapper files.

So the final rule is:

```text
Do not make Axioms.lean import RealTorsionBound.lean
if RealTorsionBound.lean imports Axioms.lean.
```

That was the core problem with Route 4B wiring.

## Final recommendation

Keep the original architecture, with exactly two project-level mathematical axioms for this torsion split:

```text
1. weil_pairing_primitive_root
   Full rational m-torsion over Q gives a rational primitive m-th root of unity.

2. mazur_cyclic_order_bound
   A rational torsion point of exact order n has n <= 12 and n != 11.
```

Do not add:

```lean
real_mTorsion_finite
real_mTorsion_card_le
```

as axioms. Route 4B becomes valuable only after `real_mTorsion_card_le` is proved. Until then, it increases the axiom count and should not replace the existing Weil-pairing boundary.
