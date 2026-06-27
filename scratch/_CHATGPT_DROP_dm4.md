# Q1158 (dm4): replacing `weil_pairing_primitive_root` by the Route 4B real torsion bound

## Executive answer

Yes.  The replacement is mathematically and architecturally correct.

The old dependency was:

```text
weil_pairing_primitive_root
  + isPrimitiveRoot_rat_order_le_two
  ⇒ no_odd_prime_square_in_torsion
  ⇒ finite_addCommGroup_two_invariant_factors_exists
```

The Route 4B replacement is:

```text
real_mTorsion_finite
  + real_mTorsion_card_le
  ⇒ fullRationalTorsion_order_le_two_route4B
  ⇒ not_hasFullRationalTorsion_of_three_le
  ⇒ no_odd_prime_square_in_torsion
  ⇒ finite_addCommGroup_two_invariant_factors_exists
```

So the old `weil_pairing_primitive_root` axiom can be deleted from `Axioms.lean`, provided `RealTorsionBound.lean` is a lower dependency and does **not** import `Axioms.lean`.  If it currently imports `Axioms.lean` only to get `HasFullRationalTorsion`, move that definition into a lower definition file, e.g. `FLT/EllipticCurve/FullRationalTorsion.lean`, then make both `RealTorsionBound.lean` and `Axioms.lean` import that file.

The core replacement is simply:

```lean
have hp_le_two : p ≤ 2 :=
  RealTorsionBound.fullRationalTorsion_order_le_two_route4B
    (E := E) (m := p) hp.pos hfull
have hp_ge_three : 3 ≤ p := ...
omega
```

No primitive roots, Weil pairing, or cyclotomic character are needed for this branch.

## Important dependency-cycle warning

The only architectural trap is an import cycle.

This is good:

```text
FullRationalTorsion.lean
  ↓
RealTorsionBound.lean
  ↓
Axioms.lean
```

This is bad:

```text
Axioms.lean
  ↓
RealTorsionBound.lean
  ↓
Axioms.lean
```

So before changing `Axioms.lean`, check whether `RealTorsionBound.lean` imports `Axioms.lean`.  If yes, split out the shared definitions first.

## Drop-in replacement code for `Axioms.lean`

Assuming `RealTorsionBound.lean` is in module path `FLT.EllipticCurve.RealTorsionBound`, add this import near the top of `Axioms.lean`:

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT
```

If the physical file is instead `FLT/RealTorsionBound.lean`, use:

```lean
import Mathlib
import FLT.RealTorsionBound
```

The theorem bodies below are unchanged except for that import path.

## Helper: Route 4B forbids full rational `m`-torsion for `m ≥ 3`

Add this immediately before `no_odd_prime_square_in_torsion`, or in a small helper section above it.

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

/--
Route 4B corollary: full rational `m`-torsion is impossible for `m ≥ 3`.

This is the replacement for the old primitive-root contradiction.  The only
mathematical input is the Route 4B theorem
`fullRationalTorsion_order_le_two_route4B`, which itself depends only on the two
real-torsion axioms `real_mTorsion_finite` and `real_mTorsion_card_le`.
-/
theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm_pos : 0 < m) (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_le_two : m ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := m) hm_pos hfull
  omega

end FLT
```

If your actual theorem was stated without the positivity argument,

```lean
RealTorsionBound.fullRationalTorsion_order_le_two_route4B :
  HasFullRationalTorsion E m → m ≤ 2
```

then use this slightly shorter wrapper instead:

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_le_two : m ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := m) hfull
  omega

end FLT
```

But I recommend keeping the `hm_pos : 0 < m` version if that is how `RealTorsionBound.lean` currently proves the cardinal comparison, since `Nat.card (ZMod 0 × ZMod 0)` is the dangerous edge case.

## Helper: odd prime means `3 ≤ p`

If the current theorem has an `Odd p` hypothesis, use this helper.

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

private lemma three_le_of_prime_odd {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    3 ≤ p := by
  rcases hp_odd with ⟨k, rfl⟩
  have hp_two_le : 2 ≤ 2 * k + 1 := hp.two_le
  omega

end FLT
```

If the current theorem instead has a `p ≠ 2` hypothesis, use this helper.

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

private lemma three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp_ne_two : p ≠ 2) :
    3 ≤ p := by
  have hp_two_le : 2 ≤ p := hp.two_le
  omega

end FLT
```

## Replacement for `no_odd_prime_square_in_torsion`

### Variant 1: theorem statement uses `Odd p`

This is the most likely shape given the theorem name.

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

private lemma three_le_of_prime_odd {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    3 ≤ p := by
  rcases hp_odd with ⟨k, rfl⟩
  have hp_two_le : 2 ≤ 2 * k + 1 := hp.two_le
  omega

/--
No odd prime square can occur as full rational torsion.

This used to be proved by:

```text
weil_pairing_primitive_root + isPrimitiveRoot_rat_order_le_two
```

It is now proved directly by Route 4B:

```text
HasFullRationalTorsion E p → p ≤ 2,
```

contradicting `3 ≤ p` for an odd prime.
-/
theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp_odd : Odd p) :
    ¬ HasFullRationalTorsion E p := by
  intro hfull
  have hp_ge_three : 3 ≤ p := three_le_of_prime_odd hp hp_odd
  exact not_hasFullRationalTorsion_of_three_le
    (E := E) (m := p) hp.pos hp_ge_three hfull

end FLT
```

If you prefer not to introduce the wrapper theorem, the body can be inlined:

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

private lemma three_le_of_prime_odd {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    3 ≤ p := by
  rcases hp_odd with ⟨k, rfl⟩
  have hp_two_le : 2 ≤ 2 * k + 1 := hp.two_le
  omega

theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp_odd : Odd p) :
    ¬ HasFullRationalTorsion E p := by
  intro hfull
  have hp_le_two : p ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := p) hp.pos hfull
  have hp_ge_three : 3 ≤ p := three_le_of_prime_odd hp hp_odd
  omega

end FLT
```

### Variant 2: theorem statement uses `p ≠ 2`

If the current `no_odd_prime_square_in_torsion` has `hp_ne_two : p ≠ 2` instead of `Odd p`, use this version.

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

private lemma three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp_ne_two : p ≠ 2) :
    3 ≤ p := by
  have hp_two_le : 2 ≤ p := hp.two_le
  omega

theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) :
    ¬ HasFullRationalTorsion E p := by
  intro hfull
  have hp_le_two : p ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := p) hp.pos hfull
  have hp_ge_three : 3 ≤ p := three_le_of_prime_ne_two hp hp_ne_two
  omega

end FLT
```

### Variant 3: theorem statement already has `3 ≤ p`

If the current theorem already carries `hp3 : 3 ≤ p`, the replacement is only three lines.

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) :
    ¬ HasFullRationalTorsion E p := by
  intro hfull
  have hp_le_two : p ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := p) hp.pos hfull
  omega

end FLT
```

## Literal body replacement inside the existing theorem

If the existing theorem already has `hfull : HasFullRationalTorsion E p` in context, replace the old body

```lean
obtain ⟨ζ, hζ⟩ := weil_pairing_primitive_root (E := E) (m := p) ?hm hfull
have hp_le_two := isPrimitiveRoot_rat_order_le_two hζ
omega
```

with:

```lean
have hp_le_two : p ≤ 2 :=
  RealTorsionBound.fullRationalTorsion_order_le_two_route4B
    (E := E) (m := p) hp.pos hfull
have hp_ge_three : 3 ≤ p := by
  -- choose one of these depending on the available local hypothesis:
  --   exact three_le_of_prime_odd hp hp_odd
  --   exact three_le_of_prime_ne_two hp hp_ne_two
  --   exact hp3
  exact three_le_of_prime_odd hp hp_odd
omega
```

That is the exact replacement for the primitive-root route.

## What to delete or keep

After this change, `Axioms.lean` no longer needs:

```lean
axiom weil_pairing_primitive_root ...
```

for `no_odd_prime_square_in_torsion`.

If `weil_pairing_primitive_root` has no other uses, delete it entirely.

The theorem

```lean
isPrimitiveRoot_rat_order_le_two
```

is no longer needed for this dependency chain either.  It can be deleted if it is unused, or kept as a harmless standalone elementary theorem if another file still imports it.

The final axiom footprint becomes:

```text
real_mTorsion_finite
real_mTorsion_card_le
```

instead of:

```text
weil_pairing_primitive_root
```

This is a genuine axiom replacement, not just a renaming: the arithmetic content moves from Weil pairing/cyclotomic roots of unity to the real Lie-group bound `#E(ℝ)[m] ≤ 2m`.

## Why `finite_addCommGroup_two_invariant_factors_exists` does not need to change

If `finite_addCommGroup_two_invariant_factors_exists` only depends on the theorem name

```lean
no_odd_prime_square_in_torsion
```

then it does not need any modification.  Keep the theorem statement and name exactly the same, and only replace its proof body.  The downstream chain remains:

```text
no_odd_prime_square_in_torsion
  ⇒ finite_addCommGroup_two_invariant_factors_exists
  ⇒ rest of proof
```

The downstream code should not see the difference.

## Recommended final `Axioms.lean` organization

Use this section order:

```lean
import Mathlib
import FLT.EllipticCurve.RealTorsionBound

open scoped Classical

noncomputable section

namespace FLT

-- Existing elementary/group-theory definitions and lemmas.

private lemma three_le_of_prime_odd {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    3 ≤ p := by
  rcases hp_odd with ⟨k, rfl⟩
  have hp_two_le : 2 ≤ 2 * k + 1 := hp.two_le
  omega

theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm_pos : 0 < m) (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_le_two : m ≤ 2 :=
    RealTorsionBound.fullRationalTorsion_order_le_two_route4B
      (E := E) (m := m) hm_pos hfull
  omega

theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp_odd : Odd p) :
    ¬ HasFullRationalTorsion E p := by
  intro hfull
  exact not_hasFullRationalTorsion_of_three_le
    (E := E) (m := p) hp.pos (three_le_of_prime_odd hp hp_odd) hfull

-- Existing `finite_addCommGroup_two_invariant_factors_exists` follows unchanged.

end FLT
```

That is the cleanest Route 4B replacement for the old Weil-pairing call.
