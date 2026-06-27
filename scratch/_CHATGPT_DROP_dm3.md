# Q1173 (dm3): replacing `weil_pairing_primitive_root` by Route 4B in `Axioms.lean`

## Replacement idea

Yes: in `no_odd_prime_square_in_torsion`, the primitive-root detour is unnecessary.  Once the proof has built

```lean
hfull : HasFullRationalTorsion E p
```

from the alleged embedding `(ZMod p × ZMod p) →+ E(ℚ)`, Route 4B immediately gives

```lean
p ≤ 2
```

while the odd-prime hypothesis gives

```lean
3 ≤ p
```

and `omega` closes the contradiction.

So the old block

```lean
  rcases weil_pairing_primitive_root E hp.pos hfull with ⟨zeta, hzeta⟩
  have hp_le_two : p ≤ 2 := isPrimitiveRoot_rat_order_le_two hzeta
  omega
```

should be replaced by the Route 4B block below.

## Import to add

At the top of `Axioms.lean`, add the module that contains Route 4B.  If the file is literally `FLT/RealTorsionBound.lean`, the import is:

```lean
import FLT.RealTorsionBound
```

If `RealTorsionBound.lean` lives under a subdirectory, use the corresponding module path, for example:

```lean
import FLT.EllipticCurve.RealTorsionBound
```

The rest of the old primitive-root imports can stay temporarily, but after this replacement they should no longer be needed by `no_odd_prime_square_in_torsion`.

## Exact replacement for lines 573-586

Use this if the current context already has the `hfull : HasFullRationalTorsion E p` line, as your description indicates.

```lean
  -- Route 4B replaces the old Weil-pairing/primitive-root contradiction.
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hfull
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

This is the replacement for the old call:

```lean
  rcases weil_pairing_primitive_root E hp.pos hfull with ⟨zeta, hzeta⟩
```

No `ζ : ℚ` is introduced anymore.

## If Route 4B has an explicit positivity argument

If the actual theorem in `RealTorsionBound.lean` has the shape

```lean
fullRationalTorsion_order_le_two_route4B
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2
```

then use this one-line variant instead:

```lean
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hp.pos hfull
```

and keep the rest identical:

```lean
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

## If `omega` cannot derive `3 ≤ p` directly

If the current proof does not already have a hypothesis like `hp_ge_three : 3 ≤ p`, but instead has a prime proof plus an oddness/non-two proof, use the expanded version.  Suppose the oddness hypothesis is named

```lean
hp_ne_two : p ≠ 2
```

Then replace the block by:

```lean
  -- Route 4B replaces the old Weil-pairing/primitive-root contradiction.
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hfull
  have hp_ge_three : 3 ≤ p := by
    have hp_two_le : 2 ≤ p := hp.two_le
    omega
  omega
```

If the oddness hypothesis is instead named, for example, `hp_odd : p ≠ 2`, change only the local name:

```lean
  have hp_ge_three : 3 ≤ p := by
    have hp_two_le : 2 ≤ p := hp.two_le
    have hp_ne_two : p ≠ 2 := hp_odd
    omega
```

If the oddness hypothesis is `hodd : Odd p`, use:

```lean
  have hp_ge_three : 3 ≤ p := by
    have hp_two_le : 2 ≤ p := hp.two_le
    have hp_ne_two : p ≠ 2 := by
      intro hp_eq
      subst p
      norm_num at hodd
    omega
```

## Full intended tail of `no_odd_prime_square_in_torsion`

The tail of the proof should now look like this.  The construction of `hfull` is whatever is already present in your file immediately before line 584.

```lean
import Mathlib
import FLT.RealTorsionBound

noncomputable section

-- Inside `Axioms.lean`, inside the existing namespace/context:

-- theorem no_odd_prime_square_in_torsion ... := by
--   ...
--   have hfull : HasFullRationalTorsion E p := by
--     -- existing code converting the alleged `(ZMod p)^2` embedding into full rational p-torsion
--     ...

  -- Route 4B replaces:
  --   rcases weil_pairing_primitive_root E hp.pos hfull with ⟨zeta, hzeta⟩
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hfull
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

If the Route 4B theorem takes `hm : 0 < m`, use the variant with `hp.pos`:

```lean
  have hp_le_two : p ≤ 2 :=
    fullRationalTorsion_order_le_two_route4B (E := E) (m := p) hp.pos hfull
  have hp_ge_three : 3 ≤ p := by
    omega
  omega
```

## What to do with the old axiom

After this change, `no_odd_prime_square_in_torsion` no longer uses

```lean
weil_pairing_primitive_root
```

So if that was the only remaining use, delete the axiom at line 72.  If Lean reports other uses, replace those uses similarly: first derive `HasFullRationalTorsion E m`, then call

```lean
fullRationalTorsion_order_le_two_route4B
```

and contradict the relevant lower bound on `m`.
