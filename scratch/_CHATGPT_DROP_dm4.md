# Q1209 (dm4): tightest torsion bound without Mazur cyclic theorem

## Executive answer

With only the listed ingredients, the tightest concrete upper bound on

```text
|E(ℚ)_tors|
```

is: **no finite bound at all**.

The best structural result available is essentially:

```text
E(ℚ)_tors ≅ Z/mZ × Z/nZ,  m ∣ n,  m ≤ 2,
```

plus a few exclusions in the `m = 2` branch:

```text
not Z/2 × Z/10,
not Z/2 × Z/12,
not Z/2 × Z/14,
not Z/2 × Z/16.
```

This does **not** bound the cyclic branch `m = 1`.  For every proposed constant `C`, the formal constraints are still compatible with

```text
Z/(C+1)Z.
```

So from these ingredients alone one cannot prove `|E(ℚ)_tors| ≤ 16`, or `≤ 100`, or any universal finite bound.

A small correction to the prompt: in invariant-factor normal form `m ∣ n`, the group

```text
Z/2 × Z/11
```

is not an `m = 2` case, since `2 ∤ 11`; it is cyclic:

```text
Z/2 × Z/11 ≅ Z/22.
```

So it belongs to the unbounded `m = 1` cyclic branch.  The conclusion is the same: without a cyclic-order theorem, the order is unbounded by the available lemmas.

## What the listed ingredients actually imply

Let

```text
T = E(ℚ)_tors.
```

Ingredient 1 gives:

```text
T ≅ Z/mZ × Z/nZ,   m ∣ n.
```

Ingredient 2 gives:

```text
m ≤ 2.
```

Therefore there are only two invariant-factor shapes:

```text
m = 1:  T ≅ Z/nZ,          n arbitrary.

m = 2:  T ≅ Z/2Z × Z/nZ,  with 2 ∣ n.
```

Ingredients 3–6 remove only four values from the second branch:

```text
n ≠ 10, 12, 14, 16
```

assuming the theorem statements are exactly `¬(Z/2 × Z/n)` for those `n`.

Ingredient 7, the cubic-root bound on `2`-torsion, gives no cyclic-order bound.  A cyclic group `Z/NZ` has at most two elements of order dividing `2`, so it is compatible with arbitrarily large `N`.

Thus the set of groups not excluded by the available ingredients still contains:

```text
Z/NZ   for every N ≥ 1.
```

Hence no finite order bound follows.

## Formal toy certificate: the constraints are unbounded

Here is a tiny Lean skeleton showing the logical shape.  It models only the invariant-factor constraints, not elliptic curves.  The point is that `m = 1` bypasses every rank-two exclusion.

```lean
import Mathlib

namespace FLT

namespace TorsionWithoutMazur

/--
A toy predicate for the invariant-factor constraints currently available.
It deliberately does not encode any cyclic Mazur theorem.
-/
def AvailableInvariantFactorShape (m n : ℕ) : Prop :=
  m ∣ n ∧ m ≤ 2

/--
The available invariant-factor constraints allow arbitrarily large orders.
Take the cyclic branch `m = 1`, `n = B + 1`.
-/
theorem available_constraints_do_not_bound_order
    (B : ℕ) :
    ∃ m n : ℕ,
      AvailableInvariantFactorShape m n ∧ B < m * n := by
  refine ⟨1, B + 1, ?_, ?_⟩
  · exact ⟨one_dvd _, by norm_num⟩
  · omega

end TorsionWithoutMazur

end FLT
```

If you want to also encode the four excluded rank-two cases, the same witness still works because `m = 1`.

```lean
import Mathlib

namespace FLT

namespace TorsionWithoutMazur

/-- The four currently excluded rank-two second factors. -/
def ExcludedRankTwoSecondFactor (n : ℕ) : Prop :=
  n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16

/--
Available constraints plus the four `Z/2 × Z/n` exclusions.
The exclusions only apply to the `m = 2` branch.
-/
def AvailableShapeWithRankTwoExclusions (m n : ℕ) : Prop :=
  m ∣ n ∧
  m ≤ 2 ∧
  ¬ (m = 2 ∧ ExcludedRankTwoSecondFactor n)

/-- Even after the four rank-two exclusions, the cyclic branch remains unbounded. -/
theorem available_constraints_with_exclusions_do_not_bound_order
    (B : ℕ) :
    ∃ m n : ℕ,
      AvailableShapeWithRankTwoExclusions m n ∧ B < m * n := by
  refine ⟨1, B + 1, ?_, ?_⟩
  · refine ⟨one_dvd _, by norm_num, ?_⟩
    intro h
    exact by omega
  · omega

end TorsionWithoutMazur

end FLT
```

This is the precise formal reason no theorem of the form

```lean
Nat.card EQtors ≤ C
```

can be derived from just the listed facts.

## What would be needed for `≤ 16`

To prove the actual Mazur bound

```text
|E(ℚ)_tors| ≤ 16,
```

you need at least a cyclic-order theorem, e.g.

```lean
cyclic_torsion_order_le_12_or_rank_two_bound
```

or more concretely:

```lean
theorem no_point_of_exact_order_gt_12_except_rank_two_cases
```

But this is already the cyclic part of Mazur / modular-curve input.

A minimal bridge sufficient for the final cardinal bound could be:

```lean
import Mathlib

namespace FLT

/-- Schematic: a point of exact order `n` on `E(ℚ)`. -/
-- Use the project's actual definition.
-- def HasPointOfExactOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
--   ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/--
Cyclic torsion bound bridge.  This is essentially the cyclic part of Mazur's theorem.
-/
axiom no_large_cyclic_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 13 ≤ n) :
    ¬ HasPointOfExactOrder E n

end FLT
```

With such a bridge, one can start proving `≤ 16`.  Without such a bridge, the cyclic branch is unlimited.

## Can Lutz–Nagell give a uniform bound?

No.  Lutz–Nagell is useful for **computing torsion on a fixed integral Weierstrass model**, but it does not give a universal constant independent of the curve.

For a short integral model, the classical Nagell–Lutz theorem says roughly:

```text
if P = (x,y) ∈ E(ℚ) is torsion,
then x,y are integers, and either y = 0 or y² divides the discriminant Δ.
```

This makes the torsion subgroup effectively finite for a fixed curve because there are only finitely many divisors of the fixed integer `Δ` to check.

But `Δ` varies with the curve and can be arbitrarily large.  Therefore the theorem gives a curve-dependent enumeration procedure, not a uniform bound on `|E(ℚ)_tors|` across all rational elliptic curves.

So the implication

```text
Lutz–Nagell + height bounds ⇒ universal n ≤ C
```

is not available in any elementary way.  Height estimates can bound searches for a fixed curve or relate torsion to a fixed discriminant/conductor, but they do not yield a universal constant without deeper input.  A genuine uniform bound is essentially the content of Mazur for `ℚ`, or Merel/uniform boundedness over number fields, both modular-curve-level theorems.

## Does Mathlib have Lutz–Nagell?

I do not find a ready FLT-local theorem named or corresponding to Lutz–Nagell.  The FLT repository’s visible torsion file is still centered around the `WeierstrassCurve.nTorsion` API and has placeholder/sorried geometric torsion facts, not an integral-model Lutz–Nagell implementation.

In practical Lean terms: even if a Lutz–Nagell theorem were added, it would not close the desired universal bound.  The theorem would likely have a shape like this:

```lean
import Mathlib

namespace FLT

/-- Schematic only: fixed-curve Lutz–Nagell style statement. -/
axiom lutz_nagell_schematic
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    -- plus an integral/minimal model package and discriminant `Δ`
    : True
    -- intended conclusion:
    -- torsion affine coordinates are integral, and y = 0 or y^2 ∣ Δ

end FLT
```

That statement is not a replacement for Mazur.  It only gives a finite computation after `E` is fixed.

## Reduction-mod-primes also gives only curve-dependent bounds

For a fixed curve, reduction at good primes can bound torsion:

```text
#E(ℚ)_tors divides or injects into #E(F_ℓ)
```

for suitable good primes and prime-to-`ℓ` torsion.  Taking two good primes often gives strong curve-dependent bounds.

But uniformly over all `E/ℚ`, the small-prime problem appears again: the bad reduction set can contain any prescribed finite set of primes.  Thus reduction mod primes is not a universal elementary substitute for the cyclic Mazur theorem.

## Best possible current statement

The strongest honest theorem you can prove from the listed ingredients is not a cardinal bound.  It is a structural reduction:

```lean
/-- Schematic final form of what the current ingredients can prove. -/
theorem rational_torsion_shape_without_cyclic_Mazur
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m n : ℕ,
      m ∣ n ∧
      m ≤ 2 ∧
      -- if m = 2, exclude the four known descent cases
      ¬ (m = 2 ∧ (n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16)) ∧
      True := by
  -- supplied by the existing two-invariant-factor theorem,
  -- Route 4B's `m ≤ 2`, and the four descent exclusions.
  sorry
```

The `sorry` is schematic: it represents wiring together your already-proved facts.  The important point is that this theorem intentionally has no `Nat.card ≤ C` conclusion, because no such `C` follows.

## Final recommendation

Do not try to claim `|E(ℚ)_tors| ≤ 16` from the current non-Mazur ingredients.  That would silently smuggle in a cyclic-order theorem.

The precise architecture should be:

```text
Current non-Mazur block:
  two invariant factors
  + Route 4B m ≤ 2
  + four rank-two exclusions
  ⇒ structural shape only, no finite cardinal bound.

New hard input needed for finite universal bound:
  cyclic Mazur theorem, or a weaker explicit cyclic bound.
```

If the downstream proof only needs to rule out the rank-two cases, the current Route 4B plus descent bridges are enough.  If it needs a universal bound on `|E(ℚ)_tors|`, then a cyclic torsion theorem is unavoidable.
