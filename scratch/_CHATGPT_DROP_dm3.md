# Q2028 (dm3): MazurProof two-invariant-factor axiom vs proved theorem

Date: 2026-06-28.

Repository/refs checked:

```text
repo:   xiangyazi24/FLT
branch: ai-scratch
files requested:
  FLT/Assumptions/MazurProof/Axioms.lean
  FLT/Assumptions/MazurProof/TwoInvariantFactors.lean
```

## Fetch status

I successfully fetched:

```text
FLT/Assumptions/MazurProof/Axioms.lean
```

from `ai-scratch`.

However, the requested file

```text
FLT/Assumptions/MazurProof/TwoInvariantFactors.lean
```

returned `404 Not Found` from the GitHub contents API on both `ai-scratch` and the branch-head commit I resolved for `ai-scratch`:

```text
848ffbf5163603f16828def879890e51e5cc3725
```

I also tried the obvious nearby guesses:

```text
TwoInvariantFactor.lean
TwoInvariantFactorData.lean
TorsionTwoInvariantFactors.lean
RationalTorsionTwoInvariantFactors.lean
TorsionStructure.lean
Torsion/TwoInvariantFactors.lean
```

and did not find the file.  So the axiom side below is verified from the fetched file, but the theorem-side comparison is necessarily based on the described Q1996 situation rather than a fetched theorem declaration.

## Verified axiom-side signature

In the `Axioms.lean` that I could fetch, the relevant public structure is:

```lean
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n
```

and the axiom is exactly:

```lean
axiom rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E
```

The downstream `mazur_torsion_bound` proof uses the returned object directly as a record with fields:

```lean
let d := rational_torsion_two_invariant_factors E
...
d.m
d.n
d.m_pos
d.n_pos
d.dvd_mn
d.has_structure
d.has_point_order_n
d.card_eq
```

In particular, the downstream proof depends not merely on an abstract classification theorem, but on exactly the public `TorsionStructureData` fields expected by `Axioms.lean`.

## Exact mismatch if the proved theorem returns private `TwoInvariantFactorData`

If `TwoInvariantFactors.lean` proves a theorem with the same mathematical content but returning a private structure such as

```lean
private structure TwoInvariantFactorData ...
```

then it is **not definitionally the same type** as the axiom target:

```lean
TorsionStructureData E
```

Even if the private structure has fields morally corresponding to `m`, `n`, positivity, divisibility, an equivalence/classification of the torsion subgroup, and a cardinality formula, Lean will not treat

```lean
TwoInvariantFactorData E
```

as interchangeable with

```lean
TorsionStructureData E
```

because they are different structure constants.  If `TwoInvariantFactorData` is private, the mismatch is worse: downstream files cannot conveniently construct or destruct terms of that private type after importing the module.

So the mismatch is a **return-type mismatch**, not just a theorem-name mismatch:

```lean
-- axiom target, verified:
(E : WeierstrassCurve ℚ) → [E.IsElliptic] → TorsionStructureData E

-- proved theorem, as described by Q1996:
(E : WeierstrassCurve ℚ) → [E.IsElliptic] → TwoInvariantFactorData E
-- or an existential/package involving private TwoInvariantFactorData
```

These are not directly replaceable.

## Likely field-level mismatch

The axiom’s `TorsionStructureData` is tailored to the current `TorsionBound.lean` proof.  Its key fields are weaker/more operational than a standard finite-abelian-group classification package:

```lean
has_structure : HasTorsionStructure E m n
has_point_order_n : HasRationalPointOfOrder E n
card_eq : (torsionSet E).ncard = m * n
```

where

```lean
HasTorsionStructure E m n :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f
```

A natural proved two-invariant-factor theorem is likely to produce something closer to an additive equivalence of the finite torsion subgroup/subtype with `ZMod m × ZMod n`, not exactly this injected-subgroup predicate into all rational points.  Converting that to the axiom shape needs small but real glue:

1. turn an equivalence/classification of the torsion subgroup into an injective additive hom
   ```lean
   ZMod m × ZMod n →+ (E⁄ℚ).Point;
   ```
2. produce a rational point of exact order `n`, typically the image of `(0, 1)` under the inverse equivalence, then coerce from the torsion subtype to `(E⁄ℚ).Point`;
3. translate the subgroup/subtype cardinality theorem into
   ```lean
   (torsionSet E).ncard = m * n;
   ```
4. copy the positivity and divisibility fields.

## Can the axiom be directly replaced?

No, not if the proved theorem returns a private `TwoInvariantFactorData` or any package other than `TorsionStructureData E`.

It needs an adapter theorem whose exported type is exactly the axiom target:

```lean
theorem rational_torsion_two_invariant_factors_adapter
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E := by
  -- obtain the proved two-invariant-factor data
  -- convert its fields to the public Axioms.lean record shape
  -- return the public structure expected by TorsionBound.lean
```

If `TwoInvariantFactorData` is private, the adapter must be written **inside `TwoInvariantFactors.lean`**, before leaving the module where the private structure is visible, or the private structure must be made public/renamed to the public `TorsionStructureData` used by `Axioms.lean`.

After that adapter exists, `Axioms.lean` can replace the axiom by importing the theorem file and defining:

```lean
theorem rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E :=
  rational_torsion_two_invariant_factors_adapter E
```

or, better, give the adapter the exact name `rational_torsion_two_invariant_factors` and remove the axiom entirely.

## Recommendation

Use the public `TorsionStructureData` from `Axioms.lean` as the exported API.  Do not export a theorem whose result type mentions a private `TwoInvariantFactorData`.  Keep any lower-level/private classification package internal, and expose only:

```lean
rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E
```

That is the type `TorsionBound.lean` already consumes.
