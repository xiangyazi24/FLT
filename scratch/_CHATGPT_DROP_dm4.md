# Q1996 (dm4): actual axiom dependencies of `mazur_torsion_bound`

Scope checked:

```text
branch: ai-scratch
main theorem file: FLT/Assumptions/MazurProof/TorsionBound.lean
axiom assembly file: FLT/Assumptions/MazurProof/Axioms.lean
```

I traced the source-level dependency chain starting at

```lean
theorem mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

## Executive answer

In the current source, the project-level axioms actually reached by `mazur_torsion_bound` are:

1. `mordell_weil_fg`  **only through an unused `_hfinite` binding**
2. `rational_torsion_two_invariant_factors`
3. `weil_pairing_primitive_root`
4. `no_rational_point_of_order_ge_17`
5. `obstruction_curve_20a4_points_degenerate`
6. `Z2xZ10_gives_non_degenerate_E20_point`
7. `obstruction_curve_N12_points_degenerate`
8. `Z2xZ12_gives_non_degenerate_N12_point`
9. `obstruction_curve_N14_points_degenerate`
10. `Z2xZ14_gives_non_degenerate_N14_point`
11. `obstruction_curve_N16_points_degenerate`
12. `Z2xZ16_gives_non_degenerate_N16_point`

So, among the source files read here, there are **12 source-level project axioms in the dependency chain**, but `mordell_weil_fg` is not mathematically needed for the proof as written: it enters only because `mazur_torsion_bound` contains

```lean
have _hfinite := rational_torsion_finite_alias E
```

and `_hfinite` is never used afterwards.  If that line and the `TorsionFinite` import are removed, the visible project-axiom dependency list should drop from 12 to 11.

## Direct calls made by `mazur_torsion_bound`

The main theorem does these source-level calls:

```lean
have _hfinite := rational_torsion_finite_alias E
let d := rational_torsion_two_invariant_factors E
have hm_le : d.m ≤ 2 :=
  full_rational_torsion_order_le_two E d.m_pos
    (first_invariant_factor_full_torsion E d.m_pos d.n_pos d.dvd_mn d.has_structure)
have hn_le : d.n ≤ 16 := n_le_sixteen_of_structure E d
...
exact no_Z2_cross_Zn_forbidden E hforbidden hcontains
```

That is enough to determine the axiom graph.

## Exact dependency graph

```text
mazur_torsion_bound
├─ rational_torsion_finite_alias E
│  └─ mordell_weil_fg E
│     NOTE: this entire branch is bound to `_hfinite` and not used later.
│
├─ rational_torsion_two_invariant_factors E
│  └─ AXIOM: rational_torsion_two_invariant_factors
│
├─ full_rational_torsion_order_le_two E d.m_pos (...)
│  ├─ weil_pairing_primitive_root E d.m_pos hfull
│  │  └─ AXIOM: weil_pairing_primitive_root
│  └─ isPrimitiveRoot_rat_order_le_two
│     └─ proved in RootsOfUnity.lean; no project axiom
│
├─ first_invariant_factor_full_torsion E d.m_pos d.n_pos d.dvd_mn d.has_structure
│  └─ zmod_prod_contains_square
│     └─ zmod_contains_of_dvd
│        └─ proved in GroupTheory.lean; no project axiom
│
├─ n_le_sixteen_of_structure E d
│  └─ no_rational_point_of_order_ge_17 E hn d.has_point_order_n
│     └─ AXIOM: no_rational_point_of_order_ge_17
│
└─ no_Z2_cross_Zn_forbidden E hforbidden hcontains
   ├─ branch n = 10
   │  └─ no_Z2_cross_Z10 E
   │     └─ no_Z2_cross_Z10_from_descent E
   │        ├─ AXIOM: Z2xZ10_gives_non_degenerate_E20_point
   │        └─ AXIOM: obstruction_curve_20a4_points_degenerate
   │
   ├─ branch n = 12
   │  └─ no_Z2_cross_Z12 E
   │     └─ no_Z2_cross_Z12_from_descent E
   │        ├─ AXIOM: Z2xZ12_gives_non_degenerate_N12_point
   │        └─ AXIOM: obstruction_curve_N12_points_degenerate
   │
   ├─ branch n = 14
   │  └─ no_Z2_cross_Z14 E
   │     └─ no_Z2_cross_Z14_from_descent E
   │        ├─ AXIOM: Z2xZ14_gives_non_degenerate_N14_point
   │        └─ AXIOM: obstruction_curve_N14_points_degenerate
   │
   └─ branch n = 16
      └─ no_Z2_cross_Z16 E
         └─ no_Z2_cross_Z16_from_descent E
            ├─ AXIOM: Z2xZ16_gives_non_degenerate_N16_point
            └─ AXIOM: obstruction_curve_N16_points_degenerate
```

Important point: all four `{10,12,14,16}` bridge branches are live because `mazur_torsion_bound` calls the generic theorem

```lean
no_Z2_cross_Zn_forbidden
```

and that theorem proof explicitly cases on the disjunction and invokes all four branch theorems.

## Per-axiom notes

### `mordell_weil_fg`

Declared in `TorsionFinite.lean`:

```lean
axiom mordell_weil_fg (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point
```

Reached by:

```text
mazur_torsion_bound
└─ rational_torsion_finite_alias
   └─ mordell_weil_fg
```

But the resulting hypothesis is stored as `_hfinite` and not used in the rest of the proof.  This is the best candidate for immediate cleanup.

### `rational_torsion_two_invariant_factors`

Declared in `Axioms.lean`:

```lean
axiom rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E
```

Reached directly by:

```text
mazur_torsion_bound
└─ let d := rational_torsion_two_invariant_factors E
```

This is essential: every later numeric argument uses `d.m`, `d.n`, `d.dvd_mn`, `d.has_structure`, `d.has_point_order_n`, and `d.card_eq`.

### `weil_pairing_primitive_root`

Declared in `Axioms.lean`:

```lean
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Reached by:

```text
mazur_torsion_bound
└─ full_rational_torsion_order_le_two
   └─ weil_pairing_primitive_root
```

This is essential for proving `d.m ≤ 2`.

### `no_rational_point_of_order_ge_17`

Declared in `Axioms.lean`:

```lean
axiom no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n
```

Reached by:

```text
mazur_torsion_bound
└─ n_le_sixteen_of_structure
   └─ no_rational_point_of_order_ge_17
```

This is essential for proving `d.n ≤ 16`.

### N = 10 bridge axioms

Declared in `DescentBridge.lean`:

```lean
axiom obstruction_curve_20a4_points_degenerate :
    ∀ u w : ℚ, E20AffineEquation u w → E20DegenerateParameter u

axiom Z2xZ10_gives_non_degenerate_E20_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E20AffineEquation u w ∧ ¬ E20DegenerateParameter u
```

Reached by:

```text
mazur_torsion_bound
└─ no_Z2_cross_Zn_forbidden
   └─ no_Z2_cross_Z10
      └─ no_Z2_cross_Z10_from_descent
         ├─ Z2xZ10_gives_non_degenerate_E20_point
         └─ obstruction_curve_20a4_points_degenerate
```

### N = 12 bridge axioms

Declared in `DescentBridgeN12.lean`:

```lean
axiom obstruction_curve_N12_points_degenerate :
    ∀ u w : ℚ, E_N12_AffineEquation u w → E_N12_DegenerateParameter u

axiom Z2xZ12_gives_non_degenerate_N12_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u
```

Reached by:

```text
mazur_torsion_bound
└─ no_Z2_cross_Zn_forbidden
   └─ no_Z2_cross_Z12
      └─ no_Z2_cross_Z12_from_descent
         ├─ Z2xZ12_gives_non_degenerate_N12_point
         └─ obstruction_curve_N12_points_degenerate
```

### N = 14 bridge axioms

Declared in `DescentBridgeN14.lean`:

```lean
axiom obstruction_curve_N14_points_degenerate :
    ∀ u w : ℚ, E_N14_AffineEquation u w → E_N14_DegenerateParameter u

axiom Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u
```

Reached by:

```text
mazur_torsion_bound
└─ no_Z2_cross_Zn_forbidden
   └─ no_Z2_cross_Z14
      └─ no_Z2_cross_Z14_from_descent
         ├─ Z2xZ14_gives_non_degenerate_N14_point
         └─ obstruction_curve_N14_points_degenerate
```

### N = 16 bridge axioms

Declared in `DescentBridgeN16.lean`:

```lean
axiom obstruction_curve_N16_points_degenerate :
    ∀ u w : ℚ, E_N16_AffineEquation u w → E_N16_DegenerateParameter u

axiom Z2xZ16_gives_non_degenerate_N16_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u
```

Reached by:

```text
mazur_torsion_bound
└─ no_Z2_cross_Zn_forbidden
   └─ no_Z2_cross_Z16
      └─ no_Z2_cross_Z16_from_descent
         ├─ Z2xZ16_gives_non_degenerate_N16_point
         └─ obstruction_curve_N16_points_degenerate
```

## Dead or not-needed code, relative to `mazur_torsion_bound`

### Semantically dead but source-referenced

```lean
have _hfinite := rational_torsion_finite_alias E
```

This line pulls in:

```text
rational_torsion_finite_alias
└─ mordell_weil_fg
```

but `_hfinite` is never used.  The proof already gets the finite cardinality information it needs from

```lean
d.card_eq : (torsionSet E).ncard = d.m * d.n
```

inside `TorsionStructureData`.

Suggested cleanup:

```diff
- import FLT.Assumptions.MazurProof.TorsionFinite
...
-   have _hfinite := rational_torsion_finite_alias E
```

After this cleanup, `mordell_weil_fg` should disappear from this theorem's project-axiom dependency chain.

### Pure helper declarations not on the path

In `RootsOfUnity.lean`, these are not used by `mazur_torsion_bound`:

```lean
rat_root_of_unity_eq_one_or_neg_one
rat_root_of_unity_exists_eq_one_or_neg_one
```

The theorem that *is* used is only:

```lean
isPrimitiveRoot_rat_order_le_two
```

In `GroupTheory.lean`, the path used by `mazur_torsion_bound` is only:

```text
first_invariant_factor_full_torsion
└─ zmod_prod_contains_square
   └─ zmod_contains_of_dvd
```

The other embedding helpers in `GroupTheory.lean` are currently dead relative to this theorem, though they may be useful elsewhere.

## Bottom line

No declared bridge axiom for N = 10, 12, 14, or 16 is dead with respect to the current `mazur_torsion_bound`; all are reached through the generic forbidden-even case split.

The one cleanup opportunity is the unused torsion-finiteness line.  Removing it should eliminate the `mordell_weil_fg` dependency from `mazur_torsion_bound` without changing the proof logic.
