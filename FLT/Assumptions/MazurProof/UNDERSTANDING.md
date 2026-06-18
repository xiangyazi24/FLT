# UNDERSTANDING.md — Mazur |T| ≤ 16 Proof Framework

## Goal

Prove `(AddCommGroup.torsion (E⁄ℚ).Point : Set).ncard ≤ 16` for any
elliptic curve `E` over `ℚ`, replacing the axiom in `FLT/Assumptions/Mazur.lean`.

## Proof Structure

```
                    ┌─────────────────────┐
                    │  |T| = m * n ≤ 16   │
                    └──────────┬──────────┘
                               │
                 ┌─────────────┴─────────────┐
                 │                           │
          m = 1: |T| = n              m = 2: |T| = 2n
          need n ≤ 16                 need n ≤ 8
                 │                           │
                 │                    ┌──────┴──────┐
                 │                    │             │
              Axiom 3:            Axiom 3:      Axiom 4:
           n ≤ 16 from         n ≤ 16 from    n ≤ 8 from
          "no order ≥17"      "no order ≥17"  "no ℤ/2×ℤ/n
                                               n∈{10,12,14,16}"

          ┌──────────────────────────────────────────┐
          │        Weil pairing → m ≤ 2              │
          │                                          │
          │  Axiom 1: full m-torsion → prim root     │
          │  RootsOfUnity: prim root in ℚ → m ≤ 2   │  ← PROVED
          └──────────────────────────────────────────┘

          ┌──────────────────────────────────────────┐
          │      Torsion structure: T ≅ ℤ/m × ℤ/n   │
          │                                          │
          │  Axiom 2a: T is finite                   │
          │  Axiom 2b: T has rank ≤ 2                │
          │  Axiom 2c: first factor gives full tors  │
          └──────────────────────────────────────────┘
```

## Dependency Graph (discharge order)

```
Level 0 (DONE):
  RootsOfUnity.lean  ← real proof, no axioms

Level 1 (pure group theory, ~1000 LOC):
  Axiom 2c (first_invariant_factor_full)
    depends on: finite abelian group structure theorem (Mathlib)
  
Level 2 (EC arithmetic, ~5000 LOC each):
  Axiom 2a (rational_torsion_finite)
    depends on: good reduction injection (EC reduction API)
  Axiom 2b (rational_torsion_two_generated)
    depends on: E[N] ≅ (ℤ/N)² over algebraic closure
  Axiom 1 (weil_pairing_primitive_root)
    depends on: Weil pairing construction, divisor theory

Level 3 (explicit certificates, ~10000 LOC):
  Axiom 4 (no_Z2_cross_Zn_forbidden)
    depends on: Kubert/Tate normal form parametrization
    discharge via: obstruction curve rational points
      N=10: LMFDB 20.a4, rank 0, MW = ℤ/6ℤ
      N=12, 14, 16: similar obstruction curves (Sage certificates)

Level 4 (deep Mazur, ~100000 LOC):
  Axiom 3 (no_rational_point_of_order_ge_17)
    depends on: modular curves X₁(n), Jacobians, Eisenstein ideal,
                OR explicit X₁(n) certificates for n = 17..28 + formal immersion for p ≥ 29
```

## Files

```
FLT/Assumptions/MazurProof/
  RootsOfUnity.lean     ← PROVED: ℚ roots of unity = {±1}
  Axioms.lean           ← All axiom declarations (Groups A-D)
  TorsionBound.lean     ← Main theorem: |T| ≤ 16 from axioms
  MazurProof.lean       ← Module import file

Future (as axioms are discharged):
  TorsionStructure.lean ← Axiom 2 discharge
  WeilPairing.lean      ← Axiom 1 discharge
  NoncyclicCert.lean    ← Axiom 4 discharge (+ Sage certificates)
  CyclicBound.lean      ← Axiom 3 discharge (the big one)
```

## Key Design Decisions

1. **Axioms as seams, not sorry.** Each axiom is a self-contained mathematical
   theorem that can be independently proved and tested. This matches Buzzard's
   own FLT methodology (see FLT/Assumptions/README.md).

2. **Opaque predicates.** `HasFullRationalTorsion`, `HasRationalPointOfOrder`,
   etc. are opaque Props. This prevents the skeleton proof from depending on
   implementation details of the torsion API, which is still developing.

3. **Card = m * n in the structure axiom.** Without this, converting between
   the group-theoretic structure and `Set.ncard` requires substantial API work.
   It's a mathematical consequence of the structure theorem, not an extra
   assumption.

4. **Weil pairing returns a primitive root, not directly m ≤ 2.** This is the
   natural mathematical seam — the Weil pairing produces the root, and the
   ordered-field argument (already proved) gives m ≤ 2. Bundling them would
   make the axiom harder to discharge.

## Noncyclic Certificate Details (Axiom 4)

For each n ∈ {10, 12, 14, 16}, the proof that ℤ/2 × ℤ/n ⊄ E(ℚ)_tors follows:

1. Parametrize all E/ℚ with full 2-torsion + order n/gcd(2,n) point
   (Kubert family / Tate normal form)
2. The parametrization gives a one-parameter family over ℚ
3. Full 2-torsion imposes a discriminant-square condition
4. This defines an obstruction curve C over ℚ
5. Show C(ℚ) consists only of degenerate/cuspidal points

For N=10: obstruction curve is LMFDB 20.a4 (y² = x³ + x² - x),
MW group = ℤ/6ℤ (rank 0), rational points u ∈ {-1, 1, 3} are all cusps.

## Progress Log (2026-06-17 automode session)

### Proved (0 sorry, 0 axiom — real Lean theorems):
1. **RootsOfUnity.lean**: isPrimitiveRoot_rat_order_le_two, rat_root_of_unity_eq_one_or_neg_one
2. **TorsionFinite.lean**: torsion_set_finite_of_fg (Noetherian ℤ-module → torsion submodule f.g. → finite)
3. **GroupTheory.lean**: zmod_prod_contains_square ((ℤ/m)² ↪ ℤ/m × ℤ/n when m|n)
4. **CyclotomicLayer.lean**: primitive_root_forces_le_two interface
5. **ZModEmbedding.lean** (scratch): same as GroupTheory content

### Proved from axioms (skeleton):
6. **TorsionBound.lean**: mazur_torsion_bound (|T| ≤ 16 from 6 axiom seams)

### Verified computation:
7. **DescentObstruction.lean**: N=10 2-isogeny local obstructions via native_decide
8. **ObstructionN10Complete.lean**: curve 20.a4 rational point verification

### Axiom seams remaining:
- mordell_weil_fg (standard, in TorsionFinite.lean)
- weil_pairing_primitive_root (needs EC Weil pairing or det = χ_m)
- rational_torsion_two_invariant_factors (needs E[m] ≅ (ℤ/m)²)
- cyclic_order_allowed (needs Mazur cyclic classification or X_1(n) certificates)
- no_Z2_cross_Z10 (needs obstruction curve 20.a4 rank-0 certificate)
- no_Z2_cross_Z12 (needs obstruction curve rank-0 certificate)

### Key design decisions:
- Refactored cyclic bound to Mazur classification (n ∈ {1..10,12}) — eliminates N=14, N=16 noncyclic cases
- Weil pairing axiom seam at the primitive-root level (not m ≤ 2 directly)
- TorsionFinite discharge: mordell_weil_fg → Noetherian → f.g. torsion → finite (real proof)
- N=10 descent: LMFDB 20.a4, MW = ℤ/6ℤ, rank 0, local obstructions mod 125
