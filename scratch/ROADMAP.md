# Mazur |T| ≤ 16 Formalization Roadmap

## Target

Replace the axiom in `FLT/Assumptions/Mazur.lean`:
```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

## Proof Architecture

```
|T| = m × n  where  T ≅ ℤ/m × ℤ/n,  m | n

Step 1: Weil pairing → m ≤ 2
Step 2: Cyclic bound → n ≤ 16
Step 3: If m = 1: |T| = n ≤ 16  ✓
Step 4: If m = 2: noncyclic bound → n ≤ 8 → |T| = 2n ≤ 16  ✓
```

## Axiom Seams (4 + 3 sub-axioms)

### Top-level axioms

| # | Axiom | Mathematical content | LOC estimate |
|---|-------|---------------------|-------------|
| 1 | `weil_pairing_primitive_root` | Full m-torsion rational → ∃ primitive m-th root in ℚ | 3000-10000 |
| 2 | `torsion_structure` | T ≅ ℤ/m × ℤ/n, card = mn | 500-1500 |
| 3 | `no_rational_point_of_order_ge_17` | No E(ℚ) point of order ≥ 17 | 50000-150000 |
| 4 | `no_Z2_cross_Zn_forbidden` | No ℤ/2 × ℤ/n for n ∈ {10,12,14,16} | 5000-20000 |

### Sub-axioms of Axiom 2

| Sub | Content | Discharge route |
|-----|---------|----------------|
| 2a | `rational_torsion_finite` | Good reduction at 2 primes |
| 2b | `rational_torsion_two_generated` | E[N] ≅ (ℤ/N)² over ℚ̄ |
| 2c | `first_invariant_factor_full` | Structure theorem consequence |

## What Exists Now

| File | Status | Content |
|------|--------|---------|
| `scratch/RootsOfUnityQ.lean` | ✅ Compiled | Only roots of unity in ℚ are ±1 |
| `scratch/MazurSkeleton.lean` | ✅ Compiled | Full |T| ≤ 16 from 4 axioms |

Key Mathlib infrastructure:
- `LinearOrderedRing.orderOf_le_two`: finite order in ℚ → order ≤ 2
- `IsPrimitiveRoot`, `rootsOfUnity`, cyclotomic polynomials
- `WeierstrassCurve`, affine/projective points, group law
- `HasGoodReduction`, `HasMultiplicativeReduction`, reduction predicates
- Division polynomials (basic + degree)
- Finite abelian group structure theorem
- Modular forms (analytic): Eisenstein, q-expansions, cusps

Key MISSING:
- Weil pairing for elliptic curves
- Isogenies
- Modular curves X₀(N), X₁(N) as schemes
- Jacobians of curves
- Néron models
- Tate module

## Implementation Phases

### Phase 1: Skeleton (DONE)
- [x] `RootsOfUnityQ.lean` — real proof
- [x] `MazurSkeleton.lean` — 4 axiom seams, compiles

### Phase 2: Axiom 2 decomposition (~1000 LOC)
- [ ] Decompose `torsion_structure` into 3 sub-axioms
- [ ] Prove `card_eq` from structure + Mathlib finite group API
- [ ] Prove `full_m_torsion` from structure (pure group theory)
- [ ] Prove `has_point_of_order_n` from structure

### Phase 3: Axiom 4 — noncyclic certificates (~5000 LOC)
- [ ] Generate Sage certificates for n = 10, 12, 14, 16
  - n=10: obstruction curve is genus-1, rank 0, only cusps
  - n=12, 14, 16: similar parametric obstructions
- [ ] Formalize in Lean 4:
  - Kubert/Tate normal form for marked torsion
  - Polynomial identity certificates
  - Verified rational-point enumeration on obstruction curves
- [ ] Alternatively: import as axioms with Sage-generated evidence

### Phase 4: Axiom 1 — Weil pairing (~5000 LOC)
- [ ] Define Weil pairing e_n : E[n] × E[n] → μ_n
  - Via Miller's algorithm or divisor theory
  - Need: divisors on elliptic curves, evaluation maps
- [ ] Prove nondegeneracy
- [ ] Prove Galois equivariance
- [ ] Derive: full m-torsion rational → μ_m ⊂ ℚ*

### Phase 5: Axiom 3 — the Mazur core (long-term)
- [ ] This is the full Mazur theorem for cyclic orders
- [ ] Routes: Mazur 1977 (154 pages), or explicit X₁(n) certificates for each n
- [ ] Likely a multi-year project requiring modular curve infrastructure
- [ ] Can be decomposed:
  - Large primes p ≥ 29: formal immersion / Eisenstein ideal argument
  - Medium composites (18-28 with small prime factors): explicit curve certificates

## Dependencies

```
Phase 1 ← nothing (DONE)
Phase 2 ← Mathlib finite abelian group API
Phase 3 ← Phase 2 (need structure to state noncyclic)
Phase 4 ← Mathlib EC point group, divisor theory
Phase 5 ← Phase 4 (Weil pairing), modular curve infrastructure
```

## Risks

1. **Axiom 3 may be infeasible in < 3 years.** The modular-curve infrastructure
   needed (X₀(N) as scheme, Jacobian, Eisenstein ideal, Néron models) is a
   foundational project comparable to building a new Mathlib subdirectory.

2. **Axiom 4 certificates depend on verified arithmetic.** The Sage-generated
   certificates need Lean-side checkers for polynomial identities and
   rational-point enumeration.

3. **FLT project may solve this independently.** Buzzard's team or other
   contributors may tackle Mazur through a different route. Coordinate via
   the FLT Zulip.

## First 30 Days

Week 1-2: Phase 2 (decompose Axiom 2, pure group theory)
Week 3-4: Phase 3 (Sage certificates for Axiom 4, start Lean formalization)

Parallel: engage FLT Zulip to check if others are working on Mazur.
