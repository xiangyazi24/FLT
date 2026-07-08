# Session Handoff — 2026-07-08 (Mazur Axiom Elimination)

## Achievement: Axiom Decomposition Complete

`mazur_cyclic_order_bound` (the single axiom) has been decomposed into
13 named sub-axioms via `CyclicOrderAssembly.lean`. Each sub-axiom has
a dedicated `CyclicExclusion*.lean` scaffolding file with the proof
architecture and sorry/axiom stubs.

## New Files This Session (all compile clean)

### 0-sorry infrastructure (Phase 0)
| File | Lines | Content |
|------|-------|---------|
| TateNFDivision | 155 | F5...F15 compact factors, T2, Psi3X, composite obstruction defs |
| CyclicOrderArithmetic | ~200 | Antichain {14,...,49} covers all smooth n>12 + divisor-of-order |
| CyclicOrderAssembly | ~90 | Assembly: 13 sub-axioms → mazur_cyclic_order_bound_assembled |

### Composite exclusion scaffolding
| File | sorry | axiom | Method |
|------|-------|-------|--------|
| CyclicExclusion18 | 2 | 0 | F9=0 + T2 rational root |
| CyclicExclusion20 | 8 | 1 | 2-isogeny quotient → Z/2×Z/10 |
| CyclicExclusion21 | 2 | 0 | F7=0 + Psi3X rational root |
| CyclicExclusion25 | 0 | 1 | Hardest: genus 12, no elliptic bridge |
| CyclicExclusion27 | 1 | 1 | X₀(27) ≅ Fermat cubic + FLT3 |
| CyclicExclusion35 | 0 | 1 | Fiber product X₁(5) ×_j X₁(7) |
| CyclicExclusion49 | 0 | 1 | X₀(49) = 49a1, rank 0 |
| RationalPointsN14 | 1 | 0 | 2-isogeny descent on 96A1 |

### Pre-existing (from prior sessions)
| File | sorry | Method |
|------|-------|--------|
| CyclicExclusion11 | 3 | Tate NF → X₁(11) = 11a3 |
| CyclicExclusion14 | 1 | Kubert bridge to N14 obstruction |
| CyclicExclusion15 | 2 | Tate NF / simultaneous 3+5 |
| CyclicExclusion16 | 1 | Kubert bridge to N16 obstruction |

## Oracle Analysis (ChatGPT × 2 + Fable)

Key findings from the three-way consultation:
1. Composite antichain {14,...,49} confirmed correct and complete
2. No uniform shortcut from real torsion / Weil pairing for cyclic orders
3. n=20,24 reduce to proved noncyclic via 2-isogeny quotient (Fable)
4. n=27 reduces to FLT3 via Fermat cubic (Fable)
5. n=25 has NO rank-0 elliptic bridge — highest risk (Fable)
6. Division polynomials at Tate origin are small: F11=11 terms, F13=20 terms
7. Realistic residual axiom: `no_prime_torsion_ge_13` + possibly `no_order_25`

## Next Steps (priority order)

1. Close RationalPointsN14 sorry (2-isogeny descent, ChatGPT has full certificate)
2. Close CyclicExclusion27 sorry (Fermat cubic ← fermatLastTheoremThree)
3. Close CyclicExclusion20 sorry's (group theory addOrderOf lemmas)
4. Close CyclicExclusion{18,21} sorry's (Tate NF parametrization + Diophantine)
5. Close CyclicExclusion{14,15} sorry's (Kubert bridge, existing pattern)
6. Attack harder targets: n=11 (5-descent), n=16 (genus 2), n=49 (7-Vélu)

## Remote Build

uisai2 at /home/xhuan5/repos/flt-ai. Push to `xiang` remote.
Local `lake build` forbidden (24GB mini). Use `lake env lean` for single-file checks.
