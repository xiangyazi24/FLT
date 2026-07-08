# Session Handoff — 2026-07-07 (Mazur FLT Formalization)

## Achievement: Single-Axiom Trust Base

`mazur_torsion_bound : |E(ℚ)_tors| ≤ 16` now depends on exactly:

```
#print axioms MazurProof.mazur_torsion_bound =
  [propext, Classical.choice, mazur_cyclic_order_bound, Quot.sound]
```

One mathematical axiom. Everything else is proved.

## The Axiom

```lean
-- FLT/Assumptions/MazurProof/Axioms.lean:288
axiom mazur_cyclic_order_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hord : HasRationalPointOfOrder E n) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)
```

This IS Mazur 1977 Inventiones Theorem 1.

### Decomposition (CyclicOrderReduction.lean)

```
mazur_cyclic_order_bound
  = mazur_prime_torsion_bound         [axiom: prime order ∈ {2,3,5,7}]
  + FutureCompositeExclusions         [parameter: n>12, small prime factors]
  + large prime exclusion             [proved from prime axiom]
```

## What Was Proved This Session (~15K new lines)

### Route 2: Real Topology (complete, 0 sorry, remote build verified)
| File | Lines | Content |
|------|-------|---------|
| RealTopologyS1-S3 | 765 | shortW, componentBit, componentBitHom |
| RealTopologyS4 | 813 | σ integral, halfPeriod, derivatives, limits |
| RealTopologyS5 | 563 | θ candidate + injectivity |
| RealTopologyS6 | 583 | defect framework, AddMonoidHom packaging |
| RealTopologyS7 | 478 | chord calculus, derivative identities |
| RealTopologyS8 | 1300 | local constancy (HasDerivAt=0) |
| RealTopologyS9 | 212 | global glue (IsLocallyConstant + atTop → 0) |
| RealTopologyS10Audit | 100 | API prerequisites |
| RealTopologyS10T2 | 658 | θ(P+T₂) = θ(P)+T (T₂-translation trick) |
| RealTopologyS10Mixed | 1676 | θ(L+U) = θ(L)+θ(U) (mixed additivity) |
| RealTopologyS11Assembly | 600 | ThetaCandidateAdditive (4×4 case bash) |
| RealTorsionBound | 764 | card_E_R_torsion_le + shortW model + harvest |

### Elementary Exclusions (0 sorry)
| File | Lines | Content |
|------|-------|---------|
| NoFull3Torsion | 220 | (ℤ/3)² ⊄ E(ℚ) via ψ₃ Vieta trick |
| NoFull4Torsion | 490 | (ℤ/4)² ⊄ E(ℚ) via halving criterion |
| FullTorsionBound | 158 | m ≤ 2 wiring |
| TorsionFiniteFromOrderBound | 53 | torsion finite via bounded exponent |

### Axioms Eliminated
| Eliminated | Method |
|------------|--------|
| mordell_weil_fg | bounded exponent (N=2520) via Route 2 |
| weil_interface_bridge | trivial: m ≤ 2 → ζ ∈ {±1} |
| kubert_C10_square | TateZ2xZ10Reduction (1540 lines) |
| kubert_C12_square | TateZ2xZ12Reduction (1745 lines) |
| Z2xZ16_gives_non_degenerate | KubertBridgeN16 |

## Next Session Plan

### Oracle-planned attack on mazur_prime_torsion_bound

**Start with /fable-ora 3 rounds**: plan rational ℓ-isogeny descent module.

**Weeks-class (p=11):**
- X₁(11) = 11a3, rank 0, 5-isogeny descent (Billing-Mahler 1940)
- Build reusable "descent via rational ℓ-isogeny" module
- Same module closes n=14, n=15 Diophantine sorry's
- Shrinks axiom to p ≥ 13

**Months-class (p=17,19):**
- X₀(p) elliptic rank 0, 2-isogeny descent
- Shrinks axiom to p ≥ 23

**Years-class (keep as axiom):**
- p = 13: X₁(13) genus 2 (Mazur-Tate 1973)
- p ≥ 23: Eisenstein ideal (Mazur 1977)

## Key Technical Insights

1. **T₂-translation trick** (Fable oracle): θ(P+T₂)=θ(P)+T has empty bad
   set; mixed additivity has built-in anchor. Eliminates atTop + doubling seam.

2. **Bounded exponent kills Mordell-Weil**: order ∈ {1,...,12} →
   addOrderOf | 2520 → E(Q)_tors ⊆ E(Q)[2520] → finite via Route 2.

3. **Convention**: shortCubic A B x = x³+Ax²+Bx. shortW A B has a₂=A, a₄=B.

4. **Tate NF reduction template**: TateZ2xZ10Reduction (1540 lines) and
   TateZ2xZ12Reduction (1745 lines) are reusable patterns.

5. **Remote build**: uisai2 at /home/xhuan5/repos/flt-ai.
   Push to `xiang`, `git reset --hard xiang/ai-scratch`.

## Active Import Chain

```
TorsionBound.lean
├── TorsionFiniteFromOrderBound.lean
│   ├── Axioms.lean (mazur_cyclic_order_bound — THE axiom)
│   └── RealTorsionBound.lean → RealTopologyS1-S11 (all 0 sorry)
├── Axioms.lean
│   ├── NoncyclicN10 → DescentBridge → KubertBridgeN10 → TateZ2xZ10Reduction
│   │                → DescentBridgeN12 → KubertBridgeN12 → TateZ2xZ12Reduction
│   ├── RealTorsionBridge, TwoInvariantFactors, GroupTheory
│   └── (no mordell_weil_fg anywhere)
└── RealTorsionBound.lean
```

## Files NOT on Active Path (future work)

- CyclicExclusion{11,14,15,16}.lean — sorry scaffolding for composite orders
- CyclicOrderReduction.lean — prime axiom decomposition
- KubertBridgeN16.lean — N=16 infrastructure (2 sorry)
- DescentBridgeN14.lean — 2 axioms (non-critical)
- OrderReduction.lean — duplicate axiom (cleanup)
- TorsionFinite.lean — dead code (mordell_weil_fg)
- WeilPairingInterface.lean — closed (0 sorry, historical)
