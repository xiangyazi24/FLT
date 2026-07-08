# Automode Doctrine: Eliminate mazur_cyclic_order_bound axiom

## Goal

Replace `axiom mazur_cyclic_order_bound` with a theorem proved from
named sub-axioms (one per excluded order + prime tail), then close
as many sub-axioms as possible.

## Avenues (ranked by dependency order)

### (a) Arithmetic foundation + Phase 0 decomposition

1. Close `exists_minimalBadComposite_dvd` sorry (pure arithmetic)
2. Wire: prime bound axiom + 11 composite exclusion axioms → theorem
3. Result: monolithic axiom → 12 named sub-axioms

Terminal: `mazur_cyclic_order_bound` is a theorem, depends on 12 named axioms.

### (b) Close composite exclusions in order: 14, 15, 18, 20, 21, 24

Each follows the Tate NF pattern (TateNFDivision.lean infrastructure).
- n=14: F7=0 + 2-torsion → obstruction curve (1 sorry in CyclicExclusion14)
- n=15: F15=0 or simultaneous 3+5 → X₁(15) (2 sorry in CyclicExclusion15)
- n=18: F9=0 + 2-torsion → new file needed
- n=20: degree-2 Vélu → Z/2×Z/10 (FREE, already proved)
- n=21: F7=0 + 3-torsion → new file needed
- n=24: degree-2 Vélu → Z/2×Z/12 (FREE, already proved)

Terminal: all 6 cyclic exclusion sorry's closed.

### (c) Close n=11 prime exclusion

F11(b,c)=0 → birational to X₁(11) = 11a3.
Needs 5-isogeny descent (Billing-Mahler style).
2 sorry in CyclicExclusion11.

Terminal: both sorry's closed.

### (d) Close n=16, 27, 49, 35, 25

- n=16: ψ₁₆=0 ∧ ψ₈≠0 → genus-2 curve (1 sorry in CyclicExclusion16)
- n=27: degree-3 Vélu → Fermat cubic → Mathlib FLT3
- n=49: degree-7 Vélu → 49a1 2-descent
- n=35: X₀(35) → 35a1 3-descent
- n=25: hardest, no elliptic bridge exists

Terminal: as many as possible; n=25 + prime p≥13 likely stay as axioms.

## Fallback

Any sub-axiom closed is permanent progress. The residual axiom set
is strictly smaller than the original monolithic axiom.
