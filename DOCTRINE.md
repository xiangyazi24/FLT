# Automode Doctrine: Close CyclicExclusion sorry's via ChatGPT harvest

## Goal

Close as many sorry's as possible in the CyclicExclusion files by
dispatching proof questions to ChatGPT Pro and harvesting/wiring results.
Opus orchestrates, ChatGPT produces proofs.

## Current state (125 sorry, 27 axiom in FLT/)

| File | sorry | axiom | Type |
|------|-------|-------|------|
| CyclicExclusion20 | 7 | 1 | Group theory (addOrderOf) |
| CyclicExclusion18 | 2 | 0 | Tate NF + Diophantine |
| CyclicExclusion21 | 2 | 0 | Tate NF + Diophantine |
| CyclicExclusion14 | 1 | 0 | Kubert bridge |
| CyclicExclusion15 | 2 | 0 | Tate NF / X₁(15) |
| CyclicExclusion16 | 1 | 0 | Kubert bridge |
| CyclicExclusion11 | 3 | 0 | 5-isogeny descent |
| RationalPointsN14 | 1 | 0 | 2-isogeny descent (scratch proof exists!) |

## Avenues

### (a) CyclicExclusion20 group-theory sorry's (7 sorry)

Pure addOrderOf lemmas + kernel analysis. ChatGPT should know Mathlib API well.
Questions: image order under quotient by kernel, independence via lift.

Terminal: all 7 sorry → 0 sorry. Or: identify which need axiom.

### (b) CyclicExclusion18/21 Tate NF sorry's (4 sorry)

Parametric computation: Tate normal form with marked N-torsion point.
Concrete polynomial identities.

Terminal: sorry's closed or identified as needing external computation.

### (c) CyclicExclusion14/15/16 Kubert bridge sorry's (4 sorry)

Similar to (b) — modular curve parametrization.

Terminal: sorry's closed.

### (d) Wire scratch/ObstructionN14 into RationalPointsN14 (1 sorry)

The 1924-line proof exists in scratch/ with 0 sorry. Need to either:
- Add scratch to the lake build graph, or
- Extract the key theorem and import it.

Terminal: rank_zero_96a1 sorry closed.

## Method

Dispatch to ChatGPT Pro, harvest, wire into files, verify with `lake env lean`.
Opus does minimal code — just enough to wire ChatGPT's output.
