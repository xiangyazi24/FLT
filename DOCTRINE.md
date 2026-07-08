# Automode Doctrine: Clear remaining 12 MazurProof sorry's

## Goal

Close all remaining sorry in FLT/Assumptions/MazurProof/.

## Current state (12 sorry in MazurProof/)

| File | sorry | Type |
|------|-------|------|
| CyclicExclusion11 | 2 | Tate bridge + X₁(11) rational points |
| CyclicExclusion14 | 1 | Kubert bridge (cyclic order 14) |
| CyclicExclusion15 | 2 | Tate bridge + X₁(15) rational points |
| CyclicExclusion16 | 1 | Kubert bridge (cyclic order 16) |
| CyclicExclusion18 | 2 | Tate bridge + X₁(18) genus-2 |
| CyclicExclusion21 | 2 | Tate bridge + X₁(21) |
| KubertBridgeN16 | 2 | Kubert discriminant + birational map |

## Avenues (ranked)

### (a) Kubert bridges: CyclicExclusion14 + CyclicExclusion16 (2 sorry)

Both are `cyclic_order_N_kubert_bridge`: from HasRationalPointOfOrder E N,
produce a point on the obstruction curve. These are concrete polynomial
computations in the Tate normal form.

Attack: write the Tate NF parametrization explicitly, compute the
obstruction curve coordinates, verify with ring/norm_num.

Terminal: both sorry's closed, or concrete Lean error identified.

### (b) KubertBridgeN16 (2 sorry)

`kubert_C16_discriminant_data` + `EN16_point_of_Phi16_and_disc`.
These are explicit polynomial computations: from Tate parameters,
extract discriminant data and birational map to obstruction curve.

Terminal: both sorry's closed.

### (c) CyclicExclusion18/21 Diophantine parts (2 sorry)

`no_obstruction18` and `no_obstruction21`: genus-2 Chabauty needed.
ChatGPT confirmed X₁(18) is genus 2. These are the hardest.

Attack: try to formalize the genus-2 argument, or find an elementary
mod-p obstruction, or parametrize and reduce to a simpler curve.

Terminal: sorry closed, or proved infeasible with current Mathlib.

### (d) Tate bridge sorry's (4 sorry across 11/15/18/21)

`order*_to_tate_obstruction`: from HasRationalPointOfOrder, extract
Tate normal form parameters. These need the Tate NF infrastructure
that already exists in the project.

Attack: use existing TateNFDivision.lean infrastructure to build
the bridge.

Terminal: sorry's closed or blocked on missing Tate NF API.

## Fallback

Any sorry closed is permanent progress. Focus on polynomial
computations (avenues a/b) first since they're most concrete.
