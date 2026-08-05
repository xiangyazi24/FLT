# Automode Doctrine: Complete Mazur `|E(ℚ)ₜₒᵣₛ| ≤ 16`

## Goal

Replace every custom axiom reachable from `MazurProof.mazur_torsion_bound` so
its rebuilt `#print axioms` output contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Source-rebuilt state (2026-08-05)

The endpoint has no reachable `sorryAx` and depends on exactly six custom
axioms:

1. `CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
2. `CyclicExclusion17.no_F17_rational_solution`
3. `CyclicExclusion19.no_F19_rational_solution`
4. `CyclicExclusion25.no_explicit_order25_obstruction`
5. `CyclicExclusion49.no_raw_order49_tate_obstruction`
6. `no_prime_order_ge_23`

The older seven-item inventory was wrong: the Vélu two-isogeny quotient for
orders 20 and 24 is proved and no longer an axiom.  The two tracked `sorry`s
in `KubertBridgeN16.lean` are outside the endpoint import closure.

## Ranked avenues

### (a) N17 explicit `X₀(17)` classification

Current active route.  The explicit model, discriminant, standard
two-isogeny, a rational point of exact order four, rational two-torsion
classification, the sharpened abstract exact-sequence/rank criterion, and the
concrete forward/dual additive homomorphisms are proved.  Their composition is
doubling, and the target point killed by the dual is the visible `(0,0)`,
not `(64,0)`.  The nonzero source first-coordinate squareclass is now proved
to be `1` or `17`, and the nonzero target squareclass is proved to be `1` or
`-1`.  Converting those coordinate classes into the chosen `T` and `(0,0)`
cosets was the next explicit task; the target cover by the forward image and
its `(0,0)` translate is now proved, so the left exact-sequence arrow is zero
and the right arrow is injective.  The independent source cover by the dual
image and its `T` translate is also proved.  Consequently `E(ℚ)/2E(ℚ)` has at
most two classes and every point is explicitly a double or `T` plus a double.
The active arithmetic producer is now finite generation from the fixed-`T`
height inequality; rank zero then follows from the proved two-torsion count.
The later torsion bound, modular quotient, and twist/kernel transport remain
separate packages.

### (b) N13 concrete specialization and separatedness

The low-degree spread algebra and the final cusp endgame are largely proved.
The immediate missing case is irreducible-quadratic special restriction on
both charts.  It is followed by concrete relation-first `SpreadData`,
`abel_reduces`, canonical mapped-special equality, and first-jet doubling
compatibility.

### (c) N19 nonsingular Tate locus

The active axiom is stronger than needed.  Preserve the proved exact-order
Tate normalization and reduce to emptiness of the nonsingular rational
`F19 = 0` locus.  Do not substitute the fixed `kernelPoly19` no-root theorem
without a universal modular/fibre map.

### (d) N25 and N49 explicit rational-point obstructions

Both front-end Tate reductions are proved.  The remaining work is the
honest rational-point classification of their explicit obstruction loci;
fixed-fibre computations alone are insufficient.

### (e) Uniform primes `p ≥ 23`

Build the formal-immersion/Eisenstein-ideal argument only from explicit
source-faithful interfaces.  This remains the broadest single axiom.

## Fallbacks and terminal conditions

- If an avenue stalls, change the mathematical attack vector while retaining
  the same theorem; do not weaken the goal or replace it by a new axiom.
- Every banked node must compile in scope, pass the bypass scan, and have a
  clean-3 axiom audit.
- The run terminates only when all six boxes in `MAZUR_CHECKLIST.md` are
  discharged and the rebuilt endpoint axiom audit is clean-3.
