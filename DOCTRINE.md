# Automode Doctrine: Complete Mazur `|E(ℚ)ₜₒᵣₛ| ≤ 16`

## Goal

Replace every custom axiom reachable from `MazurProof.mazur_torsion_bound` so
its rebuilt `#print axioms` output contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Source-rebuilt state (2026-08-09)

The endpoint has no reachable `sorryAx` and depends on exactly four custom
axioms:

1. `CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
2. `CyclicExclusion25.no_explicit_order25_obstruction`
3. `CyclicExclusion49.no_raw_order49_tate_obstruction`
4. `no_prime_order_ge_23`

Orders 17 and 19 are now proved by direct quotient and rational-point
classifications.  The Vélu two-isogeny quotient for orders 20 and 24 is also
proved.  The two tracked `sorry`s in `KubertBridgeN16.lean` are outside the
endpoint import closure.

## Ranked avenues

### (a) N25 finite-field and Jacobian reduction route

Current active route.  The primitive Tate obstruction already maps to the
checked canonical genus-four quotient and avoids all five rational cusps.
The complete executable field tables and projective counts over
`F_2,F_4,F_8,F_16` are certified as `5,5,20,29`.  Four chartwise Bézout
identities exclude the explicit complete-intersection singularity predicate
over every characteristic-two field.  Newton's identities and genus-four
reciprocity give the exact candidate Weil numerator, with value `71` at one.
The remaining geometric seam is to connect these explicit certificates to a
smooth proper genus-four special fibre and the general theorem
`#Jac(C)(F_2)=P(1)`.  The global seam needs rational rank zero and two good
reductions: reduction at two alone does not exclude two-primary torsion.
The leading candidates use either the degree-two map from `X_1(25)` or its
level-25 newform factor.  The corrected primary source has now been verified:
`J_1(25)(Q)` has rank zero and is cyclic of order `227555`; the exact
four-conjugate newform polynomial at three is also kernel-checked and has
value `71` at one.  The pure two-prime cardinal-divisibility endgame is proved
as well, including the kernel-range formula that derives each local bound
from a finite reduction map with primary kernel.  Neither route is counted at
the endpoint until the
required modular quotient/newform, specialization, and Abel--Jacobi
infrastructure is formalized.  Closing these seams forces every rational
canonical point to be a cusp, contradicting the proved noncuspidality of the
primitive Tate image.

### (b) N13 concrete specialization and separatedness

The low-degree spread algebra, complete rational Picard spread existence,
vertical saturation of every constructor, certified exact-spread choice, and
the final cusp endgame are proved.  The endpoint now has exactly two explicit
providers: `class_eq_iff` for concrete rational spread lines and first-jet
doubling compatibility for the canonical recovered representatives.

### (c) N49 explicit rational-point obstruction

The front-end Tate reduction is proved.  The terminal condition is the honest
rational-point classification of the relevant modular quotient plus a
universal Tate-to-modular map excluding its cusps; fixed-fibre computations
alone are insufficient.

### (d) Uniform primes `p ≥ 23`

Build the formal-immersion/Eisenstein-ideal argument only from explicit
source-faithful interfaces.  This remains the broadest single axiom.

## Fallbacks and terminal conditions

- If an avenue stalls, change the mathematical attack vector while retaining
  the same theorem; do not weaken the goal or replace it by a new axiom.
- Every banked node must compile in scope, pass the bypass scan, and have a
  clean-3 axiom audit.
- The run terminates only when all four remaining boxes in
  `MAZUR_CHECKLIST.md` are discharged and the rebuilt endpoint axiom audit is
  clean-3.
