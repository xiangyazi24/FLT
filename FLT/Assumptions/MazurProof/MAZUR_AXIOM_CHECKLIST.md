# Mazur torsion bound: exact discharge ledger

Goal: prove `MazurProof.mazur_torsion_bound_ncard` with no custom axioms and
no reachable `sorryAx`.

Last source rebuild and `#print axioms` audit: 2026-08-05.

## Current endpoint

The main numerical theorem and its cyclic-order input compile from source:

- `MazurProof.mazur_cyclic_order_bound_assembled`
- `MazurProof.rational_torsion_finite`
- `MazurProof.mazur_torsion_bound`
- `MazurProof.mazur_torsion_bound_ncard`

Their reachable custom-axiom ledger has exactly four entries:

1. `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
   in `CyclicExclusion13.lean`;
2. `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`
   in `CyclicExclusion25.lean`;
3. `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
   in `CyclicExclusion49.lean`;
4. `MazurProof.no_prime_order_ge_23`
   in `CyclicOrderAssembly.lean`.

Apart from these four declarations, the audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  It reports no reachable `sorryAx`.

## Newly discharged: orders seventeen and nineteen

`CyclicExclusion17.no_F17_rational_solution` is now a theorem, not an axiom.
The source proof in `TateOrder17Quotient.lean`:

1. normalizes the exact Tate residual `F₁₇(b,c)`;
2. proves all exceptional denominator factors nonzero by explicit polynomial
   identities;
3. maps the normalized point through three checked degree-two formulas to the
   integral `X₀(17)` model;
4. uses the completed four-point classification of
   `X017RationalPoints.lean`;
5. excludes the two remaining affine fibres by a monic quartic with no root
   modulo three and by the nonsquareness of seventeen in `ℚ`.

The theorem
`MazurProof.TateOrder17Quotient.no_F17_rational_solution` depends only on the
three standard logical axioms above.

`CyclicExclusion19.no_F19_rational_solution` is also now a theorem.  The
source proof:

1. completes both rational-flex degree-three isogeny descents on the
   good-reduction model;
2. combines weak three-descent with three-adic formal entry and separatedness
   to prove that every good-model rational point is killed by three;
3. classifies every affine good-model point by its first coordinate;
4. transports the classification through the scaled dual, short, and minimal
   quotient models; and
5. applies the checked algebraic Tate-to-diamond quotient identities to
   exclude every nondegenerate zero of `F₁₉`.

`MazurProof.XDelta19RationalPoints.no_F19_rational_solution` and the public
cyclic exclusion depend only on the three standard logical axioms above.

## Order-twenty-five foundation

The local source tree now contains a checked canonical model for the
genus-four quotient `25.150.4.f.1`.  The N25 files prove:

1. the exact quadric-cubic equations, the five rational cusp vectors, and
   elimination to a plane sextic away from the boundary;
2. an explicit order-five automorphism preserving the model, together with
   its basic homogeneous invariants; and
3. exhaustive projective classifications over `𝔽₂` and `𝔽₄`, showing that
   the quadratic extension introduces no new class.

These theorems compile and depend only on the three standard logical axioms.
They do not yet discharge N25: the missing inputs are the exact
Tate-obstruction-to-canonical-model map and a global rational-point or
formal-immersion argument over `ℚ`.

## Declarations present in the tree but not reachable from the endpoint

These custom axioms remain in older or alternative routes, but the rebuilt
main theorem does not depend on them:

- `CyclicOrderReduction.mazur_prime_torsion_bound`;
- `OrderReduction.mazur_cyclic_order_bound`;
- `TorsionFinite.mordell_weil_fg`.

The two tracked proof placeholders in `KubertBridgeN16.lean` are likewise not
reachable from the current endpoint.  They must not be counted as completed
work, but they are not part of the four-entry endpoint ledger.

## Next discharge order

The four remaining assumptions are independent named arithmetic inputs.
The finite cases should be attacked before the uniform tail:

1. finish the rational-point classification on the order-thirteen sextic;
2. close the explicit order-twenty-five obstruction;
3. close the raw order-forty-nine Tate obstruction;
4. formalize the uniform prime-order exclusion for `p ≥ 23`.

Any future count must come from a fresh source rebuild of every changed
downstream module followed by `#print axioms`; stale `.olean` files can retain
already removed axiom dependencies.
