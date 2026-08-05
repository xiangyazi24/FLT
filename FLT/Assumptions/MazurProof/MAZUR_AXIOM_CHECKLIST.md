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

Their reachable custom-axiom ledger has exactly five entries:

1. `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
   in `CyclicExclusion13.lean`;
2. `MazurProof.CyclicExclusion19.no_F19_rational_solution`
   in `CyclicExclusion19.lean`;
3. `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`
   in `CyclicExclusion25.lean`;
4. `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
   in `CyclicExclusion49.lean`;
5. `MazurProof.no_prime_order_ge_23`
   in `CyclicOrderAssembly.lean`.

Apart from these five declarations, the audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  It reports no reachable `sorryAx`.

## Newly discharged: order seventeen

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

## Declarations present in the tree but not reachable from the endpoint

These custom axioms remain in older or alternative routes, but the rebuilt
main theorem does not depend on them:

- `CyclicOrderReduction.mazur_prime_torsion_bound`;
- `OrderReduction.mazur_cyclic_order_bound`;
- `TorsionFinite.mordell_weil_fg`.

The two tracked proof placeholders in `KubertBridgeN16.lean` are likewise not
reachable from the current endpoint.  They must not be counted as completed
work, but they are not part of the five-entry endpoint ledger.

## Next discharge order

The five remaining assumptions are independent named arithmetic inputs.
The finite cases should be attacked before the uniform tail:

1. finish the rational-point classification on the order-thirteen sextic;
2. prove the order-nineteen Tate residual has no nondegenerate rational zero;
3. close the explicit order-twenty-five obstruction;
4. close the raw order-forty-nine Tate obstruction;
5. formalize the uniform prime-order exclusion for `p ≥ 23`.

Any future count must come from a fresh source rebuild of every changed
downstream module followed by `#print axioms`; stale `.olean` files can retain
already removed axiom dependencies.
