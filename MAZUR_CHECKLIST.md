# Mazur Endpoint Checklist

Last source-rebuilt audit: 2026-08-05.

The authoritative endpoint is `MazurProof.mazur_torsion_bound`.  A box may be
checked only after the replacement theorem is reachable from that endpoint,
scoped builds pass, and `#print axioms` contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Primitive endpoint axioms

- [ ] N13 — `CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
  - Closed infrastructure: low-degree proper spreads; complete degree-one and
    split/repeated-root two-fibre Picard data; 19-element special Abel set;
    selected quotient basis; graph/disk-pair recovery; abstract classifier;
    final rational-point-to-cusp implication.
  - Immediate open atom: irreducible-quadratic special restriction on both
    charts.
  - Remaining semantic atoms: either pointwise specialization reflection on
    rational Abel classes, or the stronger concrete `SpreadData` plus
    `abel_reduces`, canonical mapped-special equality, and first-jet doubling
    compatibility.

- [ ] N17 — `CyclicExclusion17.no_F17_rational_solution`
  - Closed infrastructure: exact-order Tate normalization with preserved
    `j`; explicit `X₀(17)` model and standard two-isogeny; visible point of
    exact order four; rational two-torsion has cardinality two; sharpened
    exact-sequence and general rank-zero criterion; concrete forward and dual
    additive homomorphisms with dual-forward composition equal to doubling;
    nonzero source first-coordinate squareclasses restricted to `1` and `17`;
    nonzero target first-coordinate squareclasses restricted to `1` and `-1`;
    explicit target quotient cover by the forward-isogeny image and its
    translate by `(0,0)`, hence zero left exact-sequence arrow and injective
    right arrow; explicit source quotient cover by the dual image and its
    translate by `T`; source modulo doubling has at most two classes and is
    explicitly covered by `0,T`;
    two-coset height-descent wrapper reducing finite generation to one fixed
    translation estimate; good-fibre point counts
    `#X₀(17)(𝔽₂)=#X₀(17)(𝔽₃)=4`.
  - Open arithmetic atoms: finite generation from the fixed-`T` height
    inequality and dependency-clean height infrastructure; good-reduction
    torsion injection; and the rational-point classification.
  - Open geometric atoms: the Tate `X₁(17) → X₀(17)` quotient with cusp and
    `j` control, then twist/model/kernel transport for the two noncuspidal
    fibres.

- [ ] N19 — `CyclicExclusion19.no_F19_rational_solution`
  - Closed infrastructure: Tate exact-order normalization and fixed
    `kernelPoly19` no-root tail.
  - Open atom: emptiness of the nonsingular rational Tate `F19 = 0` locus.
    A universal map is required before the fixed-fibre polynomial can be
    consumed.

- [ ] N25 — `CyclicExclusion25.no_explicit_order25_obstruction`
  - Closed infrastructure: explicit primitive order-25 obstruction.
  - Open atom: rational-point exclusion for that explicit locus.

- [ ] N49 — `CyclicExclusion49.no_raw_order49_tate_obstruction`
  - Closed infrastructure: structural `ψ₄₉` factorization bridge to the
    explicit obstruction.
  - Open atoms: rational-point classification of `X₀(49)` and the universal
    Tate-to-modular map with cusp exclusion.

- [ ] Large primes — `no_prime_order_ge_23`
  - Open atom family: formal-immersion/Eisenstein-ideal exclusion uniformly
    for primes at least 23.

## Cross-cutting checks

- [x] Endpoint has no reachable `sorryAx`.
- [x] Orders 11, 14, 15, 16, 18, 20, 21, 24, 27, and 35 are discharged from
  the endpoint.
- [x] The order-20/order-24 Vélu two-isogeny quotient is a theorem, not an
  axiom.
- [x] The two tracked `KubertBridgeN16` `sorry`s are outside the endpoint
  import closure.
- [ ] Rebuild the final endpoint and obtain a clean-3 axiom audit after all
  six primitive boxes are checked.

Scoreboard: **0 / 6 primitive endpoint axioms discharged** in the current
source-rebuilt snapshot.
