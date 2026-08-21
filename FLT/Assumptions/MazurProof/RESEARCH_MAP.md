# Mazur torsion proof: claim-level research map

Last verified: 2026-08-21 on `uisai2`.

This is the human projection of `research-map/{sources,claims,edges}.jsonl`.
Its scope is the dependency closure of `MazurProof.mazur_torsion_bound` and the
active routes toward its four remaining assumptions.  Historical experiments
outside that closure are inventoried only when they affect a live route,
supersede an old route, or account for remaining source placeholders.

## Exact target and verified backbone

The target `[MZ-GOAL]` is

```lean
∀ E : WeierstrassCurve ℚ, [E.IsElliptic] →
  (AddCommGroup.torsion (E⁄ℚ).Point).ncard ≤ 16
```

The fresh source build completed all 8775 jobs.  The endpoint audit
`[MZ-AUDIT-FOUR-CUT]` reports exactly four custom axioms and no reachable
`sorryAx`:

| Claim | Exact remaining assertion | Lean declaration |
|---|---|---|
| `[MZ-N13]` | Every rational point on the optimized `X₁(13)` sextic has `X = 0` or `X = -1` | `C13Sextic_affine_x_is_cuspidal` |
| `[MZ-N25]` | The explicit primitive order-25 obstruction has no rational solution | `no_explicit_order25_obstruction` |
| `[MZ-N49]` | The primitive order-49 Tate obstruction has no rational solution | `no_raw_order49_tate_obstruction` |
| `[MZ-TAIL23]` | No prime order `p ≥ 23` occurs over `ℚ` | `no_prime_order_ge_23` |

The downstream torsion-structure argument `[MZ-STRUCTURE-BACKBONE]` is proved.
The exclusions for composite orders `14,15,16,18,20,21,24,27,35` and prime
orders `11,17,19` are proved.  Orders `25` and `49` are wired, but their public
theorems still consume `[MZ-N25]` and `[MZ-N49]` respectively.

## Shortest candidate chains to the target

```text
[MZ-N13-SPECIALIZE]
  → [MZ-N13]
  → [MZ-CYCLIC-ASSEMBLY]
  → [MZ-STRUCTURE-BACKBONE]
  → [MZ-GOAL]

[MZ-N25-KOSZUL-CURVE]
  → [MZ-N25-CECH-COMPARE]
  → [MZ-N25-ADJUNCTION-DESCENT]
  → [MZ-N25-AFFINE-CANONICAL]
  → [MZ-N25-CHART-CANONICAL]
  → [MZ-N25-OVERLAP-LOCALIZATION]
  → [MZ-N25-PICARD-RR]
  → [MZ-N25-ABEL-JACOBI]
  → [MZ-N25]
  → [MZ-CYCLIC-ASSEMBLY]
  → [MZ-GOAL]

[MZ-N49-COMPOSE] + certified Newton faces
  → [MZ-N49-NEWTON]
  → [MZ-N49]
  → [MZ-CYCLIC-ASSEMBLY]
  → [MZ-GOAL]

[MZ-TAIL23]
  → [MZ-CYCLIC-ASSEMBLY]
  → [MZ-GOAL]
```

The N49 chain is an attack family, not yet a proved implication: the
composition identity only reformulates the obstruction, and the three
remaining Newton faces still require independent certificates.

## Ready frontier

1. **`[MZ-N25-PICARD-RR]`.** `[MZ-N25-CECH-COMPARE]` is proved: the pulled-back
   ambient hyperplane twist and the effective curve Čech twist are globally
   isomorphic.  `[MZ-N25-ADJUNCTION-DESCENT]` is also proved: the line glued by
   the actual ambient-canonical/inverse-conormal transition is globally that
   twist.  `[MZ-N25-AFFINE-CANONICAL]` now constructs the actual Kähler
   differential module on each ordinary chart and proves it is free of rank
   one via the unimodular Jacobian cross product.
   `[MZ-N25-CHART-CANONICAL]` transports these modules and their residue
   coordinates to the actual degree-zero homogeneous projective chart rings.
   `[MZ-N25-OVERLAP-LOCALIZATION]` localizes both actual chart coordinates to
   every ordered overlap and packages their change of basis as an explicit
   unit.  The remaining seam is to identify that unit with the already
   verified exponent `-1` transition, yielding `ω_C ≅ O_C(1)`.
2. **`[MZ-N13-SPECIALIZE]`.** The curve model, rational Abel map, special point
   classifier, cardinality 19, and normalized Mumford comparison are present.
   The next sound object is a genuine specialization group homomorphism, not
   the old arbitrary-spread-line classifier.
3. **`[MZ-N49-COMPOSE]`.** The exact identity is stated with the required
   nonvanishing hypotheses and has one literal proof placeholder.  Closing it
   provides a checked computational interface, though not the final exclusion.
4. **`[MZ-TAIL23]`.** No local Lean package in the current tree discharges the
   uniform tail.  The required modular-curve, Hecke, winding-quotient, and
   formal-immersion infrastructure remains a separate long-range build.

## Minimal unresolved cuts

At the endpoint level the unique visible cut is the four-element set

```text
{ [MZ-N13], [MZ-N25], [MZ-N49], [MZ-TAIL23] }.
```

All four are independently consumed by `[MZ-CYCLIC-ASSEMBLY]`; closing only
three does not make `[MZ-GOAL]` unconditional.

On the active N25 route, the current internal cut is

```text
{ [MZ-N25-PICARD-RR],
  good-reduction/rank-zero/pullback-norm bridges inside
    [MZ-N25-ABEL-JACOBI] }.
```

The source tree also contains 12 literal `sorry` placeholders and three
legacy-route axioms not reachable from the endpoint.  They are cleanup debt,
not additional members of the endpoint cut.

## Attack families

| Family | Status | Exact scope |
|---|---|---|
| N13 specialization homomorphism | active | Construct characteristic-two Picard group law, specialization, Abel compatibility, and prime-to-two injectivity |
| N13 arbitrary `class_eq_iff` | refuted | False for arbitrary spread lines because vertical divisors can change the special class |
| N25 ambient/Čech comparison | proved | The equalizer lift is globally invertible by the four-chart stalk cover |
| N25 adjunction transition descent | proved | The `4 + (-5) = -1` composite defines the same global equalizer as the effective hyperplane twist |
| N25 affine canonical differentials | proved | Each actual affine Kähler module is explicitly equivalent to its chart ring via the unimodular Jacobian residue |
| N25 homogeneous chart canonical differentials | proved | The Kähler equivalences and residue coordinates are transported to all four actual degree-zero projective chart rings |
| N25 overlap localization | proved | Both actual chart residue coordinates are localized to every ordered overlap and their rank-one transition is packaged as an explicit unit |
| N25 Picard/Riemann–Roch route | active, downstream | Turn finite-field divisor counts and Koszul geometry into actual Picard fibres and rational-point classification |
| N49 composition identity | active, narrow | Rewrites `preΨ'₄₉(0)` through the order-seven data; does not itself exclude solutions |
| N49 parity/Newton analysis | conditional | Six charts excluded; three Newton faces and their coefficient certificates remain |
| Uniform prime tail | open | Formal immersion for every prime `p ≥ 23`; current Mathlib/FLT infrastructure is insufficient |

## Counterexample bank and supersession table

| Claim or route | Verdict | Replacement or surviving scope |
|---|---|---|
| Arbitrary spread-line `class_eq_iff` | `[MZ-N13-CLASS-EQ]` refuted | Use a genuine Néron/Picard specialization homomorphism or a pointwise construction with proved additivity |
| `Classical.choose` classifier on special classes | scoped no-go | Cardinality alone cannot force agreement with geometric reduction on curve points |
| N49 composition as a complete proof | scoped no-go | It is a structural identity; global arithmetic or complete local Newton analysis is still required |
| ChatGPT Q5754/Q5757 snippets | support only | They contain uncompiled normalization sketches and are not proof evidence |
| July 11 `ROADMAP.md` status | `[MZ-OLD-ROADMAP]` superseded | This map plus the machine ledger and fresh audit are authoritative |

## Lean projection

Dependency order for new work:

1. Prove that `coordinateOverlapResidueUnit` is the exponent `-1`
   coordinate-ratio unit represented by `coordinateAdjunctionOverlapIso`.
2. Compose that local identification with
   `adjunctionTransitionLineIsoCurvePullback` to prove `ω_C ≅ O_C(1)`.
3. Connect that canonical twist to the explicit hyperplane section and the
   class-indexed middle-degree Riemann--Roch fibres.
4. For N13, replace the false `class_eq_iff` route with a separately named
   specialization group homomorphism and prove Abel–Jacobi compatibility before
   wiring `CyclicExclusion13`.
5. For N49, prove the composition identity, formalize every edge coefficient,
   and close all three Newton faces before wiring `CyclicExclusion49`.
6. Keep the uniform tail as an explicit obligation until its actual package is
   present and audited; do not hide it behind a renamed axiom.

After every endpoint change, rebuild
`FLT.Assumptions.MazurProof.MazurEndpointAudit` from source and compare the
printed axiom list with `[MZ-AUDIT-FOUR-CUT]`.

## Next questions

1. **`RM-N25-03` for `[MZ-N25-PICARD-RR]`:** Calculate the explicit unit
   `coordinateOverlapResidueUnit` obtained by comparing the two localized
   actual residue coordinates.  Acceptance: the induced overlap automorphism
   is proved equal to
   `coordinateAdjunctionOverlapIso` (equivalently exponent `-1`), so the four
   actual Kähler modules descend to `adjunctionTransitionLine` with no carried
   adjunction hypothesis.
2. **`RM-N25-04` for `[MZ-N25-PICARD-RR]`:** How should the explicit degree-six
   hyperplane section be connected to that canonical module without assuming
   divisor theory?  Acceptance: a checked section/divisor bridge supplies the
   canonical class consumed by the middle-degree Riemann--Roch fibres.
3. **`RM-N13-01` for `[MZ-N13-SPECIALIZE]`:** Which concrete finite model should
   carry the characteristic-two group law, and what checked map from the
   rational Picard quotient descends to it?  Acceptance: a compiled additive
   homomorphism with Abel compatibility and injective 19-primary restriction.
4. **`RM-N49-01` for `[MZ-N49-COMPOSE]`:** Prove the division-polynomial
   composition identity with its exact side conditions.  Acceptance: remove
   the sole `sorry` from `RationalPointsN49Composition.lean` and pass an axiom
   audit.
5. **`RM-N49-02` for `[MZ-N49-NEWTON]`:** Produce kernel-checked certificates for
   the boundary monomials and each of the three initial forms.  Acceptance: all
   nine primitive parity charts are excluded in Lean.
6. **`RM-TAIL-01` for `[MZ-TAIL23]`:** State the weakest uniform package whose
   fields match the formal-immersion proof without claiming unavailable Hecke
   infrastructure.  Acceptance: a conditional theorem with every deep premise
   explicit and no scope extension from fixed primes to a uniform prime.
