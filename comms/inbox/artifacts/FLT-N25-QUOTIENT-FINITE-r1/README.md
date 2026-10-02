# N25 actual W-chart quotient finiteness

## Result and exact target

Source candidate:
`comms/candidates/N25F_WChartQuotientFinite.lean`

Proposed lead placement:
`FLT/Assumptions/MazurProof/N25F_WChartQuotientFinite.lean`

Final FQN:
`MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finite`

```lean
theorem wChart_quotient_finite (a : W) (ha : a ≠ 0) :
    Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W))
```

Here W is the **existing actual W-chart ring**, `MazurProof.N25F_NonBoundaryPrincipalDivisor.W`. No ring, finite-type structure, or finite-dimensionality hypothesis is substituted or added.

The r6 ACK proposed a new namespace provisionally. The final candidate instead extends the existing principal-divisor namespace so that the existing W is used directly, without introducing an alias solely for packaging. There is no pre-existing caller whose name is changed.

## Proof

The six-line proof uses current pinned Mathlib:
1. Finite-type algebra over a field is finite-dimensional iff its Krull dimension is at most zero
2. For W/(a), dimension at most zero iff every minimal prime above (a) is maximal
3. a ≠ 0 implies (a) ≠ bottom
4. Every prime above (a) is therefore nonzero
5. The already established Dedekind structure of W makes every nonzero prime maximal

The unit case is included: W/(a) may be the zero ring. No nonunit or proper-ideal premise is introduced.

The existing finite-type instance is supplied by W's actual presentation as a quotient of a finite-variable polynomial algebra over ZMod 2; source provenance is in SOURCE_API_EVIDENCE.md.

## Compiler feedback: precisely what passed

A new bounded local check compiled the generic version and the generic nonzero principal-ideal corollary:
- Lean 4.31.0-rc2, commit 5e44d5f905127c78a2da7a015fe7a47840c95eb1
- Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05
- exact checked GenericFiniteQuotient.lean SHA-256: 0d2f30725331edc3649feb35597e567bd6e944e1cdbb6398798eefa965f82aca
- exit 0, 2.779 seconds, generated .olean
- both emitted axiom sets: [propext, Classical.choice, Quot.sound]
- one CPU, one Lean thread, 3,072 MiB Lean memory cap, 60-second timeout
- observed peak RSS for the check: 2,615,672 KiB
- selective official cache acquisition covered 2,004 required Mathlib modules; no full project build

The checked test file is copied **byte for byte** in this artifact folder. GenericFiniteQuotient.log is the actual emitted output; LOCAL_MICROCOMPILE.json records commands, pins, hashes and bounds. The .olean exists in the local verification environment; no precompiled binary is part of the source handoff.

**The actual FLT W specialization has not been compiled locally.** Its body instantiates the same checked argument, but import resolution and concrete-instance synthesis still need the lead's check. A generic kernel pass is not relabeled as a project-specialized or full-endpoint pass.

## Lead handoff

- Source pin: 22f88d43187caf0e57affcc6ded92cdf9b49714a
- Ownership/GO: [lead r6](https://github.com/xiangyazi24/FLT/blob/fd37948be1f5ac54edf68841b76a662c948d9c61/comms/outbox/lead-FLT-N13-ENDPOINT-go-r6.md)
- Candidate is a new file only; no existing theorem or accepted module changed
- LEAD_VALIDATION.lean provides the exact statement check and `#print axioms` request
- Please compile the specialization at the accepted source pin, emit its actual dependencies, and return the integration receipt

No alternate in-place patch is delivered: this avoids duplicate declaration placement. No new axiom, sorry, admit, native_decide or conditional interface is added.

## Intended caller and scope

The next intended consumer is the actual weighted affine principal-divisor degree/quotient-finrank theorem, which may install:

```lean
letI : Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) :=
  wChart_quotient_finite a ha
```

This is a proved instance, not an extra premise of the eventual degree theorem.

This result is only the finite-quotient prerequisite. It does not prove the weighted degree identity, genuine boundary valuations, the projective product formula, Picard/Riemann–Roch/rational arithmetic, or `no_explicit_order25_obstruction`. The accepted Mazur root still has three custom axioms. N13 acceptance is unchanged and no N13 integration is repeated.

