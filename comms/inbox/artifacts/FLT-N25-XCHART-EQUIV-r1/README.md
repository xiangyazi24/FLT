# Actual N25 X/W chart algebra equivalence

## Deliverable

`N25F_XChartWChartEquiv.lean` is the production candidate for
`FLT/Assumptions/MazurProof/N25F_XChartWChartEquiv.lean` at FLT revision
`f0eb8381677bc483bddd93826871845030dd5c0e`.

The file proves, in namespace `MazurProof.N25F_XChartWChartEquiv`:

- Four coordinate-polynomial preservation identities for the binary linear
  transformation T(X,Y,Z,W)=(X+Y,X+Y+Z,Y+Z+W,X) and its explicit inverse
- Actual quotient algebra maps `wChartToXChart` and `xChartToWChart`
- All six coordinate identities from the proposed transformation
- The mutually inverse algebra equivalence
  `xChartAlgEquivWChart : XChartRing ≃ₐ[ZMod 2] W`
- `instance xChartRing_isDomain : IsDomain XChartRing`, transported from the
  existing W-chart domain instance supplied by the production import

The equivalence has **no extra hypotheses**. Its domain transport introduces
no new production assumption. No proxy curve ring, arbitrary embedding,
opaque geometric class, axiom, sorry, admit, or native_decide is used.
The characteristic-two identity is obtained by mapping 2=0 from ZMod 2, so
there is no circular nontriviality or CharP assumption on the X chart.

This automorphism-induced equivalence changes the coordinate functions. It
is not the coordinate-rigid inclusion of the two charts into the same
function field; the independent `N25F_XChartFractionMap` handles that map.

## Verification status

The full FLT import graph was not built in this environment. The production
file is a lead-compile candidate, not a claimed full-project build pass.

`XChartEquivCheck.lean` uses 51 verbatim source declarations with their actual
quotient-ring definitions, copied from 11 exact-pin source files. The source
snapshot manifests also include the 3 additional contextual files fetched by
the parallel map task. It checks the complete candidate proof body. The only
insertion in that body is an ordinary `[IsDomain W]` variable immediately
before the final domain instance, standing for the already-established W
instance supplied by the production import. All polynomial identities,
quotient lifts, coordinate formulas, inverse laws, and the algebra equivalence
are checked unconditionally.

`check-02.log` and `check-02.json`: exit 0, 15.26 seconds, 2,160,428 KiB peak
child RSS, single compiler thread, 60-second / 3 GiB cap. One unused simp
argument linter warning remains. `#print axioms` reports only Lean's standard
propext/Classical.choice/Quot.sound foundations; no sorryAx or custom axiom.
The generic polynomial identities need only propext and Quot.sound.

The actual tested check SHA-256 and production candidate hash are recorded
in `validation.json`. `source-inputs.json` records each exact source blob and
SHA-256; `copied-declarations.json` records declaration ranges and hashes.
`make_check.py` reconstructs the check from local `sources/` and the production
candidate. `run_check.py` records timing, return code, RSS, and file hash using
the already authorized bounded Lean wrapper.

## Required downstream acceptance

Compile the candidate with the full pinned FLT dependency graph; then check
`#print axioms` for `xChartAlgEquivWChart` and `xChartRing_isDomain` under those
real imports. No full build, cache-mass operation, remote write, or commit was
performed here.

## Remote handoff layout

The candidate lives in `comms/candidates/`; the remaining files in this packet
live in `comms/inbox/artifacts/FLT-N25-XCHART-EQUIV-r1/`. To recreate the local
harness, fetch the 14 source paths from the immutable URLs and revisions in
`source-inputs.json`, verify their hashes, and place them under `sources/`.
The source snapshots are existing repository files and are not duplicated in
this delivery. Adjust the local `root` paths in the two helper scripts as
needed. Their tested copies use the original bounded-check workspace.
`ActualXChartEquivCheck.lean` is the full-import validation request for the
lead; its full-import execution here is NOT RUN.
