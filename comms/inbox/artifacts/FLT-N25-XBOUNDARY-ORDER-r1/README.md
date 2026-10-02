# Actual X-boundary order on the fixed W function field

`N25F_XBoundaryOrder.lean` supplies five public declarations in
`MazurProof.N25F_XBoundaryOrder`:

1. `xLocalToFraction_isFractionRing`: the common field is a fraction field of
   the actual XLocalRing under the explicitly induced xLocalToFraction algebra
2. `xLocalFractionOrder`: the genuine local length order extended by Ring.ordFrac
3. `xBoundaryOrder`: its logarithm as an additive homomorphism on nonzero functions
4. `xLocalFractionOrder_xWGerm`: the actual germ W/X has order three in the common field
5. `xBoundaryOrder_qx`: the actual function X/W has signed boundary order -3

The scalar tower is proved from the exact coordinate-rigid local map; no
automorphism-induced competing field structure is used. The existing
xWGerm_ord_eq_three theorem provides the length-three input. No new premise,
axiom, sorry, admission, or product formula is added to production statements.
The global boundary coefficient triple, other two boundary valuations, and
projective degree-zero theorem remain separate work.

## Bounded checks and precise evidence boundary

The small generic log/inverse-order argument passed in 2.884 seconds. The
actual-source incremental harness passed in 18.391 seconds, exit 0, 2765412
KiB peak child RSS, one CPU/thread, 3072 MiB cap, 60-second timeout, shared
flock gate. Lean 4.31.0-rc2; Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05.
All five public declarations print only propext, Classical.choice, Quot.sound.
Two unused fixture-section-variable warnings remain.

The harness imports the exact emitted XChartFractionEquivCheck module,
whose .olean emission and import smoke are documented in EMISSION_RECEIPT.json.
It then reproduces 13 additional verbatim accepted-source declarations for
the actual point prime, localization and germ, and includes the unchanged
DVR and local-embedding proof bodies before the complete new candidate.

The harness explicitly parameterizes the accepted W Dedekind instance.
It also supplies the already accepted exact theorem
`Ring.ord XLocalRing xWGerm = 3` as an ordinary input to the last two checked
theorems, rather than rebuilding the original Artin-quotient proof closure.
The provenance and full original theorem body are in accepted-order-input.json.
The first three new declarations do not depend on this order-three input.
The production import uses the existing source theorem and adds no premise.

Full FLT import checking is NOT RUN. ActualXBoundaryOrderCheck.lean is the
lead acceptance request. Earlier failed diagnostics are retained: a notation
scope fix, an elaboration heartbeat timeout resolved by a small explicit
generic lemma, and its final reflexivity step. No bound was raised; the
successful source and raw output are identified in validation.json.

## Reproduction

Set LEAN_PATH to the directory holding the exact emitted
XChartFractionEquivCheck.olean; its verified source is in dot commit
ebadf93d13b02ec5fbffcac0036bb9a02cbaa591 under
`comms/inbox/artifacts/FLT-N25-XFIELD-EQUIV-r1/`. The source-only repository
packet includes the emission log/receipt but not the binary .olean. Rebuild
it with the exact bounded command in EMISSION_RECEIPT.json when needed.

`make_check.py` uses that module, the exact XLocal source, the unchanged
DVR/local-embedding predecessors from ac7bb62b24aa0065b7e7d63fd726abdcae346ee7,
and the new candidate. Adjust local paths if necessary; verify the source
manifest first. It inserts only the disclosed structural/order inputs and
the explicit application of the order input in the last proof. Prior files
are unchanged. The shared gate does not change the compiler's bounds.
