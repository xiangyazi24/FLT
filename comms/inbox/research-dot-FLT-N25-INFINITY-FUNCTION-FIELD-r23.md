# r23 ACK and separability under the actual reciprocal action

TASK_ID: FLT-N25-INFINITY-FUNCTION-FIELD
REVISION: 23
TYPE: ACK_AND_RESULT
STATUS: FINITE-DEGREE-FOUR-ACCEPTED; RECIPROCAL-SEPARABILITY-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 366318f1af7d6a6722cc90fee468a2b0c5dcf9ea
DISPATCH_COMMIT: 5bb66f6452505bd1dfd528ddfd92650943b2f733
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the actual infinity normalization proof

## R23 acceptance verified

The explicit reciprocal rational-base action and its finite degree-four
result are integrated byte-equal from 7d09da85442482622c34848e9aac07f755a77593:
8684-job build and all ten public audits exactly standard-three. I resolved
the full source SHA and independently verified the accepted bytes. That
actual production-binding gate is closed.

## New exact production theorem

Candidate: comms/candidates/N25F_InfinitySeparable.lean
Namespace: MazurProof.N25F_InfinitySeparable

    infinityRationalBaseToField_isSeparable :
      letI : Algebra BaseField CurveField :=
        infinityRationalBaseToField.toRingHom.toAlgebra
      Algebra.IsSeparable BaseField CurveField

Here BaseField is the already constructed fraction field of the binary
polynomial ring and CurveField is the same FractionRing W. The map is the
actual reciprocal action from the accepted previous module. No new
separability premise is added to production.

First, affineRationalBaseToField_eq_canonicalLift proves the explicit old
map equals the source's canonical fraction lift. Thus the existing actual
canonicalWChart_fractionRing_isSeparable supplies separability for that
explicit old action. Then the proved rational-base inversion transports
separability to the reciprocal action. The same underlying fields carry
different explicit algebra actions; those actions are not silently
identified.

## Validation ledger

PASS: generic separability transport through a field automorphism,
generic-01:33.482s wrapper elapsed,2,395,048KiB peak child RSS, exactly
propext/Classical.choice/Quot.sound.

PASS: actual-curve common-field map equality and both separability
transports, actual-01:42.849s,2,487,904KiB peak child RSS, all three public
audits exactly standard-three, no sorryAx or warnings in the final check.
The source-specific fixture has the accepted W structural facts and the
already-existing canonical-action separability explicit. Its conclusion
uses infinityRationalBaseToField.toRingHom.toAlgebra; its premise uses
FractionRing.liftAlgebra. Default #check output hides those algebra
instances, so the visually repeated IsSeparable names in the log are not
the same action. The exact source and validation metadata make them explicit.
The production source instead invokes the existing named canonical theorem.

NOT RUN locally: the complete new FLT module with its parameter-free actual
canonical theorem binding and aggregate audit. ActualInfinitySeparableCheck.lean
lists all three public declarations for the lead. The reused actual-field
fixture was emitted successfully without changing its source; source and
olean hashes, emission receipt, generator and logs are attached.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation, one CPU/thread,3072MiB Lean cap,60s compiler limit, synthesis
budget200000. Wrapper times may include lock waiting. No broad build or
accepted-source rewrite was performed here.

## Next owned theorem boundary

With finite degree four and this separability proof, the next construction
is the actual finite integral closure over the reciprocal polynomial base.
It must retain the proved coefficient map and be compared with the three
actual boundary local rings. Their complete prime classification and the
relative-norm/valuation sum for arbitrary functions remain unproved.
The accepted base-polynomial degree-zero theorem remains a subcase only.

The last fresh Mazur root audit remains no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion and the
N49 raw-obstruction exclusion. N25 and the general projective product
formula remain open.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-FUNCTION-FIELD-r23-manifest.json
