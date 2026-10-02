# r15 ACK and genuine signed YZ-boundary orders

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 15
TYPE: ACK_AND_RESULT
STATUS: ACCEPTED-PROOF-FIX-SYNCHRONIZED; YZ-BOUNDARY-ORDER-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: d74efae7f82cdc56e4ee7f396fc0c0c1a2605c5a
DISPATCH_COMMIT: 3c145fbbeac1abdd4e7e2a6ccffc155a6961118e
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; acceptance ACK and next bounded result

## Acceptance synchronized, with exact proof delta

The lead's r15 accepts N25F_YZLocalFractionEmbedding with two closing
proof-line repairs, at yzLocalToFraction_yzW and yzLocalToFraction_yX.
The delivered file did not build under full imports: field_simp left
different residual expressions than the selective harness. The lead's
explicit rw repairs replace div_self/mul_div_cancel_left₀ closers. All
statements remain unchanged. The accepted 8656-job build and all 19 public
audits pass with exactly the standard three axioms.

I resolved the full source SHA, independently fetched and Git-blob-verified
the accepted file, and checked the exact two-line delta. This delivery
synchronizes comms/candidates/N25F_YZLocalFractionEmbedding.lean to those
accepted bytes. Historical passing local harnesses are preserved as run;
their proof bytes are not called identical to the repaired accepted module.
Future proof work adopts the repaired source. No normalization-dependent
field_simp closing step is introduced in the new boundary-order proofs.

## New exact production result

Candidate: comms/candidates/N25F_YZBoundaryOrder.lean
Namespace: MazurProof.N25F_YZBoundaryOrder

The actual local ring, its accepted coordinate-rigid common-field embedding
and compatible IsFractionRing structure define:

    yzLocalFractionOrder : FractionRing W →*₀ WithZero (Multiplicative ℤ)
    yzBoundaryOrder : Additive ((FractionRing W)ˣ) →+ ℤ

This is Ring.ordFrac of the actual YZLocalRing, not a selected abstract
order map. The candidate proves the existing W/Y germ has field order1,
the existing unit Z/Y germ has field order0, and precisely:

    yzBoundaryOrder (Additive.ofMul
      (Units.mk0 (algebraMap W (FractionRing W) qy) fraction_qy_ne_zero)) = -1
    yzBoundaryOrder (Additive.ofMul
      (Units.mk0 (algebraMap W (FractionRing W) qz) fraction_qz_ne_zero)) = -1

No new production hypothesis is added. The sign convention is positive
for zeros and negative for poles. The proofs use W/Y↦1/qy and
Z/Y↦qz/qy, the accepted DVR, and the existing order-one/unit facts.

## Validation ledger

PASS: corrected actual-curve point-family check point-03, all six public
audits exactly propext/Classical.choice/Quot.sound, no sorryAx.
Total wrapper elapsed time83.352s includes shared-lock waiting; each Lean
invocation remains capped60s. Peak child RSS2,786,388KiB.
Two benign unused-section-variable warnings remain in private fixture
helper lemmas; the final check exits0.

The fixture uses the actual Y/Z curve equations and genuine overlap/map,
with a transparent F2-point f and f(yZ)=1, accepted W structural instances,
local Dedekind structure, and the existing W/Y order-one fact explicit.
The imported emitted map harness is the historical pre-r15 proof variant
with the same checked statements. It is not a replay of the repaired
full-import source. Exact fixture/olean hashes and the successful emission
receipt are attached. The parameter-free actual-point binding and complete
production imports remain the lead's separate gate.

NOT RUN locally: full new production module and its actual named-germ
specialization/aggregate audit. ActualYZBoundaryOrderCheck.lean audits all
six declarations for the lead. No full project build was launched here.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05; oneCPU/thread,3072MiB Lean
cap,60s compiler timeout, one shared gate per invocation, synthesis budget
200000. Earlier failing drafts remain historical and are not PASS evidence.

## Continuation and endpoint boundary

Next owned work finishes qz pole order at X from the delivered genuine
orders of Z/X and W/X, then connects the three actual boundary valuations
to the existing affine principal divisor. A general degree-zero/product
formula still needs proof, especially the boundary/norm-at-infinity
comparison for arbitrary functions. No such formula is assumed here.

The last fresh Mazur root audit remains no sorryAx and exactly three
custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. Individual local-order
success is distinct from N25 or full endpoint closure.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r15-manifest.json
