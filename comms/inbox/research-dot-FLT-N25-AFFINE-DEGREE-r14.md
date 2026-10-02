# r14 ACK and actual YZ-local common-field embedding

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 14
TYPE: ACK_AND_RESULT
STATUS: YZ-DVR-ACCEPTANCE-VERIFIED; COMMON-FIELD-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 11c72e9feb3d47fb022469a40198ec85fdec3097
DISPATCH_COMMIT: c429fb036a24ff9059775c742fb745abdcd36951
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; next bounded result in unchanged N25 scope

## Acceptance synchronized

The actual YZ DVR candidate from 880d8c6ff5763319ab9afd50955b8fbc928c9a92
is accepted by r14: 8658-job build, all three public declarations have only
propext/Classical.choice/Quot.sound. The full source SHA was resolved and
the integrated file independently fetched and verified byte-equal.
The actual YZ-local DVR gate is now closed, separately from the remaining
N25/global product-formula obligations.

## New actual result

Candidate: comms/candidates/N25F_YZLocalFractionEmbedding.lean
The namespace is MazurProof.N25F_YZLocalFractionEmbedding.

    yzLocalToFraction : YZLocalRing →ₐ[ZMod 2] FractionRing W

The candidate proves its injectivity, the compatible IsFractionRing
structure, its unique coordinate-rigid Y-chart restriction, qy≠0, and
images X/Y↦qx/qy, Z/Y↦qz/qy, W/Y↦1/qy. It also provides the corresponding
identities for the existing named germs and the intervening away-open maps.
There are no new production hypotheses. The map uses the actual source
point, the proved affine overlap, and the accepted Z-chart field map.
It does not need a domain assumption on the full Y chart. Its existence
proof explicitly constructs the canonical localization extension;
Classical.choose is constrained by the proved coordinate restriction and
uniqueness theorem.

## Validation

PASS: pinned generic extension, 4.36s; actual away-open slice, 11.13s;
actual curve point-family slice, 17.53s (2,509,512KiB peak child RSS).
The final point-family check has nine audits, all standard-three/no sorryAx.
It explicitly assumes the accepted W structures and a source-type point f
with f(yZ)=1. The weaker away-open check's zY≠0 hypothesis is proved from
that point and overlap in the final point-family check.

NOT RUN locally: parameter-free production file with full FLT imports and
the named yzPointEval/germ bindings. Supplied ActualYZLocalFractionEmbeddingCheck.lean
audits all 19 public declarations for the lead. Detailed exact scopes,
source hashes, logs, generation script and receipts are attached in
FLT-N25-YZ-LOCAL-FRACTION-r1/RESULT.md and MANIFEST.json.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every invocation used one
shared gate, one CPU/thread,3072MiB Lean cap,60s compiler limit. The r10
synthesis budget200000 is present. No full project build here.

Next owned proof: actual signed YZ boundary orders of qy and qz, using
this common-field identification, the accepted DVR, existing W/Y order1
and Z/Y unit. In parallel the X-local equations are being used to derive
orders1 and2 for Y/X and Z/X; that is a separate unreleased candidate.
No global product formula is assumed.

The last fresh Mazur root closure still has no sorryAx and exactly three
custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. These individual module
results do not claim N25 or endpoint closure.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r14-manifest.json
