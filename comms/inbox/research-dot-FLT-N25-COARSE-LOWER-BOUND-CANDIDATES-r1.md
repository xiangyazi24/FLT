# N25 boundary costs through coarse lower-bound candidates

TASK_ID: FLT-N25-COARSE-LOWER-BOUND-CANDIDATES
REVISION: 1
TYPE: RESULT
STATUS: CHECKED-LOCAL-COMPONENTS; ACTUAL-GEOMETRY-CANDIDATES-UNCOMPILED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 20f43b99f3a906637e369439c0eab2e78ed1d1b0
SUPERSEDES: none
SCOPE: Resume delivery of the original FLT-N25-BOUNDARY-CONDITION-COST@1 payload and separately deliver its four completed local continuations, without production integration.
ACCEPTANCE: Lead checks manifest bytes, stages complete named imports and all production axiom audits, then returns an exact-result-SHA acknowledgement; this envelope does not claim those checks or acceptance.

## 1. Original canceled boundary package, preserved

All 18 entries of the earlier FLT-N25-BOUNDARY-CONDITION-COST r1 payload are
included unchanged at their original candidate/inbox/artifact paths. Its
source pin is 51bbb4f191ad0d3753b87123635c100a638ae580; its prior-output producer is
20f43b99f3a906637e369439c0eab2e78ed1d1b0. Its eight bounded-family audits passed,
including the genuine binary-DVR cancellation producer. The full named
production imports and seven actual-curve declarations were NOT COMPILED.
This delivery resumes publication only; no successful earlier commit is
presumed and no old evidence is relabeled as a new compiler run.

## 2. Later results, kept separate

1. Exact affine ideal and total boundary cost: three generic Dedekind
   declarations plus one sequential three-boundary family theorem were checked.
   N25F_EffectiveAffineIdeal and N25F_TotalBoundaryCost preserve their source
   bytes; N25F_ShiftedAffineIdeal.UNCOMPILED is the source-only actual adapter.
2. Exact-count weighted reindexing: both new modules were checked at their
   intended names in a pinned overlay, with three standard-only axiom audits.
   The reused factor-degree dependency is pinned separately. Quotient
   specializations explicitly require finite ideal quotient dimension.
3. Kernel-to-section injection: five generic audits passed. The actual
   identity-on-functions injection and combined dimension inequality are
   N25F_KernelSectionInjection.UNCOMPILED. Generic membership and degree premises
   are not claimed discharged by those five audits.
4. Coarse lower-bound assembly: DegreeReindex has two checked generic audits.
   N25F_CoarseLowerBound.UNCOMPILED writes the actual prime-index alignment,
   signed affine degree calculation, three deficits and final candidate

       deg D <= dim_F2 L(D) + 4 * wPolynomialBasisPoleBound25Two.

   It introduces no new geometric hypothesis, but the complete actual proof
   chain is UNCOMPILED. Its production theorem is not a kernel-checked result.

Together these are 22 historically audited declarations, not 22 independently
checked actual-curve theorems. All final printed axiom sets are standard-only;
the fresh delivery audit verifies receipt/source hashes and log contents.
Full checked scopes and exact declaration names are in CHECK_AUDIT.json.

## 3. Source pins, logs, and reproduction

SOURCE_PROVENANCE.json separates the accepted source pin, prior published
candidate producers at the output base, and new local candidate producers.
Every payload file has UTF-8 byte count, SHA-256 and Git blob SHA in the bundle
manifest. The original manifest is retained unchanged and supplemented by this
complete bundle manifest. The original boundary family input is reused once;
no historical source tree or compiled object cache is copied.

Final receipts and axiom logs are included, with failed attempts under separate
failed paths. Historical per-stage reports keep their old publication/frontier
wording as historical records; this envelope is the current delivery status.
Runners and generators preserve their original local paths. To reproduce,
materialize candidates at the declared module names in a validation overlay,
restore explicit referenced inputs by their manifest hashes, and use the pinned
toolchain. Removing .UNCOMPILED in an overlay does not itself validate anything.

Lean 4.31.0-rc2, compiler 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Historical bounded runs used
one shared compiler slot, one CPU/thread, 3072 MiB and 60 active seconds. Logged
elapsed times may include slot wait; RSS is the runner child high-water mark.

## 4. Remaining verification and acknowledgement

PASS: historical bounded checks and current source/hash/log audit.
FAIL: preserved exploratory attempts only, never counted as success.
NOT RUN: fresh Lean rerun, complete actual-geometry import chain, production
theorem axiom closure, full FLT build, root axiom elimination and lead acceptance.
No independent review artifact is claimed; DELIVERY_SOURCE_AUDIT.md is clearly
a preparation audit rather than an independent or kernel review.

High-degree effectiveness, Picard finiteness and the sharp RR endpoint remain
unestablished. This additive candidate delivery does not edit production
sources. Integration remains with the lead. A subsequent envelope must carry
the full verified result commit SHA; this commit cannot claim its own hash.

Manifest: comms/inbox/research-dot-FLT-N25-COARSE-LOWER-BOUND-CANDIDATES-r1-manifest.json
