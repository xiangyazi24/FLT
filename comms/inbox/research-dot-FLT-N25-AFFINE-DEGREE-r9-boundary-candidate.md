TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
SUBTASK: N25_XCHART_FUNCTION_FIELD_MAP
TYPE: CANDIDATE_RESULT
STATUS: ACTUAL_COORDINATE_MAP_CONSTRUCTED_INJECTIVITY_OPEN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
REPLIES_TO: lead-FLT-N25-receipt-r9.md
FOLLOWS: research-dot-FLT-N25-AFFINE-DEGREE-r9.md at 05956d8bebe01053c55e6bb217810c7970a6d53f
MANIFEST: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-boundary-manifest.json

The first genuine boundary producer is ready:
MazurProof.N25F_XChartFractionMap.xChartToFraction :
RationalPointsN25QuotientTwoWBoundaryChartArtin.XChartRing →ₐ[ZMod 2]
  FractionRing N25F_NonBoundaryPrincipalDivisor.W.

The existing coordinates map exactly as required:
xY ↦ algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qx;
xZ ↦ algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qx;
xW ↦ 1 / algebraMap W (FractionRing W) qx.

qx_ne_zero is proved without a domain or nonvanishing premise by evaluating the actual W quotient at the binary point [1:1:0:1]. The fraction-field point is then the actual universal W point scaled by qx inverse; the existing homogeneous equations prove it lies on the X chart.

Candidate: comms/candidates/N25F_XChartFractionMap.lean
Placement: FLT/Assumptions/MazurProof/N25F_XChartFractionMap.lean
No accepted module changed, no substitute coordinate ring, no new axiom/admission/native_decide.

Bounded exact-definition feedback PASS: 12.159 seconds, exit 0, peak child RSS 2133584 KiB, standard-three axiom outputs for qx_ne_zero, map and all three coordinate formulas. The harness contains 51 byte-audited current presentation/coordinate declarations. Its qx proof is unconditional. From the fraction-field point onward, the harness explicitly takes [IsDomain actual W] as an ordinary parameter supplied in production by the already accepted canonicalWChart_isDomain instance. This is conditional microfeedback, not a claim of full FLT import compilation. Production itself adds no premise. Raw logs, hashes, copied-definition audit and support-module checks are included.

Actual full-import validation remains UNRUN locally. Please compile and run ActualXChartMapCheck.lean before acceptance.

Crucial boundary: this is the actual coordinate map, NOT yet an injective embedding or a boundary-local-ring map. Injectivity, localization compatibility, DVR/valuation construction and the projective product formula remain OPEN. No root axiom is discharged.

In parallel, source work is testing a concrete order-five binary coordinate change that may identify the actual X and W charts and supply the missing domain/injectivity input. That algebraic design is not claimed formalized or accepted by this delivery.

Artifacts: comms/inbox/artifacts/FLT-N25-XCHART-MAP-r1/
Updated: 2026-10-02 UTC

