# N25 actual Y/Z map into the existing YZ local ring

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: SOURCE-CANDIDATE; GENERIC-ALGEBRA-CHECK-PASS; ACTUAL-LOCAL/FULL-IMPORTS-NOT-RUN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 1eab90d583a58211846c1b69e24e5ed73a59ce4d
FIXTURE_SOURCE_BASE: f0eb8381677bc483bddd93826871845030dd5c0e
LAST_DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; new overlap producer within the existing exclusive N25 lane

## Observed lead integration

The source branch now contains our XChartFractionMap byte-equal at
[1eab90d583a58211846c1b69e24e5ed73a59ce4d](https://github.com/xiangyazi24/FLT/commit/1eab90d583a58211846c1b69e24e5ed73a59ce4d).
I reread and matched its exact bytes (blob fff302ef924a9e8d97f7c57299da3bbfd34018c3).
Its commit receipt reports 8645 build jobs and eight standard-three axiom
audits. The formal next dispatch receipt is still pending; this observation
is not an invented r10 ACK. The compare against f0eb shows only that one
new file, so all Y/Z input definitions are unchanged. Later modules remain
pending their own lead acceptance.

## New genuine statement

`N25F_YZOverlapMap.lean` defines:

```lean
MazurProof.N25F_YZOverlapMap.zChartToYZLocal :
  ZChartRing →ₐ[ZMod 2] YZLocalRing
```

It uses the proved actual Z/Y unit to normalize the existing Y-chart point.
The exact zX, zY, zW formulas and unit status of the zY image are proved.
There is no new domain, field, nonvanishing, point, or product-formula premise
in the production code. This is a map into the actual existing local ring,
not an assumed overlap isomorphism or a substitute carrier.

Required unchanged candidates:
- Z/W equivalence at 6999499b1155d42c8ac17876012b3625d1a59b1e
- actual YZ Z/Y unit at ec7da3d29290b8c56a9cc80b8081694abb2674c2

## Actual verification boundary

PASS: source review and complete generic commutative-algebra feedback,
5.215 s, 2445992 KiB peak RSS, eight standard-three axiom audits, one CPU/thread,
3072 MiB and 60-second bounds. Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
The fixture uses an arbitrary commutative Y-chart algebra L with the explicit
unit condition for image(yZ), while preserving the actual chart/coordinate
definitions. It does not check the actual YZ point/unit specialization.

NOT RUN: actual YZLocalRing specialization/full imports and the supplied
ActualYZOverlapMapCheck.lean. The README and validation.json explicitly mark
this generic-feedback boundary. No custom axiom, sorry or admission is added
to production. Candidate SHA-256:
`de28ed3e7d886f5a4db2077891b319c74c5b6a456202ae6292b486858b4018df`.
Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-yz-overlap-map-manifest.json.

The next owned step is the actual overlap-localization comparison, needed
before transferring a DVR/field order to YZLocalRing. Full projective product
formula and N25 exclusion remain open. Integration remains with the lead.
